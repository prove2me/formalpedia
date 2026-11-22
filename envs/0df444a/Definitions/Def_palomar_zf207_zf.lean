-- Prove2me | Definitions.Def_palomar_zf207_zf
-- name    : palomar_zf207_zf
-- status  : Definition
-- author  : @LG
-- created : 2026-11-21T17:13:55.971368+00:00
-- url     : https://prove2.me/theorems/ebf3e064-b5cb-4744-9709-31638511f466
-- title:
--   ZF207: standalone first-order ZF syntax, natural deduction and axioms
-- statement:
--   This bundle fixes the standalone presentation of first-order ZF used by the ZF207 claim.
--
--   **Syntax.** `PalomarZF207.Formula` is the de Bruijn-indexed grammar with $\bot$, membership and equality atoms, $\land,\lor,\to$, and $\forall,\exists$; `lift`, `rename`, `shift`, `subst` implement variable renaming and substitution; `Bound p n` bounds the free indices; `Closed p := Bound p 0`; `eval E p s` is Tarski evaluation under assignment $s$ in the relation $E$; `Neg p := imp p bot`.
--
--   **Proof system.** `ND` is a natural-deduction calculus on sequent rows `Γ ⊢ a` with a branching row for disjunction elimination: context, Peirce's law, implication introduction/elimination, explosion, conjunction introduction/elimination, disjunction introduction, branch-pair and disjunction elimination, weakening, and universal/existential introduction/elimination with the de Bruijn shift discipline.
--
--   **Axioms.** `FixedAxiom` lists equality reflexivity, symmetry, transitivity and congruence, extensionality, empty set, pairing, union, power set, infinity (`fixedOmega`), and foundation. `Axiom` adds the full Separation and Replacement schemas with arbitrary finite parameter prefixes (`separationSchema`, `replacementSchema`).
--
--   **Provability and models.** `Provable p` is derivability from axioms; `Consistent := ¬ Provable bot`; `Model E` requires every axiom valid under every assignment, with nonemptiness of the domain required separately at each use.
-- source:
--   James Chang, 'Nonhalting and ZF-independence for a 207-state Turing machine' (2026), §1 (The result), §7 (Lean verification); standalone definitions https://github.com/jamesyc/BusyBeaver/blob/37861b991bb70dbaee7dbd91120ab533cba658e2/ZF207/ProofSources/Challenge.lean#L314-L462 (production module Palomar207ZFDefinition.lean)

/- Source: https://github.com/jamesyc/BusyBeaver/blob/37861b991bb70dbaee7dbd91120ab533cba658e2/ZF207/ProofSources/Challenge.lean#LL314-L462
   Standalone ZF presentation; production module Palomar207ZFDefinition.lean. ND binders carry forced types (autoImplicit=false). -/
namespace PalomarZF207
inductive Formula where
 | bot : Formula
 | mem : Nat → Nat → Formula
 | eq : Nat → Nat → Formula
 | and : Formula → Formula → Formula
 | or : Formula → Formula → Formula
 | imp : Formula → Formula → Formula
 | all : Formula → Formula
 | ex : Formula → Formula
 deriving DecidableEq, Repr

def lift (σ : Nat → Nat) : Nat → Nat
 | 0 => 0
 | n+1 => σ n + 1

def rename (σ : Nat → Nat) : Formula → Formula
 | .bot => .bot
 | .mem i j => .mem (σ i) (σ j)
 | .eq i j => .eq (σ i) (σ j)
 | .and a b => .and (rename σ a) (rename σ b)
 | .or a b => .or (rename σ a) (rename σ b)
 | .imp a b => .imp (rename σ a) (rename σ b)
 | .all a => .all (rename (lift σ) a)
 | .ex a => .ex (rename (lift σ) a)


def shift (a:Formula) := rename Nat.succ a
def substMap (t:Nat) : Nat→Nat | 0=>t | n+1=>n
def subst (t:Nat) (a:Formula) := rename (substMap t) a

def Bound : Formula → Nat → Prop
  | .bot, _ => True
  | .mem i j, n => i < n ∧ j < n
  | .eq i j, n => i < n ∧ j < n
  | .and p q, n => Bound p n ∧ Bound q n
  | .or p q, n => Bound p n ∧ Bound q n
  | .imp p q, n => Bound p n ∧ Bound q n
  | .all p, n => Bound p (n+1)
  | .ex p, n => Bound p (n+1)


universe u
/-- Interpretation of a de Bruijn assignment after pushing an eigenvariable. -/
def pushValue {α : Type u} (s : Nat → α) (x : α) : Nat → α
  | 0 => x
  | n + 1 => s n

def eval {α : Type u} (mem : α → α → Prop) : Formula → (Nat → α) → Prop
  | .bot, _ => False
  | .mem i j, s => mem (s i) (s j)
  | .eq i j, s => s i = s j
  | .and p q, s => eval mem p s ∧ eval mem q s
  | .or p q, s => eval mem p s ∨ eval mem q s
  | .imp p q, s => eval mem p s → eval mem q s
  | .all p, s => ∀ x, eval mem p (pushValue s x)
  | .ex p, s => ∃ x, eval mem p (pushValue s x)


abbrev Context := List Formula

def ContextSub (Γ Δ : Context) : Prop := ∀ a, a ∈ Γ → a ∈ Δ
inductive Row where
 | seq : Context → Formula → Row
 | branches : Context → Formula → Formula → Formula → Row
 deriving DecidableEq, Repr


def shiftContext (Γ:Context):=Γ.map shift

inductive ND : Row → Prop where
 | ctx {Γ : Context} {a : Formula} : a ∈ Γ → ND (.seq Γ a)
 | pc (Γ : Context) (a b : Formula) : ND (.seq Γ (.imp (.imp (.imp a b) a) a))
 | ii {Γ : Context} {a b : Formula} : ND (.seq (a :: Γ) b) → ND (.seq Γ (.imp a b))
 | ie {Γ : Context} {a b : Formula} : ND (.seq Γ (.imp a b)) → ND (.seq Γ a) → ND (.seq Γ b)
 | exp {Γ : Context} {a : Formula} : ND (.seq Γ .bot) → ND (.seq Γ a)
 | ci {Γ : Context} {a b : Formula} : ND (.seq Γ a) → ND (.seq Γ b) → ND (.seq Γ (.and a b))
 | ce1 {Γ : Context} {a b : Formula} : ND (.seq Γ (.and a b)) → ND (.seq Γ a)
 | ce2 {Γ : Context} {a b : Formula} : ND (.seq Γ (.and a b)) → ND (.seq Γ b)
 | di1 {Γ : Context} {a b : Formula} : ND (.seq Γ a) → ND (.seq Γ (.or a b))
 | di2 {Γ : Context} {a b : Formula} : ND (.seq Γ b) → ND (.seq Γ (.or a b))
 | branchPair {Γ : Context} {a b c : Formula} : ND (.seq (a :: Γ) c) → ND (.seq (b :: Γ) c) → ND (.branches Γ a b c)
 | de {Γ : Context} {a b c : Formula} : ND (.seq Γ (.or a b)) → ND (.branches Γ a b c) → ND (.seq Γ c)
 | wk {Γ Δ : Context} {a : Formula} : ContextSub Γ Δ → ND (.seq Γ a) → ND (.seq Δ a)
 | allI {Γ : Context} {a : Formula} : ND (.seq (shiftContext Γ) a) → ND (.seq Γ (.all a))
 | allE {Γ : Context} {a : Formula} (t : Nat) : ND (.seq Γ (.all a)) → ND (.seq Γ (subst t a))
 | exI {Γ : Context} {a : Formula} (t : Nat) : ND (.seq Γ (subst t a)) → ND (.seq Γ (.ex a))
 | exE {Γ : Context} {a c : Formula} : ND (.seq Γ (.ex a)) → ND (.seq (a :: shiftContext Γ) (shift c)) → ND (.seq Γ c)


def fixedRefl : Formula := (.all (.eq 0 0))

def fixedSym : Formula := (.all (.all (.imp (.eq 1 0) (.eq 0 1))))

def fixedTrans : Formula := (.all (.all (.all (.imp (.eq 2 1) (.imp (.eq 1 0) (.eq 2 0))))))

def fixedEqElem : Formula := (.all (.all (.all (.all (.imp (.eq 3 1) (.imp (.eq 2 0) (.imp (.mem 3 2) (.mem 1 0))))))))

def fixedExt : Formula := (.all (.all (.imp (.all (.imp (.mem 0 2) (.mem 0 1))) (.imp (.all (.imp (.mem 0 1) (.mem 0 2))) (.eq 1 0)))))

def fixedEmpty : Formula := (.ex (.all (.imp (.mem 0 1) (.bot))))

def fixedPair : Formula := (.all (.all (.ex (.all (.and (.imp (.mem 0 1) (.or (.eq 0 3) (.eq 0 2))) (.imp (.or (.eq 0 3) (.eq 0 2)) (.mem 0 1)))))))

def fixedUnion : Formula := (.all (.ex (.all (.and (.imp (.mem 0 1) (.ex (.and (.mem 0 3) (.mem 1 0)))) (.imp (.ex (.and (.mem 0 3) (.mem 1 0))) (.mem 0 1))))))

def fixedPower : Formula := (.all (.ex (.all (.and (.imp (.mem 0 1) (.all (.imp (.mem 0 1) (.mem 0 3)))) (.imp (.all (.imp (.mem 0 1) (.mem 0 3))) (.mem 0 1))))))

def fixedOmega : Formula := (.ex (.and (.and (.ex (.and (.all (.imp (.mem 0 1) (.bot))) (.mem 0 1))) (.all (.imp (.mem 0 1) (.ex (.and (.all (.and (.imp (.mem 0 1) (.or (.mem 0 2) (.eq 0 2))) (.imp (.or (.mem 0 2) (.eq 0 2)) (.mem 0 1)))) (.mem 0 2)))))) (.all (.imp (.and (.ex (.and (.all (.imp (.mem 0 1) (.bot))) (.mem 0 1))) (.all (.imp (.mem 0 1) (.ex (.and (.all (.and (.imp (.mem 0 1) (.or (.mem 0 2) (.eq 0 2))) (.imp (.or (.mem 0 2) (.eq 0 2)) (.mem 0 1)))) (.mem 0 2)))))) (.all (.imp (.mem 0 2) (.mem 0 1)))))))

def fixedFoundation : Formula := (.all (.imp (.ex (.mem 0 1)) (.ex (.and (.mem 0 1) (.all (.imp (.mem 0 1) (.imp (.mem 0 2) (.bot))))))))


def sourceIff (a b : Formula) := Formula.and (.imp a b) (.imp b a)
def separationFormula (body : Formula) := Formula.all (.ex (.all
 (sourceIff (.mem 0 1) (.and (.mem 0 2) body))))
def functionalityFormula (a b : Formula) := Formula.all (.all (.all
 (.imp a (.imp b (.eq 1 0)))))
def replacementFormula (a b c : Formula) := Formula.imp (functionalityFormula a b)
 (.all (.ex (.all (sourceIff (.mem 0 1) (.ex (.and (.mem 0 3) c))))))
def allPrefix : Nat → Formula → Formula
 | 0, a => a
 | n+1, a => .all (allPrefix n a)

def sepIndex (i : Nat) := if i=0 then 0 else i+2
def repAIndex (i : Nat) := if i=0 then 2 else if i=1 then 1 else i+1
def repBIndex (i : Nat) := if i=0 then 2 else if i=1 then 0 else i+1
def repCIndex (i : Nat) := if i=0 then 0 else if i=1 then 1 else i+2

def separationSchema (n : Nat) (phi : Formula) := allPrefix n (separationFormula (rename sepIndex phi))
def replacementSchema (n : Nat) (phi : Formula) := allPrefix n
 (replacementFormula (rename repAIndex phi) (rename repBIndex phi) (rename repCIndex phi))


/-- All fixed axioms, including logical equality, omega, and foundation. -/
def FixedAxiom (p:Formula):Prop:=
 p=fixedRefl ∨ p=fixedSym ∨ p=fixedTrans ∨ p=fixedEqElem ∨ p=fixedExt ∨
 p=fixedEmpty ∨ p=fixedPair ∨ p=fixedUnion ∨ p=fixedPower ∨ p=fixedOmega ∨ p=fixedFoundation
/-- Full standard schemas, with arbitrary finite parameter lists. -/
def Axiom (p:Formula):Prop:= FixedAxiom p ∨
 (∃ n body,Bound body (n+1) ∧ p=separationSchema n body) ∨
 (∃ n body,Bound body (n+2) ∧ p=replacementSchema n body)
def Provable (p:Formula):Prop:=∃Γ:Context,(∀q,q∈Γ→Axiom q) ∧ ND (.seq Γ p)
def Consistent:Prop:=¬Provable .bot
def Closed (p:Formula):Prop:=Bound p 0
def Neg (p:Formula):Formula:=.imp p .bot
/-- Nonemptiness is separately required at every quantified model use. -/
def Model {V:Type} (E:V→V→Prop):Prop:=∀p,Axiom p→∀s:Nat→V,eval E p s
end PalomarZF207


