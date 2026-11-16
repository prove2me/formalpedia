-- Prove2me | Definitions.Def_RandomCNFDeficiency_LowerBound_Supplement_ModFrege
-- name    : RandomCNFDeficiency_LowerBound_Supplement_ModFrege
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:57:14.813618+00:00
-- url     : https://prove2.me/theorems/fcd7ec20-0350-428f-8df7-a4727dc609bc
-- title:
--   Syntactic $\mathrm{AC}^0[p]$-Frege: formulas, rules, depth, size and refutations
-- statement:
--   Fix a prime $p$. **Formulas** are finite trees over $\bot,\top$, variables, negation $\neg$, binary $\wedge$ and $\vee$, and $\mathrm{MOD}_{p,a}(A_1,\dots,A_m)$ for $a\in\mathbb F_p$ and any finite list of arguments; $\mathrm{MOD}_{p,a}$ is true iff the number of true arguments is congruent to $a$ modulo $p$.
--
--   **Depth** follows the gate convention of Section 2.3: literals and constants have depth $0$, negation adds nothing, a modular gate adds one, and each maximal block of consecutive $\wedge$ (or of consecutive $\vee$) counts as one unbounded fan-in gate of depth one plus the maximal depth of its inputs. **Size** is the number of occurrences of constants, variables and connectives, summed over all lines of a proof. $M_i$ is the number of distinct rooted syntactic subformulas of the proof lines that have depth $i$ and output gate $\wedge$ or $\vee$.
--
--   A **Frege rule** is a scheme $F_1,\dots,F_r\vdash F$ of de Morgan formulas over metavariables; it is sound if every Boolean valuation of the metavariables satisfying all $F_i$ satisfies $F$. Instances substitute arbitrary formulas for metavariables. The **modular axioms** are all instances of
--
--   $$B\vee\neg U\vee V,\quad B\vee U\vee\neg V,\quad \neg B\vee\neg U\vee W,\quad \neg B\vee U\vee\neg W,$$
--
--   with $U=\mathrm{MOD}_{p,a}(\Gamma,B)$, $V=\mathrm{MOD}_{p,a}(\Gamma)$, $W=\mathrm{MOD}_{p,a-1}(\Gamma)$, together with $\mathrm{MOD}_{p,0}(\emptyset)$ and $\neg\mathrm{MOD}_{p,a}(\emptyset)$ for $a\ne0$. An input clause is written as $\bot$ (empty clause) or as a disjunction of exactly its literals. A **proof** from a CNF $F$ with rule set $R$ is a sequence of formulas each of which is an input clause, a modular axiom instance, or an instance of a rule of $R$ whose instantiated premises occur earlier; a **refutation** ends in $\bot$; it has depth at most $\ell$ when every line does.
--
--   This is the proof system of the size–degree tradeoffs in Appendix A.
--
--   **Formalization Note** Rooted binary syntax is kept for $\wedge,\vee$; input clauses and the three-literal modular clauses are accepted in any order and bracketing of their disjuncts. The rule set is a finite list of schemes; Boolean semantics of formulas is included for reference.
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Section 2.3, printed p. 8, PDF p. 10; Theorem A.3, printed p. 21, PDF p. 23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_Clause
set_option autoImplicit false

namespace RandomCNFDeficiency.LowerBound.Supplement

open RandomCNFDeficiency.LowerBound

/-- Formulas over `{⊥, ⊤, ¬, ∧, ∨, MOD_{p,a} : a ∈ F_p}` (§2.3), with variables in `V` and residues `a ∈ F_p = ZMod p`. `∧` and `∨`
are binary (rooted syntax is kept); `MOD_{p,a}` takes a finite list of arguments. -/
inductive MFormula (p : ℕ) (V : Type) where
  | bot : MFormula p V
  | top : MFormula p V
  | var (v : V) : MFormula p V
  | neg (A : MFormula p V) : MFormula p V
  | and (A B : MFormula p V) : MFormula p V
  | or (A B : MFormula p V) : MFormula p V
  | mod (a : ZMod p) (args : List (MFormula p V)) : MFormula p V

namespace MFormula

variable {p : ℕ} {V : Type}

/-- Inputs of the maximal `∧`-block rooted at a formula (the formula itself if it is not `∧`). -/
def andInputs : MFormula p V → List (MFormula p V)
  | and A B => andInputs A ++ andInputs B
  | A => [A]

/-- Inputs of the maximal `∨`-block rooted at a formula (the formula itself if it is not `∨`). -/
def orInputs : MFormula p V → List (MFormula p V)
  | or A B => orInputs A ++ orInputs B
  | A => [A]

/-- Auxiliary depth data `(depth A, ∧-member value, ∨-member value)`. The `∧`-member value of
`A` is the maximum depth of the inputs of the `∧`-block that `A` continues: if `A = A₁ ∧ A₂` it
is the maximum of the member values of `A₁, A₂`; otherwise it is `depth A`. Likewise for `∨`. -/
def depthData : MFormula p V → ℕ × ℕ × ℕ
  | bot => (0, 0, 0)
  | top => (0, 0, 0)
  | var _ => (0, 0, 0)
  | neg A => ((depthData A).1, (depthData A).1, (depthData A).1)
  | and A B =>
      let m := max (depthData A).2.1 (depthData B).2.1
      (1 + m, m, 1 + m)
  | or A B =>
      let m := max (depthData A).2.2 (depthData B).2.2
      (1 + m, 1 + m, m)
  | mod _ args =>
      let d := 1 + (args.attach.map fun ⟨x, _⟩ => (depthData x).1).foldr max 0
      (d, d, d)

/-- Depth in the gate convention (§2.3): literals and constants have depth 0, negation adds
nothing, each `MOD` gate adds one, and each maximal block of consecutive `∧` (or of consecutive
`∨`) counts as one unbounded fan-in gate of depth one plus the maximum depth of its inputs. -/
def depth (A : MFormula p V) : ℕ := (depthData A).1

/-- Number of symbol occurrences (constants, variables, connectives). -/
def size : MFormula p V → ℕ
  | bot => 1
  | top => 1
  | var _ => 1
  | neg A => 1 + size A
  | and A B => 1 + size A + size B
  | or A B => 1 + size A + size B
  | mod _ args => 1 + (args.attach.map fun ⟨x, _⟩ => size x).sum

/-- All rooted syntactic subformulas (with multiplicity, the formula itself first). -/
def subformulas : MFormula p V → List (MFormula p V)
  | bot => [bot]
  | top => [top]
  | var v => [var v]
  | neg A => neg A :: subformulas A
  | and A B => and A B :: (subformulas A ++ subformulas B)
  | or A B => or A B :: (subformulas A ++ subformulas B)
  | mod a args => mod a args :: (args.attach.map fun ⟨x, _⟩ => subformulas x).flatten

/-- The output gate is a conjunction or a disjunction. -/
def IsAndOr : MFormula p V → Prop
  | and _ _ => True
  | or _ _ => True
  | _ => False

/-- Boolean semantics: `MOD_{p,a}` is true iff the number of true inputs is `≡ a (mod p)`. -/
def eval (σ : V → Bool) : MFormula p V → Bool
  | bot => false
  | top => true
  | var v => σ v
  | neg A => !(eval σ A)
  | and A B => eval σ A && eval σ B
  | or A B => eval σ A || eval σ B
  | mod a args =>
      decide ((((args.attach.map fun ⟨x, _⟩ => eval σ x).count true : ℕ) : ZMod p) = a)

end MFormula

/-- `IsDisjOf φ l`: `φ` is a binary `∨`-tree whose leaves, left to right, are the list `l`. -/
inductive IsDisjOf {p : ℕ} {V : Type} : MFormula p V → List (MFormula p V) → Prop
  | leaf (φ : MFormula p V) : IsDisjOf φ [φ]
  | node (A B : MFormula p V) (l₁ l₂ : List (MFormula p V)) :
      IsDisjOf A l₁ → IsDisjOf B l₂ → IsDisjOf (MFormula.or A B) (l₁ ++ l₂)

/-- `φ` is a disjunction of exactly the formulas in `l`, in any order and any bracketing. -/
def IsClauseOf {p : ℕ} {V : Type} (φ : MFormula p V) (l : List (MFormula p V)) : Prop :=
  ∃ l' : List (MFormula p V), IsDisjOf φ l' ∧ l'.Perm l

/-- The literals of a signed clause: `x_i` for a positive occurrence, `¬x_i` for a negative one. -/
def clauseLiterals {p n : ℕ} (C : Clause n) : List (MFormula p (Fin n)) :=
  (List.finRange n).filterMap fun i =>
    (C i).map fun b => if b then MFormula.var i else MFormula.neg (MFormula.var i)

/-- `φ` is a formula writing the input clause `C`: `⊥` for the empty clause, otherwise a
disjunction of exactly its literals (any order and bracketing). -/
def IsInputClauseFormula {p n : ℕ} (C : Clause n) (φ : MFormula p (Fin n)) : Prop :=
  (clauseLiterals (p := p) C = [] ∧ φ = MFormula.bot) ∨
    (clauseLiterals (p := p) C ≠ [] ∧ IsClauseOf φ (clauseLiterals C))

/-- De Morgan formulas over metavariables `W` (the language of the Frege rule schemes). -/
inductive DMFormula (W : Type) where
  | bot : DMFormula W
  | top : DMFormula W
  | var (w : W) : DMFormula W
  | neg (A : DMFormula W) : DMFormula W
  | and (A B : DMFormula W) : DMFormula W
  | or (A B : DMFormula W) : DMFormula W

namespace DMFormula

variable {W : Type}

def eval (σ : W → Bool) : DMFormula W → Bool
  | bot => false
  | top => true
  | var w => σ w
  | neg A => !(eval σ A)
  | and A B => eval σ A && eval σ B
  | or A B => eval σ A || eval σ B

/-- Substitution of formulas for metavariables. -/
def subst {p : ℕ} {V : Type} (σ : W → MFormula p V) : DMFormula W → MFormula p V
  | bot => MFormula.bot
  | top => MFormula.top
  | var w => σ w
  | neg A => MFormula.neg (subst σ A)
  | and A B => MFormula.and (subst σ A) (subst σ B)
  | or A B => MFormula.or (subst σ A) (subst σ B)

end DMFormula

/-- A Frege rule scheme `F₁, …, F_r ⊢ F` in the de Morgan language over `m` metavariables. -/
structure FregeRule where
  m : ℕ
  premises : List (DMFormula (Fin m))
  conclusion : DMFormula (Fin m)

/-- Soundness: every Boolean valuation of the metavariables satisfying all premises satisfies the
conclusion. -/
def FregeRule.Sound (ρ : FregeRule) : Prop :=
  ∀ v : Fin ρ.m → Bool, (∀ G ∈ ρ.premises, G.eval v = true) → ρ.conclusion.eval v = true

/-- The modular counting axioms of §2.3, for all substitution instances: with
`U = MOD_{p,a}(Γ, B)`, `V = MOD_{p,a}(Γ)`, `W = MOD_{p,a-1}(Γ)` (residues mod `p`), the four clauses
`B ∨ ¬U ∨ V`, `B ∨ U ∨ ¬V`, `¬B ∨ ¬U ∨ W`, `¬B ∨ U ∨ ¬W` (each in any order and bracketing), and
`MOD_{p,0}(∅)` and `¬MOD_{p,a}(∅)` for `a ≠ 0`. -/
def IsModAxiom {p : ℕ} {V : Type} (φ : MFormula p V) : Prop :=
  (∃ (Γ : List (MFormula p V)) (B : MFormula p V) (a : ZMod p),
      let U := MFormula.mod a (Γ ++ [B])
      let Vf := MFormula.mod a Γ
      let Wf := MFormula.mod (a - 1) Γ
      IsClauseOf φ [B, MFormula.neg U, Vf] ∨
      IsClauseOf φ [B, U, MFormula.neg Vf] ∨
      IsClauseOf φ [MFormula.neg B, MFormula.neg U, Wf] ∨
      IsClauseOf φ [MFormula.neg B, U, MFormula.neg Wf]) ∨
  φ = MFormula.mod 0 [] ∨
  (∃ a : ZMod p, a ≠ 0 ∧ φ = MFormula.neg (MFormula.mod a []))

/-- One line of an AC⁰[p]-Frege proof of the CNF `F` with rules `R`, given the earlier lines:
an input clause, a modular axiom instance, or a substitution instance of a rule of `R` whose
instantiated premises all occur among the earlier lines. -/
inductive FregeStep {p n : ℕ} (R : List FregeRule) (F : CNF n)
    (earlier : List (MFormula p (Fin n))) : MFormula p (Fin n) → Prop
  | input (C : Clause n) (hC : C ∈ F) (φ : MFormula p (Fin n))
      (hφ : IsInputClauseFormula C φ) : FregeStep R F earlier φ
  | modAxiom (φ : MFormula p (Fin n)) (hφ : IsModAxiom φ) : FregeStep R F earlier φ
  | rule (ρ : FregeRule) (hρ : ρ ∈ R) (σ : Fin ρ.m → MFormula p (Fin n))
      (hprem : ∀ G ∈ ρ.premises, G.subst σ ∈ earlier) :
      FregeStep R F earlier (ρ.conclusion.subst σ)

/-- An AC⁰[p]-Frege proof from `F`: every line is justified by `FregeStep` from the lines
before it. -/
def IsFregeProof {p n : ℕ} (R : List FregeRule) (F : CNF n)
    (π : List (MFormula p (Fin n))) : Prop :=
  ∀ (j : ℕ) (φ : MFormula p (Fin n)), π[j]? = some φ → FregeStep R F (π.take j) φ

/-- An AC⁰[p]-Frege refutation of `F`: a proof whose last line is `⊥`. -/
def IsFregeRefutation {p n : ℕ} (R : List FregeRule) (F : CNF n)
    (π : List (MFormula p (Fin n))) : Prop :=
  π.getLast? = some MFormula.bot ∧ IsFregeProof R F π

/-- The proof has depth at most `ℓ`: every line has depth at most `ℓ`. -/
def ProofDepthLE {p n : ℕ} (π : List (MFormula p (Fin n))) (ℓ : ℕ) : Prop :=
  ∀ φ ∈ π, φ.depth ≤ ℓ

/-- Size of a proof: the total number of symbol occurrences in the whole sequence. -/
def proofSize {p n : ℕ} (π : List (MFormula p (Fin n))) : ℕ :=
  (π.map MFormula.size).sum

/-- `M_i`: the number of DISTINCT rooted syntactic subformulas of the proof lines that have
depth `i` and whose output gate is a conjunction or a disjunction. -/
noncomputable def gateCount {p n : ℕ} (π : List (MFormula p (Fin n))) (i : ℕ) : ℕ :=
  Set.ncard {A : MFormula p (Fin n) |
    (∃ L ∈ π, A ∈ L.subformulas) ∧ A.IsAndOr ∧ A.depth = i}

end RandomCNFDeficiency.LowerBound.Supplement


