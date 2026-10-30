-- Prove2me | Definitions.Def_HofmannStreicher1994_Syntax
-- name    : HofmannStreicher1994_Syntax
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-10-29T06:17:06.974074+00:00
-- url     : https://prove2.me/theorems/6dcb1be2-b401-45ac-87d0-0d2ab2633792
-- title:
--   Annotated syntax and derivability for the selected intensional type theory
-- statement:
--   The object language has dependent products $\Pi$ with judgemental $\beta$ and $\eta$, dependent sums $\Sigma$ with their dependent eliminator and $\beta$ rule, identity types with reflexivity and $J$, natural numbers with dependent recursion, and a universe $U$ with decoding family $\mathrm{El}$. Its contexts, types, terms, judgemental equalities, substitutions and equal substitutions are specified by mutually inductive relations on annotated de Bruijn expressions. Substitution and context conversion are explicit closure rules.
--
--   The selected 1994 universe interface has $U$ as a type and $\mathrm{El}(X)$ as a type whenever $X:U$. It has no small-type code constructors or decoding computation rules, no $U:U$, and no universe induction. There is no equality reflection, $K$, identity-type $\eta$, or judgemental $\Sigma$-$\eta$. The ordinary $\Pi$, $\Sigma$, identity and natural-number constructors remain available, including large sums over $U$.
--
--   The closed expression $A_0=\Sigma X:U.\mathrm{El}(X)$ and the two UIP contexts and conclusions are defined explicitly. The diagonal context is $x:A,p,q:\mathrm{Id}_A(x,x)$ and its conclusion is $\mathrm{Id}_{\mathrm{Id}_A(x,x)}(p,\mathrm{refl}_A(x))$, retaining the unused $q$. The standard context is $x,y:A,p,q:\mathrm{Id}_A(x,y)$ with conclusion $\mathrm{Id}_{\mathrm{Id}_A(x,y)}(p,q)$.
--
--   **Presentation convention.** Expressions carry Church annotations. The application/$\eta$ presentation of $\Pi$ is selected from the fuller Hofmann–Streicher account, Appendix A.4. This is an explicitly fixed rule system for the chosen fragment; it does not assert an annotation comparison with every other presentation of Martin-Löf type theory. These are syntax definitions, with no assumed interpretation or soundness.
-- source:
--   Hofmann and Streicher, A Groupoid Model Refutes Uniqueness of Identity Proofs, author manuscript dated 21 March 1994, https://www.dcs.ed.ac.uk/home/mxh/SH.dvi.gz; LICS 1994, https://doi.org/10.1109/LICS.1994.316071. Manuscript Sections 1–3, pp. 1–7; Pi presentation from the fuller account, Appendix A.4. The mission owner selected the restricted 1994 U/El interface on 29 October 2026.

import Std

/-!
# Object syntax for the Hofmann--Streicher independence theorem

Source: Hofmann--Streicher, March 21, 1994 author manuscript, §§1--3.
The paper specifies J and refers to Nordström--Petersson--Smith for the remaining
rules. Here the application/eta presentation of Pi is fixed explicitly as in
Hofmann--Streicher, *The groupoid interpretation of type theory*, Appendix A.4.
Sigma has its dependent eliminator and beta rule, with no judgmental eta rule.
The first-universe interface consists exactly of U as a type and El as its
generic family, as established in §2.3 of the 1994 manuscript. There are no
small-type code constructors, decoding computation rules, code for U itself,
or universe induction principle. Ordinary Pi, Sigma, Id/J and N remain full
object-theory constructors, including large Pi/Sigma over U. In particular,
Sigma X:U, El(X) remains a closed type. This source-approved scope retains the
literal 1994 discrete universe and does not import closure operations from the
later isomorphism-valued-universe construction. Binary sums and other additional
type formers are outside the explicitly selected fragment.

All object expressions, including object identity proofs, are data in `Type`.
The judgment `TermEq` denotes the object's judgmental equality; it is not an
object identity type and it has no equality-reflection constructor.

Contexts list the most recent binder first. A stored binder type is expressed
in the context preceding that binder. The definitions below are syntax only;
there is no semantic-soundness premise in object derivability.

Application, pairing and Sigma elimination explicitly carry their domain A and
family B. Reflexivity explicitly carries its type A. These Church annotations
make the typing data available to an interpretation defined recursively on raw
syntax; the annotations are also renamed, substituted and compared by congruence.
In each occurrence, B binds one variable over the current context. In Sigma
elimination C binds the pair variable, while d binds its two components.
-/

namespace HofmannStreicher1994

/-- Raw de Bruijn syntax. Bodies of Pi, Sigma and lambda bind one variable;
the Sigma eliminator's branch binds two; the J motive binds three and its branch
binds one; the natural-number step binds a number and its induction hypothesis. -/
inductive Expr where
  | var : Nat → Expr
  | pi : Expr → Expr → Expr
  | sigma : Expr → Expr → Expr
  | identity : Expr → Expr → Expr → Expr
  | nat : Expr
  | universe : Expr
  | el : Expr → Expr
  | lam : Expr → Expr → Expr
  | app : Expr → Expr → Expr → Expr → Expr
  | pair : Expr → Expr → Expr → Expr → Expr
  | sigmaRec : Expr → Expr → Expr → Expr → Expr → Expr
  | refl : Expr → Expr → Expr
  | idRec : Expr → Expr → Expr → Expr → Expr → Expr → Expr
  | zero : Expr
  | succ : Expr → Expr
  | natRec : Expr → Expr → Expr → Expr → Expr
  deriving DecidableEq, Repr

abbrev Context := List Expr

/-- Extend a renaming underneath one binder. -/
def liftRenaming (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

/-- Capture-avoiding simultaneous renaming. -/
def rename (ρ : Nat → Nat) : Expr → Expr
  | .var n => .var (ρ n)
  | .pi A B => .pi (rename ρ A) (rename (liftRenaming ρ) B)
  | .sigma A B => .sigma (rename ρ A) (rename (liftRenaming ρ) B)
  | .identity A a b => .identity (rename ρ A) (rename ρ a) (rename ρ b)
  | .nat => .nat
  | .universe => .universe
  | .el a => .el (rename ρ a)
  | .lam A b => .lam (rename ρ A) (rename (liftRenaming ρ) b)
  | .app A B f a => .app (rename ρ A) (rename (liftRenaming ρ) B)
      (rename ρ f) (rename ρ a)
  | .pair A B a b => .pair (rename ρ A) (rename (liftRenaming ρ) B)
      (rename ρ a) (rename ρ b)
  | .sigmaRec A B C d p => .sigmaRec (rename ρ A) (rename (liftRenaming ρ) B)
      (rename (liftRenaming ρ) C)
      (rename (liftRenaming (liftRenaming ρ)) d) (rename ρ p)
  | .refl A a => .refl (rename ρ A) (rename ρ a)
  | .idRec A C d a b p => .idRec (rename ρ A)
      (rename (liftRenaming (liftRenaming (liftRenaming ρ))) C)
      (rename (liftRenaming ρ) d) (rename ρ a) (rename ρ b) (rename ρ p)
  | .zero => .zero
  | .succ a => .succ (rename ρ a)
  | .natRec C z s n => .natRec (rename (liftRenaming ρ) C) (rename ρ z)
      (rename (liftRenaming (liftRenaming ρ)) s) (rename ρ n)

/-- Weaken an expression by inserting one new most-recent variable. -/
def weaken (e : Expr) : Expr := rename Nat.succ e

/-- Extend a simultaneous substitution underneath a binder. -/
def liftSubstitution (σ : Nat → Expr) : Nat → Expr
  | 0 => .var 0
  | n + 1 => weaken (σ n)

/-- Capture-avoiding simultaneous substitution. -/
def substitute (σ : Nat → Expr) : Expr → Expr
  | .var n => σ n
  | .pi A B => .pi (substitute σ A) (substitute (liftSubstitution σ) B)
  | .sigma A B => .sigma (substitute σ A) (substitute (liftSubstitution σ) B)
  | .identity A a b => .identity (substitute σ A) (substitute σ a) (substitute σ b)
  | .nat => .nat
  | .universe => .universe
  | .el a => .el (substitute σ a)
  | .lam A b => .lam (substitute σ A) (substitute (liftSubstitution σ) b)
  | .app A B f a => .app (substitute σ A) (substitute (liftSubstitution σ) B)
      (substitute σ f) (substitute σ a)
  | .pair A B a b => .pair (substitute σ A) (substitute (liftSubstitution σ) B)
      (substitute σ a) (substitute σ b)
  | .sigmaRec A B C d p => .sigmaRec (substitute σ A) (substitute (liftSubstitution σ) B)
      (substitute (liftSubstitution σ) C)
      (substitute (liftSubstitution (liftSubstitution σ)) d) (substitute σ p)
  | .refl A a => .refl (substitute σ A) (substitute σ a)
  | .idRec A C d a b p => .idRec (substitute σ A)
      (substitute (liftSubstitution (liftSubstitution (liftSubstitution σ))) C)
      (substitute (liftSubstitution σ) d) (substitute σ a) (substitute σ b) (substitute σ p)
  | .zero => .zero
  | .succ a => .succ (substitute σ a)
  | .natRec C z s n => .natRec (substitute (liftSubstitution σ) C) (substitute σ z)
      (substitute (liftSubstitution (liftSubstitution σ)) s) (substitute σ n)

/-- Instantiate the most recent variable, discharging its binder. -/
def instantiate (B a : Expr) : Expr :=
  substitute (fun | 0 => a | n + 1 => .var n) B

/-- Instantiate the two most recent variables: index zero receives `b`. -/
def instantiate₂ (C a b : Expr) : Expr :=
  substitute (fun | 0 => b | 1 => a | n + 2 => .var n) C

/-- Instantiate three most recent variables: index zero receives `p`. -/
def instantiate₃ (C a b p : Expr) : Expr :=
  substitute (fun | 0 => p | 1 => b | 2 => a | n + 3 => .var n) C

/-- The context Γ,x:A,y:A,p:Id_A(x,y), with the appropriate weakenings. -/
def identityContext (Γ : Context) (A : Expr) : Context :=
  .identity (weaken (weaken A)) (.var 1) (.var 0) :: weaken A :: A :: Γ

/-- The restriction of a J motive to (x,x,refl x), in context Γ,x:A. -/
def reflexivityMotive (A C : Expr) : Expr :=
  substitute (fun | 0 => .refl (weaken A) (.var 0) | 1 => .var 0 | 2 => .var 0
                  | n + 3 => .var (n + 1)) C

/-- The restriction of a Sigma motive to pair(x,y), in context Γ,x:A,y:B. -/
def pairingMotive (A B C : Expr) : Expr :=
  substitute (fun
    | 0 => .pair (rename (fun n => n + 2) A)
        (rename (liftRenaming (fun n => n + 2)) B) (.var 1) (.var 0)
    | n + 1 => .var (n + 2)) C

/-- The natural-recursion successor motive, in context Γ,n:N,h:C(n). -/
def successorMotive (C : Expr) : Expr :=
  substitute (fun | 0 => .succ (.var 1) | n + 1 => .var (n + 2)) C

/-! The five judgments and simultaneous substitution are the least relations
closed under the displayed rules. Structural substitution is included explicitly
so that judgmental equality is stable under substitution of equal terms. -/
mutual
  /-- Well-formed object contexts. -/
  inductive ContextWf : Context → Prop where
    | nil : ContextWf []
    | cons {Γ A} : ContextWf Γ → TypeWf Γ A → ContextWf (A :: Γ)

  /-- Formation of object types (including the large first universe). -/
  inductive TypeWf : Context → Expr → Prop where
    | pi {Γ A B} : TypeWf Γ A → TypeWf (A :: Γ) B → TypeWf Γ (.pi A B)
    | sigma {Γ A B} : TypeWf Γ A → TypeWf (A :: Γ) B → TypeWf Γ (.sigma A B)
    | identity {Γ A a b} : TypeWf Γ A → TermWf Γ a A → TermWf Γ b A →
        TypeWf Γ (.identity A a b)
    | nat {Γ} : ContextWf Γ → TypeWf Γ .nat
    | universe {Γ} : ContextWf Γ → TypeWf Γ .universe
    | el {Γ a} : TermWf Γ a .universe → TypeWf Γ (.el a)
    | subst {Γ Δ A σ} : TypeWf Γ A → SubstitutionWf Γ Δ σ →
        TypeWf Δ (substitute σ A)
    | context {Γ Δ A} : TypeWf Γ A → ContextEq Γ Δ → TypeWf Δ A

  /-- Object term formation. -/
  inductive TermWf : Context → Expr → Expr → Prop where
    | var {Γ n A} : ContextWf Γ → Γ[n]? = some A →
        TermWf Γ (.var n) (rename (fun k => k + n + 1) A)
    | lam {Γ A B b} : TypeWf Γ A → TypeWf (A :: Γ) B → TermWf (A :: Γ) b B →
        TermWf Γ (.lam A b) (.pi A B)
    | app {Γ A B f a} : TypeWf Γ A → TypeWf (A :: Γ) B →
        TermWf Γ f (.pi A B) → TermWf Γ a A → TermWf Γ (.app A B f a) (instantiate B a)
    | pair {Γ A B a b} : TypeWf Γ A → TypeWf (A :: Γ) B →
        TermWf Γ a A → TermWf Γ b (instantiate B a) →
        TermWf Γ (.pair A B a b) (.sigma A B)
    | sigmaRec {Γ A B C d p} : TypeWf Γ A → TypeWf (A :: Γ) B →
        TypeWf (.sigma A B :: Γ) C → TermWf (B :: A :: Γ) d (pairingMotive A B C) →
        TermWf Γ p (.sigma A B) → TermWf Γ (.sigmaRec A B C d p) (instantiate C p)
    | refl {Γ A a} : TypeWf Γ A → TermWf Γ a A →
        TermWf Γ (.refl A a) (.identity A a a)
    | idRec {Γ A C d a b p} : TypeWf Γ A → TypeWf (identityContext Γ A) C →
        TermWf (A :: Γ) d (reflexivityMotive A C) → TermWf Γ a A → TermWf Γ b A →
        TermWf Γ p (.identity A a b) →
        TermWf Γ (.idRec A C d a b p) (instantiate₃ C a b p)
    | zero {Γ} : ContextWf Γ → TermWf Γ .zero .nat
    | succ {Γ n} : TermWf Γ n .nat → TermWf Γ (.succ n) .nat
    | natRec {Γ C z s n} : TypeWf (.nat :: Γ) C →
        TermWf Γ z (instantiate C .zero) → TermWf (C :: .nat :: Γ) s (successorMotive C) →
        TermWf Γ n .nat → TermWf Γ (.natRec C z s n) (instantiate C n)
    | conv {Γ a A B} : TermWf Γ a A → TypeEq Γ A B → TermWf Γ a B
    | subst {Γ Δ a A σ} : TermWf Γ a A → SubstitutionWf Γ Δ σ →
        TermWf Δ (substitute σ a) (substitute σ A)
    | context {Γ Δ a A} : TermWf Γ a A → ContextEq Γ Δ → TermWf Δ a A

  /-- Judgmental equality of object types. -/
  inductive TypeEq : Context → Expr → Expr → Prop where
    | refl {Γ A} : TypeWf Γ A → TypeEq Γ A A
    | symm {Γ A B} : TypeEq Γ A B → TypeEq Γ B A
    | trans {Γ A B C} : TypeEq Γ A B → TypeEq Γ B C → TypeEq Γ A C
    | pi {Γ A A' B B'} : TypeEq Γ A A' → TypeEq (A :: Γ) B B' →
        TypeEq Γ (.pi A B) (.pi A' B')
    | sigma {Γ A A' B B'} : TypeEq Γ A A' → TypeEq (A :: Γ) B B' →
        TypeEq Γ (.sigma A B) (.sigma A' B')
    | identity {Γ A A' a a' b b'} : TypeEq Γ A A' → TermEq Γ a a' A →
        TermEq Γ b b' A → TypeEq Γ (.identity A a b) (.identity A' a' b')
    | el {Γ a b} : TermEq Γ a b .universe → TypeEq Γ (.el a) (.el b)
    | subst {Γ Δ A B σ} : TypeEq Γ A B → SubstitutionWf Γ Δ σ →
        TypeEq Δ (substitute σ A) (substitute σ B)
    | substEq {Γ Δ A σ τ} : TypeWf Γ A → SubstitutionEq Γ Δ σ τ →
        TypeEq Δ (substitute σ A) (substitute τ A)
    | context {Γ Δ A B} : TypeEq Γ A B → ContextEq Γ Δ → TypeEq Δ A B

  /-- Judgmental equality of object terms, generated by congruence and beta/eta
rules. There is no reflection of object identity proofs into this judgment. -/
  inductive TermEq : Context → Expr → Expr → Expr → Prop where
    | refl {Γ a A} : TermWf Γ a A → TermEq Γ a a A
    | symm {Γ a b A} : TermEq Γ a b A → TermEq Γ b a A
    | trans {Γ a b c A} : TermEq Γ a b A → TermEq Γ b c A → TermEq Γ a c A
    | conv {Γ a b A B} : TermEq Γ a b A → TypeEq Γ A B → TermEq Γ a b B
    | lam {Γ A A' B b b'} : TypeEq Γ A A' → TypeWf (A :: Γ) B →
        TermEq (A :: Γ) b b' B → TermEq Γ (.lam A b) (.lam A' b') (.pi A B)
    | app {Γ A A' B B' f f' a a'} : TypeEq Γ A A' → TypeEq (A :: Γ) B B' →
        TermEq Γ f f' (.pi A B) → TermEq Γ a a' A →
        TermEq Γ (.app A B f a) (.app A' B' f' a') (instantiate B a)
    | pair {Γ A A' B B' a a' b b'} : TypeEq Γ A A' → TypeEq (A :: Γ) B B' →
        TermEq Γ a a' A → TermEq Γ b b' (instantiate B a) →
        TermEq Γ (.pair A B a b) (.pair A' B' a' b') (.sigma A B)
    | sigmaRec {Γ A A' B B' C C' d d' p p'} : TypeEq Γ A A' → TypeEq (A :: Γ) B B' →
        TypeEq (.sigma A B :: Γ) C C' →
        TermEq (B :: A :: Γ) d d' (pairingMotive A B C) →
        TermEq Γ p p' (.sigma A B) →
        TermEq Γ (.sigmaRec A B C d p) (.sigmaRec A' B' C' d' p') (instantiate C p)
    | reflCongr {Γ A A' a a'} : TypeEq Γ A A' → TermEq Γ a a' A →
        TermEq Γ (.refl A a) (.refl A' a') (.identity A a a)
    | idRec {Γ A A' C C' d d' a a' b b' p p'} : TypeEq Γ A A' →
        TypeEq (identityContext Γ A) C C' →
        TermEq (A :: Γ) d d' (reflexivityMotive A C) → TermEq Γ a a' A →
        TermEq Γ b b' A → TermEq Γ p p' (.identity A a b) →
        TermEq Γ (.idRec A C d a b p) (.idRec A' C' d' a' b' p') (instantiate₃ C a b p)
    | succ {Γ n n'} : TermEq Γ n n' .nat → TermEq Γ (.succ n) (.succ n') .nat
    | natRec {Γ C C' z z' s s' n n'} : TypeEq (.nat :: Γ) C C' →
        TermEq Γ z z' (instantiate C .zero) →
        TermEq (C :: .nat :: Γ) s s' (successorMotive C) → TermEq Γ n n' .nat →
        TermEq Γ (.natRec C z s n) (.natRec C' z' s' n') (instantiate C n)
    | betaPi {Γ A B b a} : TypeWf Γ A → TypeWf (A :: Γ) B →
        TermWf (A :: Γ) b B → TermWf Γ a A →
        TermEq Γ (.app A B (.lam A b) a) (instantiate b a) (instantiate B a)
    | etaPi {Γ A B f} : TypeWf Γ A → TypeWf (A :: Γ) B → TermWf Γ f (.pi A B) →
        TermEq Γ (.lam A (.app (weaken A) (rename (liftRenaming Nat.succ) B) (weaken f) (.var 0))) f (.pi A B)
    | betaSigma {Γ A B C d a b} : TypeWf Γ A → TypeWf (A :: Γ) B →
        TypeWf (.sigma A B :: Γ) C → TermWf (B :: A :: Γ) d (pairingMotive A B C) →
        TermWf Γ a A → TermWf Γ b (instantiate B a) →
        TermEq Γ (.sigmaRec A B C d (.pair A B a b)) (instantiate₂ d a b)
          (instantiate C (.pair A B a b))
    | betaId {Γ A C d a} : TypeWf Γ A → TypeWf (identityContext Γ A) C →
        TermWf (A :: Γ) d (reflexivityMotive A C) → TermWf Γ a A →
        TermEq Γ (.idRec A C d a a (.refl A a)) (instantiate d a)
          (instantiate₃ C a a (.refl A a))
    | betaNatZero {Γ C z s} : TypeWf (.nat :: Γ) C →
        TermWf Γ z (instantiate C .zero) → TermWf (C :: .nat :: Γ) s (successorMotive C) →
        TermEq Γ (.natRec C z s .zero) z (instantiate C .zero)
    | betaNatSucc {Γ C z s n} : TypeWf (.nat :: Γ) C →
        TermWf Γ z (instantiate C .zero) → TermWf (C :: .nat :: Γ) s (successorMotive C) →
        TermWf Γ n .nat →
        TermEq Γ (.natRec C z s (.succ n)) (instantiate₂ s n (.natRec C z s n))
          (instantiate C (.succ n))
    | subst {Γ Δ a b A σ} : TermEq Γ a b A → SubstitutionWf Γ Δ σ →
        TermEq Δ (substitute σ a) (substitute σ b) (substitute σ A)
    | substEq {Γ Δ a A σ τ} : TermWf Γ a A → SubstitutionEq Γ Δ σ τ →
        TermEq Δ (substitute σ a) (substitute τ a) (substitute σ A)
    | context {Γ Δ a b A} : TermEq Γ a b A → ContextEq Γ Δ → TermEq Δ a b A

  /-- Pointwise well-typed simultaneous substitutions, from Γ into Δ. -/
  inductive SubstitutionWf : Context → Context → (Nat → Expr) → Prop where
    | mk {Γ Δ σ} : ContextWf Γ → ContextWf Δ →
        (∀ n A, Γ[n]? = some A →
          TermWf Δ (σ n) (substitute σ (rename (fun k => k + n + 1) A))) →
        SubstitutionWf Γ Δ σ

  /-- Pointwise equal simultaneous substitutions. -/
  inductive SubstitutionEq : Context → Context → (Nat → Expr) → (Nat → Expr) → Prop where
    | mk {Γ Δ σ τ} : SubstitutionWf Γ Δ σ → SubstitutionWf Γ Δ τ →
        (∀ n A, Γ[n]? = some A →
          TermEq Δ (σ n) (τ n) (substitute σ (rename (fun k => k + n + 1) A))) →
        SubstitutionEq Γ Δ σ τ

  /-- Context conversion by judgmentally equal binder types. -/
  inductive ContextEq : Context → Context → Prop where
    | nil : ContextEq [] []
    | cons {Γ Δ A B} : ContextEq Γ Δ → TypeEq Γ A B → ContextEq (A :: Γ) (B :: Δ)
end

/-- The closed type used in the 1994 proof: Σ X:U, El X. -/
def counterexampleType : Expr := .sigma .universe (.el (.var 0))

/-- The exact printed context x:A,p:Id_A(x,x),q:Id_A(x,x); q is intentionally
retained even though it is unused in the printed conclusion. -/
def diagonalContext (A : Expr) : Context :=
  .identity (weaken (weaken A)) (.var 1) (.var 1) ::
    .identity (weaken A) (.var 0) (.var 0) :: A :: []

/-- The exact printed conclusion Id_{Id_A(x,x)}(p,refl_A(x)), in the context
with x at index 2, p at index 1 and q at index 0. -/
def diagonalConclusion (A : Expr) : Expr :=
  .identity (.identity (rename (fun n => n + 3) A) (.var 2) (.var 2))
    (.var 1) (.refl (rename (fun n => n + 3) A) (.var 2))

/-- The standard UIP context x:A,y:A,p:Id_A(x,y),q:Id_A(x,y). -/
def uipContext (A : Expr) : Context :=
  .identity (rename (fun n => n + 3) A) (.var 2) (.var 1) ::
    .identity (weaken (weaken A)) (.var 1) (.var 0) :: weaken A :: A :: []

/-- The standard UIP conclusion Id_{Id_A(x,y)}(p,q). -/
def uipConclusion (A : Expr) : Expr :=
  .identity (.identity (rename (fun n => n + 4) A) (.var 3) (.var 2)) (.var 1) (.var 0)

end HofmannStreicher1994


