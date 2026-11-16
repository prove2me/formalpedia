-- Prove2me | Definitions.Def_RobustBoolPCSP_Supplement_Classes
-- name    : RobustBoolPCSP_Supplement_Classes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:20:52.017064+00:00
-- url     : https://prove2.me/theorems/fe672596-5541-416d-86ad-9654a99ad50c
-- title:
--   Polymorphisms, symmetric Plurality, the classes $\mathfrak P$ and $\mathrm{MC}$, homomorphisms and soft equality
-- statement:
--   For a finite promise template $T$ with relation pairs $(P_j,Q_j)$:
--
--   1. A **polymorphism** of arity $n$ is a map $f:A^n\to B$ such that applying $f$ coordinatewise to any $n$ tuples of $P_j$ gives a tuple of $Q_j$, for every $j$.
--   2. When $A=B$, a **symmetric Plurality operation** returns a most frequent input value and is invariant under permutations of its inputs; the class $\mathfrak P$ consists of the same-domain templates with a symmetric Plurality polymorphism at every positive arity.
--   3. For an output map $h:A\to B$, the **pulled-back relation** is $W_j=(h^{r_j})^{-1}(Q_j)$, and $\mathrm{MC}$ is the class of templates for which some $h$ gives every pair $(P_j,W_j)$ the mode property.
--   4. A **homomorphism** $h:A\to B$ maps every $P_j$ into $Q_j$ coordinatewise.
--   5. The **soft-equality expansion** $T^{=}$ adds the binary pair $(\mathrm{EQ}_A,\mathrm{EQ}_B)$, $\mathrm{EQ}_D=\{(a,a):a\in D\}$, as an ordinary constraint counted in both errors.
--
--   These notions organize the classwise statements of the supplement.
--
--   **Formalization Note** In $T^{=}$ the original symbols are `some j` and the equality symbol is `none`; no variables are identified.
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §2.2 p.8–9 (W_j, MC, 𝔓), §2.3 p.11 (T^=), §3.1 p.15 (polymorphisms, symmetric Plurality, homomorphisms)

import Mathlib
import Definitions.Def_RobustBoolPCSP_Template
import Definitions.Def_RobustBoolPCSP_ModeProperty

set_option autoImplicit false

namespace RobustBoolPCSP.Supplement

open RobustBoolPCSP

/-- `f : A^n → B` is a **polymorphism** of the template `T`.
Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03, sha256
fd1be0d0…), §3.1, p.15: "A polymorphism of arity n is a map f : A^n → B such that, for every j,
applying f coordinatewise to any n tuples in P_j produces a tuple in Q_j."

**Formalization Note.** The `n` input tuples are `x k`, `k : Fin n`; the output tuple has `i`-th
entry `f (fun k => x k i)`. Arity `n = 0` is allowed by the definition (a constant map). -/
def IsPol {ι A B : Type} (T : Template ι A B) {n : ℕ} (f : (Fin n → A) → B) : Prop :=
  ∀ j, ∀ x : Fin n → Fin (T.r j) → A, (∀ k, x k ∈ T.P j) → (fun i => f (fun k => x k i)) ∈ T.Q j

/-- `f : A^n → A` is a **symmetric Plurality operation** (§3.1, p.15): "When A = B, a symmetric
Plurality operation returns a most frequent input value and is invariant under permutations of the
input positions. Its tie-breaking rule may depend on the operation and on the input multiset." -/
def IsSymPlurality {A : Type} [DecidableEq A] {n : ℕ} (f : (Fin n → A) → A) : Prop :=
  (∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → A), f (x ∘ σ) = f x) ∧
    ∀ (x : Fin n → A) (a : A),
      (Finset.univ.filter (fun k => x k = a)).card ≤
        (Finset.univ.filter (fun k => x k = f x)).card

/-- The class `𝔓` (p.9): a same-domain template admits a symmetric Plurality polymorphism at every
positive arity. "Write … P for same-domain templates with symmetric Plurality at every positive
arity." -/
def InPlur {ι A : Type} [DecidableEq A] (T : Template ι A A) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ f : (Fin n → A) → A, IsSymPlurality f ∧ IsPol T f

/-- The **pulled-back relation** `W_j = (h^{r_j})⁻¹(Q_j) ⊆ A^{r_j}` of an output map `h : A → B`
(§2.2, p.8); `h^r` acts coordinatewise (on nullary tuples it is the unique map). -/
def pullback {ι A B : Type} (T : Template ι A B) (h : A → B) (j : ι) : Set (Fin (T.r j) → A) :=
  {x | h ∘ x ∈ T.Q j}

/-- The class `MC` (p.9): "Write MC for templates satisfying the mode property for some output map",
i.e. some `h : A → B` gives every pair `(P_j, W_j)` the mode property (published
`RobustBoolPCSP.ModeProperty`, Definition 2.3). -/
def InMC {ι A B : Type} [Fintype A] [DecidableEq A] (T : Template ι A B) : Prop :=
  ∃ h : A → B, ∀ j, ModeProperty (T.P j) (pullback T h j)

/-- `h : A → B` is a **homomorphism** of the template (§3.1, p.15): "A homomorphism h : A → B maps
every strong relation into its weak partner coordinatewise." -/
def IsHom {ι A B : Type} (T : Template ι A B) (h : A → B) : Prop :=
  ∀ j, ∀ x ∈ T.P j, h ∘ x ∈ T.Q j

/-- The **soft-equality expansion** `T^=` (§2.3, p.11): "For domains A, B, the expansion T^= adds the
relation pair (EQ_A, EQ_B), where EQ_D = {(a, a) : a ∈ D}. Its constraints are soft equality
constraints: they are ordinary constraints of the robust instance, counted in the strong and weak
errors".

**Formalization Note.** The new index type is `Option ι`: `some j` is the original pair `j`,
`none` the binary equality pair. Equality constraints are ordinary constraints of the instance;
no variables are identified. -/
def withEq {ι A B : Type} (T : Template ι A B) : Template (Option ι) A B where
  r := fun o => match o with
    | none => 2
    | some j => T.r j
  P := fun o => match o with
    | none => {x : Fin 2 → A | x 0 = x 1}
    | some j => T.P j
  Q := fun o => match o with
    | none => {y : Fin 2 → B | y 0 = y 1}
    | some j => T.Q j

end RobustBoolPCSP.Supplement


