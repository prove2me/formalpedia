-- Prove2me | Definitions.Def_RobustBoolPCSP_Supplement_PPConstruction
-- name    : RobustBoolPCSP_Supplement_PPConstruction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:24:40.712187+00:00
-- url     : https://prove2.me/theorems/8d9d908c-5aca-4c4a-ad55-0627f08ccc30
-- title:
--   pp-powers, homomorphic relaxations, pp-constructibility, $\mathrm{PP}(\mathrm{MC})$ and $\Sigma_{\mathrm{maj}}$
-- statement:
--   A **primitive positive formula** over the signature of a template is an existentially quantified conjunction of relational atoms and equalities. The **$n$-th pp-power** of $T$ ($n\ge1$) has domains $A^n$, $B^n$ and relations defined by pp-formulas on the $n$ coordinates of each argument, interpreted in the strong and in the weak structure. A **homomorphic relaxation** of $T$ is a template of the same signature with homomorphisms $A'\to A$ of the strong and $B\to B'$ of the weak structures. A template is **pp-constructible** from $T$ if it arises by finitely many such steps [BBKO21]; $\mathrm{PP}(\mathrm{MC})$ is the class of templates pp-constructible from a member of $\mathrm{MC}$.
--
--   A template satisfies the bipartite minor condition
--
--   $$\Sigma_{\mathrm{maj}}:\quad f(x,x,y)=f(x,y,x)=f(y,x,x)=u(x)$$
--
--   if some ternary polymorphism $f$ and unary polymorphism $u$ obey these identities. The module also defines $d(x,y,z)=y$ if $y=z$ and $x$ otherwise.
--
--   These notions state the strict separation of $\mathrm{MC}$ and $\mathrm{CS}_{\mathrm{out}}$ under pp-constructions (Theorems 5.20 and 5.22).
--
--   **Formalization Note** Every template in a chain is finite with nonempty domains; pp-powers are taken with a finite new signature.
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §5.4, p.42 (PP(C), Σmaj (46), d); [BBKO21, Definitions 4.7, 4.9] as cited on pp.15, 42

import Mathlib
import Definitions.Def_RobustBoolPCSP_Supplement_Classes

set_option autoImplicit false

namespace RobustBoolPCSP.Supplement

open RobustBoolPCSP

/-- A **primitive positive formula** over a signature with arities `r : ι → ℕ`, with free variables
`V` and `m` existentially quantified variables `Fin m`: a finite list of atoms `R_j(u_1, …, u_{r_j})`
and a finite list of equality atoms `u = u'`, the arguments ranging over `V ⊕ Fin m`. -/
structure PPFormula {ι : Type} (r : ι → ℕ) (V : Type) where
  /-- The number of existentially quantified variables. -/
  m : ℕ
  /-- The relational atoms. -/
  atoms : List (Σ j : ι, Fin (r j) → V ⊕ Fin m)
  /-- The equality atoms. -/
  eqs : List ((V ⊕ Fin m) × (V ⊕ Fin m))

/-- The formula `φ` holds of the free-variable assignment `x : V → X` in the structure with relations
`R_j ⊆ X^{r_j}`: some values `y` of the quantified variables satisfy every atom. -/
def PPFormula.Holds {ι : Type} {r : ι → ℕ} {V X : Type} (φ : PPFormula r V)
    (R : (j : ι) → Set (Fin (r j) → X)) (x : V → X) : Prop :=
  ∃ y : Fin φ.m → X, (∀ a ∈ φ.atoms, (fun i => Sum.elim x y (a.2 i)) ∈ R a.1) ∧
    ∀ e ∈ φ.eqs, Sum.elim x y e.1 = Sum.elim x y e.2

/-- The **`n`-th pp-power** of `T` with new signature `r' : ι' → ℕ` defined by the pp-formulas `φ`:
the template with domains `A^n`, `B^n` whose `j`-th relations consist of the tuples
`(a_1, …, a_{r'_j})` of `A^n` (resp. `B^n`) for which `φ_j` holds of the `r'_j · n` coordinates
`(a_k)_l`, interpreted in the strong (resp. weak) structure of `T` [BBKO21, Definition 4.7]. -/
def ppPower {ι A B : Type} (T : Template ι A B) (n : ℕ) {ι' : Type} (r' : ι' → ℕ)
    (φ : (j : ι') → PPFormula T.r (Fin (r' j) × Fin n)) : Template ι' (Fin n → A) (Fin n → B) where
  r := r'
  P := fun j => {x | (φ j).Holds T.P (fun p => x p.1 p.2)}
  Q := fun j => {y | (φ j).Holds T.Q (fun p => y p.1 p.2)}

/-- **pp-constructibility** [BBKO21, Definition 4.9], used in §5.4, p.42 ("if T′ is
pp-constructible from T, which includes pp-powers and homomorphic relaxations"): `T'` is obtained
from `T` by a finite chain of pp-powers (`n ≥ 1`, finite signature) and homomorphic relaxations.
A homomorphic relaxation of `T₁` (same signature) is a template `(A', B'; P', Q')` with
homomorphisms `e : A' → A₁` of the strong structures and `g : B₁ → B'` of the weak structures.

**Formalization Note.** Every intermediate template is finite with nonempty domains: pp-powers of
such templates are, and the relaxation step asks for it. -/
inductive PPConstructible {ι A B : Type} (T : Template ι A B) :
    {ι' A' B' : Type} → Template ι' A' B' → Prop
  | refl : PPConstructible T T
  | power {ι₁ A₁ B₁ : Type} {T₁ : Template ι₁ A₁ B₁} (h : PPConstructible T T₁) (n : ℕ)
      (hn : 1 ≤ n) {ι' : Type} [Fintype ι'] (r' : ι' → ℕ)
      (φ : (j : ι') → PPFormula T₁.r (Fin (r' j) × Fin n)) :
      PPConstructible T (ppPower T₁ n r' φ)
  | relax {ι₁ A₁ B₁ A' B' : Type} {T₁ : Template ι₁ A₁ B₁} (h : PPConstructible T T₁)
      [Fintype A'] [Nonempty A'] [Fintype B'] [Nonempty B']
      (P' : (j : ι₁) → Set (Fin (T₁.r j) → A')) (Q' : (j : ι₁) → Set (Fin (T₁.r j) → B'))
      (e : A' → A₁) (g : B₁ → B')
      (he : ∀ j, ∀ x ∈ P' j, e ∘ x ∈ T₁.P j) (hg : ∀ j, ∀ y ∈ T₁.Q j, g ∘ y ∈ Q' j) :
      PPConstructible T (⟨T₁.r, P', Q'⟩ : Template ι₁ A' B')

/-- `T ∈ PP(MC)` (§5.4, p.42: "Write PP(C) for the templates pp-constructible from a member of a
class C"): `T` is pp-constructible from a finite template with nonempty domains in `MC`. -/
def InPPMC {ι A B : Type} (T : Template ι A B) : Prop :=
  ∃ (ι₀ A₀ B₀ : Type) (_ : Fintype ι₀) (_ : Fintype A₀) (_ : DecidableEq A₀) (_ : Nonempty A₀)
    (_ : Fintype B₀) (_ : Nonempty B₀) (T₀ : Template ι₀ A₀ B₀), InMC T₀ ∧ PPConstructible T₀ T

/-- The template satisfies the bipartite minor condition **`Σmaj`** (46), p.42,
"f(x, x, y) = f(x, y, x) = f(y, x, x) = u(x)", in its polymorphism minion: some ternary polymorphism
`f` and unary polymorphism `u` obey these identities for all `x, y ∈ A`. -/
def SatisfiesSigmaMaj {ι A B : Type} (T : Template ι A B) : Prop :=
  ∃ (f : (Fin 3 → A) → B) (u : (Fin 1 → A) → B), IsPol T f ∧ IsPol T u ∧
    ∀ x y : A, f ![x, x, y] = u ![x] ∧ f ![x, y, x] = u ![x] ∧ f ![y, x, x] = u ![x]

/-- The ternary operation `d(x, y, z) = y` if `y = z`, and `x` otherwise (Theorem 5.20, p.42). -/
def dMaj {A : Type} [DecidableEq A] (x : Fin 3 → A) : A :=
  if x 1 = x 2 then x 1 else x 0

end RobustBoolPCSP.Supplement


