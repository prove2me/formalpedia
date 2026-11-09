-- Prove2me | Definitions.Def_GoodQLTC_IsProductExpanding
-- name    : GoodQLTC_IsProductExpanding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:40:47.14296+00:00
-- url     : https://prove2.me/theorems/9be1815c-050a-4c7c-a7c3-a06ad4b56950
-- title:
--   $\rho$-product expansion and universal $\rho$-product expansion (Definition 4.6)
-- statement:
--   Let $\Omega_i$ ($i\in I$) be finite sets with $|\Omega_i|=n_i$, $\Omega=\prod_i\Omega_i$, and $C_i\subseteq K^{\Omega_i}$ linear codes. Put $A_i(C_i)=C_i\otimes\bigotimes_{j\ne i}K^{\Omega_j}$ (the arrays all of whose $i$-lines lie in $C_i$), $A(\{C_i\})=\sum_iA_i(C_i)$, and let $\ell_i(x)$ be the number of nonzero $i$-lines of $x$. For $\rho>0$ the family is **$\rho$-product-expanding** if every $x\in A(\{C_i\})$ admits $x_i\in A_i(C_i)$ with
--   $$
--   x=\sum_{i\in I}x_i\qquad\text{and}\qquad \rho\sum_{i\in I}n_i\,\ell_i(x_i)\le|x| .
--   $$
--   A family over $F$ is **universally $\rho$-product-expanding** if $\{C_i\otimes_FE\}$ is $\rho$-product-expanding over $E$ for every field extension $E/F$.
--
--   **Formalization Note** $C_i\otimes_FE$ is the $E$-span of $C_i$ in $E^{\Omega_i}$; extensions range over all fields $E$ with an $F$-algebra structure in a universe parameter; $\rho>0$ is part of the predicate.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §4.2 and Definition 4.6, pp.16–17 (PDF pp.19–20)

import Mathlib

namespace GoodQLTC

universe u

/-- The space `A_i(C_i) := C_i ⊗ ⨂_{j ≠ i} K^{Ω_j} ⊆ K^Ω`, `Ω := ∏_i Ω_i`, Gay–Jeronimo,
arXiv:2609.20780 (held version), §4.2, p.16.

**Formalization Note.** Arrays are functions `(∀ i, Ω i) → K`. `A_i(C_i)` is described as the
arrays every `i`-line `ω_i ↦ x(ω_i, b)` of which lies in `C_i`, which is the same subspace as the
tensor product under `K^Ω = ⨂_i K^{Ω_i}`. -/
def axisCode {K : Type u} [Field K] {ι : Type} [DecidableEq ι] {Ω : ι → Type}
    (C : ∀ i, Submodule K (Ω i → K)) (i : ι) : Submodule K ((∀ i, Ω i) → K) :=
  ⨅ b : (∀ i, Ω i), (C i).comap (LinearMap.funLeft K K (Function.update b i))

open Classical in
/-- The number `ℓ_i(x) := |{b ∈ Ω_{I∖{i}} : x(·, b) ≠ 0}|` of nonzero `i`-lines of an array `x`
with values in any space `M` (arXiv:2609.20780, §4.2, p.16). **Formalization Note.** Computed as
the number of distinct restrictions to the coordinates `≠ i` of the support of `x`. -/
noncomputable def lineCount {ι : Type} [Fintype ι] {Ω : ι → Type} [∀ i, Fintype (Ω i)]
    {M : Type*} [Zero M] (i : ι) (x : (∀ i, Ω i) → M) : ℕ :=
  ((Finset.univ.filter fun ω => x ω ≠ 0).image fun ω => fun j : {j // j ≠ i} => ω j.1).card

open Classical in
/-- The support size `|x| := |{ω : x(ω) ≠ 0}|` of an array with values in any space; for
vector-valued arrays this is the block weight `|x|_b` (arXiv:2609.20780, §4.2, p.16). -/
noncomputable def supportCard {α M : Type*} [Fintype α] [Zero M] (x : α → M) : ℕ :=
  (Finset.univ.filter fun a => x a ≠ 0).card

/-- **`ρ`-product expansion**, Gay–Jeronimo, arXiv:2609.20780 (held version), Definition 4.6,
p.17: for `ρ > 0`, the family `{C_i}_{i∈I}` is `ρ`-product-expanding if every
`x ∈ A({C_i}) := ∑_i A_i(C_i)` admits `x_i ∈ A_i(C_i)` with `x = ∑_i x_i` and
`ρ ∑_i n_i ℓ_i(x_i) ≤ |x|`, where `n_i = |Ω_i|`.

**Formalization Note.** The index set `I` is a finite type `ι`; `ρ > 0` is part of the predicate.
The field `K` is arbitrary (it is `F` or an extension `E` of `F` in the paper). -/
def IsProductExpanding {K : Type u} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type} [∀ i, Fintype (Ω i)] (ρ : ℝ) (C : ∀ i, Submodule K (Ω i → K)) : Prop :=
  0 < ρ ∧ ∀ x ∈ ⨆ i, axisCode C i, ∃ y : ι → ((∀ i, Ω i) → K), (∀ i, y i ∈ axisCode C i) ∧
    x = ∑ i, y i ∧ ρ * ∑ i, (Fintype.card (Ω i) : ℝ) * (lineCount i (y i) : ℝ) ≤ supportCard x

/-- The extended code `C^E := C ⊗_F E ⊆ E^Ω` of a code `C ⊆ F^Ω` (arXiv:2609.20780, §4.2,
p.16), as the `E`-span of the image of `C`. -/
def extendCode {F : Type} [Field F] (E : Type u) [Field E] [Algebra F E] {Ω : Type}
    (C : Submodule F (Ω → F)) : Submodule E (Ω → E) :=
  Submodule.span E ((fun c : Ω → F => fun ω => algebraMap F E (c ω)) '' (C : Set (Ω → F)))

/-- **Universal `ρ`-product expansion**, Gay–Jeronimo, arXiv:2609.20780 (held version),
Definition 4.6, p.17: `{C_i^E}_{i∈I}` is `ρ`-product-expanding over `E` for every field extension
`E/F`.

**Formalization Note.** The extensions range over all fields `E : Type u` with an `F`-algebra
structure, in a universe `u` left as a parameter (theorems keep it free); no finiteness or
algebraicity is imposed on `E`. -/
def IsUnivProductExpanding {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type} [∀ i, Fintype (Ω i)] (ρ : ℝ) (C : ∀ i, Submodule F (Ω i → F)) : Prop :=
  ∀ (E : Type u) [Field E] [Algebra F E], IsProductExpanding ρ fun i => extendCode E (C i)

end GoodQLTC


