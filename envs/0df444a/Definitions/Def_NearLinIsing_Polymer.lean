-- Prove2me | Definitions.Def_NearLinIsing_Polymer
-- name    : NearLinIsing_Polymer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:08.041577+00:00
-- url     : https://prove2.me/theorems/bb0b07e9-76b8-4014-849a-c3e283362f43
-- title:
--   Polymer models, $D(\gamma)$, spectral bounds and the insertion–deletion chain
-- statement:
--   A **polymer model** consists of a finite or countable type space $\mathcal P$, activities $w_\gamma$, and a symmetric compatibility relation $\sim$ with $\gamma\not\sim\gamma$ for every type. Configurations are finite pairwise compatible families, with law
--
--   $$\mu(X)=\frac1Z\prod_{\gamma\in X}w_\gamma,\qquad Z=\sum_{X\text{ compatible}}\ \prod_{\gamma\in X}w_\gamma .$$
--
--   Write $A_{\gamma\gamma'}=\mathbf 1\{\gamma\not\sim\gamma'\}$, which includes the diagonal, $W=\mathrm{Diag}(w)$, and $D(\gamma)=\sum_{\gamma'\not\sim\gamma}w_{\gamma'}$. Spectral bounds on $AW$ refer to the symmetric matrix $W^{1/2}AW^{1/2}$: $\lambda_{\min}(AW)\ge c$ means $x^{\mathsf T}W^{1/2}AW^{1/2}x\ge c\|x\|^2$ for finitely supported $x$, and $\lambda_{\max}(AW)\le c$ is the reverse bound.
--
--   The **insertion–deletion chain** with size parameter $N$ moves from $X$ to $X\cup\{\gamma\}$ with probability $w_\gamma/(4N)$ for each $\gamma$ compatible with $X$, to $X\setminus\{\gamma\}$ with probability $1/(4N)$ for each $\gamma\in X$, and stays otherwise. The module also defines its law $\delta_\emptyset P^T$ after $T$ steps from the empty family, and the total-variation distance $\sup_A|\rho(A)-\pi(A)|$ on a countable space.
--
--   These objects carry the paper's general sampling theorem.
--
--   **Formalization Note** Positivity of the activities is a hypothesis of the theorems, not a field. Total variation takes the supremum over finite sets, which equals the supremum over all sets for summable laws; it repeats the body of the published `MarkovMixing.tvDist` without its `Fintype` assumption, which a countable polymer space does not satisfy.
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, Definition 1.4, p. 3; Theorem 1.5, p. 4; §2.1, p. 7; §2.4, p. 9

import Mathlib

namespace NearLinIsing

noncomputable section

open Classical

/-- A **polymer model** (Definition 1.4, p. 3; §2.4, p. 9): a type space `P`, activities `w`, and a
symmetric compatibility relation `compat` (`γ ∼ γ'`) with `γ ≁ γ` for every type.

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, Definition 1.4, p. 3, and §2.4, p. 9.

**Formalization Note.** Positivity of the activities is not a field: theorems that need it assume
`∀ γ, 0 < M.w γ` explicitly. The type space is finite or countable (`[Countable P]` in the
theorems, reading R9). -/
structure PolymerModel (P : Type) where
  /-- the activity `w_γ` -/
  w : P → ℝ
  /-- compatibility `γ ∼ γ'` -/
  compat : P → P → Prop
  symm : ∀ γ γ', compat γ γ' → compat γ' γ
  irrefl : ∀ γ, ¬ compat γ γ

namespace PolymerModel

variable {P : Type} (M : PolymerModel P)

/-- A finite family is **compatible** when its members are pairwise compatible. -/
def IsCompat (X : Finset P) : Prop := ∀ γ ∈ X, ∀ γ' ∈ X, γ ≠ γ' → M.compat γ γ'

/-- The weight `1{X compatible} ∏_{γ ∈ X} w_γ` of a finite family. -/
def weight (X : Finset P) : ℝ := if M.IsCompat X then ∏ γ ∈ X, M.w γ else 0

/-- The partition function `Z = ∑_{X compatible} ∏_{γ ∈ X} w_γ` (Definition 1.4). -/
def Z : ℝ := ∑' X : Finset P, M.weight X

/-- The **polymer law** `µ(X) = Z⁻¹ ∏_{γ ∈ X} w_γ` on compatible families (Definition 1.4). -/
def law (X : Finset P) : ℝ := M.weight X / M.Z

/-- `D(γ) = ∑_{γ' ≁ γ} w_{γ'}`, the total activity conflicting with `γ`; since `γ ≁ γ`, the
diagonal term `w_γ` is included (§2.4, p. 9). -/
def D (γ : P) : ℝ := ∑' γ' : {γ' : P // ¬ M.compat γ γ'}, M.w γ'

/-- The quadratic form `xᵀ W^{1/2} A W^{1/2} x` of the symmetric realization of `AW`, with
`A_{γγ'} = 1{γ ≁ γ'}` (diagonal included), at a finitely supported vector `x` (§2.4, p. 9). -/
def quadForm (x : P →₀ ℝ) : ℝ :=
  ∑ γ ∈ x.support, ∑ γ' ∈ x.support,
    x γ * Real.sqrt (M.w γ) * (if M.compat γ γ' then 0 else 1) * Real.sqrt (M.w γ') * x γ'

/-- `λmin(AW) ≥ c`: the Rayleigh form of `W^{1/2} A W^{1/2}` is at least `c ‖x‖²` on finitely
supported vectors (reading R7). -/
def LambdaMinGe (c : ℝ) : Prop := ∀ x : P →₀ ℝ, c * ∑ γ ∈ x.support, x γ ^ 2 ≤ M.quadForm x

/-- `λmax(AW) ≤ c`: the Rayleigh form of `W^{1/2} A W^{1/2}` is at most `c ‖x‖²` on finitely
supported vectors (reading R7). -/
def LambdaMaxLe (c : ℝ) : Prop := ∀ x : P →₀ ℝ, M.quadForm x ≤ c * ∑ γ ∈ x.support, x γ ^ 2

/-- One step of the **insertion–deletion chain** of Theorem 1.5 (p. 4), from `X` to `Y`:
(i) for each `γ` compatible with every member of `X`, move to `X ∪ {γ}` with probability
`w_γ/(4N)`; (ii) for each `γ ∈ X`, move to `X \ {γ}` with probability `1/(4N)`; (iii) stay with the
remaining probability. -/
def idKernel (N : ℕ) (X Y : Finset P) : ℝ :=
  (if Y = X then
      1 - (∑' γ : {γ : P // ∀ γ' ∈ X, M.compat γ γ'}, M.w γ / (4 * N))
        - (X.card : ℝ) / (4 * N)
    else 0)
  + (∑' γ : {γ : P // ∀ γ' ∈ X, M.compat γ γ'},
      if Y = insert γ.1 X then M.w γ / (4 * N) else 0)
  + ∑ γ ∈ X, if Y = X.erase γ then 1 / (4 * (N : ℝ)) else 0

/-- The law `δ_∅ P^T` of the insertion–deletion chain after `T` steps from the empty family. -/
def stepLaw (N : ℕ) : ℕ → Finset P → ℝ
  | 0 => fun X => if X = ∅ then 1 else 0
  | T + 1 => fun Y => ∑' X : Finset P, stepLaw N T X * M.idKernel N X Y

end PolymerModel

/-- Total variation distance `sup_A |ρ(A) − π(A)|` of two laws on a finite or countable space,
given by their point masses (§2.1, p. 7).

**Formalization Note.** The supremum runs over finite sets `A`; for summable nonnegative laws it
equals the supremum over all subsets. This is the body of the platform definition
`MarkovMixing.tvDist` without its `Fintype` assumption, which the countable polymer space of
Theorem 1.5 does not satisfy. -/
def tvDistC {α : Type} (ρ π : α → ℝ) : ℝ :=
  ⨆ A : Finset α, |∑ x ∈ A, ρ x - ∑ x ∈ A, π x|

end

end NearLinIsing


