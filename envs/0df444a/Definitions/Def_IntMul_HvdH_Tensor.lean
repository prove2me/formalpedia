-- Prove2me | Definitions.Def_IntMul_HvdH_Tensor
-- name    : IntMul_HvdH_Tensor
-- status  : Definition
-- author  : @avi
-- created : 2026-10-09T01:43:46.984979+00:00
-- url     : https://prove2.me/theorems/e07f90a0-7c1b-4e57-86ca-ca2947945d37
-- title:
--   Multidimensional complex DFT $\mathcal F_{n_1,\dots,n_d}$ (Harvey–van der Hoeven §2.4)
-- statement:
--   An element of $\bigotimes_{i=1}^d \mathbb C^{n_i}$ is a $d$-dimensional array $u=(u_{j_1,\dots,j_d})$, indexed by $\prod_i \mathbb Z/n_i\mathbb Z$ (so, as in §2.4 of the paper, an index $j_i$ is always read modulo $n_i$). `TIdx n` is this index set.
--
--   `dftN n` is the normalised multidimensional DFT $\mathcal F_{n_1,\dots,n_d} = \bigotimes_i \mathcal F_{n_i}$:
--   $$(\mathcal F_{n_1,\dots,n_d}\,u)_{j} = \frac{1}{n_1\cdots n_d}\sum_{k}\ \prod_{i=1}^d e^{-2\pi i\, j_i k_i/n_i}\; u_{k},$$
--   where $j_i,k_i\in\{0,\dots,n_i-1\}$ are the canonical representatives. It is a continuous $\mathbb C$-linear map; Mathlib's norm on arrays is the supremum norm $\|u\|=\max_j|u_j|$ of §2.3, so operator norms are those of §2.6. For $d=1$ it agrees with `dft` of `IntMul_HvdH_Resampling`.
-- source:
--   D. Harvey, J. van der Hoeven, Integer multiplication in time O(n log n), Ann. of Math. 193 (2021), https://doi.org/10.4007/annals.2021.193.2.4 (preprint https://hal.science/hal-02070778v2), §2.3–2.4, pp. 11–13 (multidimensional DFT F_{n1,...,nd}).

import Mathlib

/-!
# Multidimensional complex DFTs of Harvey–van der Hoeven

D. Harvey, J. van der Hoeven, *Integer multiplication in time O(n log n)*,
Ann. of Math. 193 (2021), §2.3–§2.4.

An element of `⊗ᵢ ℂ^{nᵢ}` (`1 ≤ i ≤ d`) is a `d`-dimensional array, i.e. a function on the index
set `∏ᵢ ℤ/nᵢℤ`; as in §2.4, an index `jᵢ` is always read modulo `nᵢ`. Mathlib's norm on such
functions is the supremum norm `‖u‖ = max_j |u_j|` of §2.3, and the norm of a continuous linear
map is the operator norm of §2.6.
-/

namespace IntMul.HvdH

open Complex Real

/-- The index set `∏ᵢ ℤ/nᵢℤ` of a `d`-dimensional array of size `n₁ × ⋯ × n_d`. -/
abbrev TIdx {d : ℕ} (n : Fin d → ℕ) : Type := (i : Fin d) → ZMod (n i)

/-- The multidimensional complex DFT `𝓕_{n₁,…,n_d} = ⊗ᵢ 𝓕_{nᵢ}` (§2.4):
`(𝓕 u)_j = (n₁⋯n_d)⁻¹ ∑_k ∏ᵢ e^{-2πi jᵢkᵢ/nᵢ} u_k`. -/
noncomputable def dftN {d : ℕ} (n : Fin d → ℕ) [∀ i, NeZero (n i)] :
    (TIdx n → ℂ) →L[ℂ] (TIdx n → ℂ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (Matrix.of fun j k : TIdx n =>
    ∏ i, (1 / (n i : ℂ)) * exp (-2 * π * I * ((j i).val : ℂ) * ((k i).val : ℂ) / (n i : ℂ))))

end IntMul.HvdH


