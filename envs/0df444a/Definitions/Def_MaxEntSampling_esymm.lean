-- Prove2me | Definitions.Def_MaxEntSampling_esymm
-- name    : MaxEntSampling_esymm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:26.333759+00:00
-- url     : https://prove2.me/theorems/9d320e45-abb7-4471-8625-5ec09e13a96d
-- title:
--   Elementary symmetric polynomial $E_\ell(x)$ (Definition 3)
-- statement:
--   For $x\in\mathbb R^n$ and an integer $\ell$, the **elementary symmetric polynomial** of degree $\ell$ is
--
--   $$
--   E_\ell(x) := \sum_{S\in\binom{[n]}{\ell}}\prod_{i\in S}x_i .
--   $$
--
--   $E_s(\hat x)$ is the normalizing constant of the sampling law (13).
--
--   **Formalization Note** $\prod_{i\in S}x_i$ is `PropVolSampling.Reduction.xPow x S`. The definition is total in $\ell$ ($E_0=1$, $E_\ell=0$ for $\ell>n$); the paper uses $\ell\in[n]$.
-- source:
--   Li, Xie, Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem, arXiv:2001.08537v3, Definition 3, p.17 (PDF p.17)

import Mathlib
import Definitions.Def_PropVolSampling_Reduction_Model

open Finset

namespace MaxEntSampling

open PropVolSampling.Reduction

/-- **The elementary symmetric polynomial `E_ℓ(x)` (Definition 3).**
Li, Xie, *Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem*,
arXiv:2001.08537v3, Definition 3, p.17 (PDF p.17): "For any vector x ∈ R^n and a positive integer
ℓ ∈ [n], we define the elementary symmetric polynomial of degree ℓ as
Eℓ(x) := Σ_{S∈C([n],ℓ)} ∏_{i∈S} xi."

**Formalization Note.** `∏_{i∈S} x_i` is `PropVolSampling.Reduction.xPow x S`; the sum is over the
size-`ℓ` subsets of `Fin n` (`powersetCard`). The definition is total in `ℓ`
(`E_0 = 1`, `E_ℓ = 0` for `ℓ > n`); the paper uses `ℓ ∈ [n]`. -/
noncomputable def esymm {n : ℕ} (ℓ : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ S ∈ (univ : Finset (Fin n)).powersetCard ℓ, xPow x S

end MaxEntSampling


