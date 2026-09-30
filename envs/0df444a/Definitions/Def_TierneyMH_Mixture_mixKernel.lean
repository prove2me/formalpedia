-- Prove2me | Definitions.Def_TierneyMH_Mixture_mixKernel
-- name    : TierneyMH_Mixture_mixKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T02:28:48.125228+00:00
-- url     : https://prove2.me/theorems/a144cb02-e40e-4879-9133-f2fe97b367a5
-- title:
--   Mixture $\sum_i \beta_i K_i$ of a countable family of kernels
-- statement:
--   Let $(K_i)_{i\in I}$ be a finite or countably infinite family of transition kernels on $E$ and let $\beta_i\ge0$ be weights. The **mixture** $\sum_i\beta_iK_i$ is the kernel
--
--   $$\Bigl(\sum_i\beta_iK_i\Bigr)(x,A) = \sum_i \beta_i\,K_i(x,A),\qquad x\in E,\ A\in\mathcal E .$$
--
--   When $\sum_i\beta_i=1$ and each $K_i$ is a Markov kernel, the mixture is the kernel that first picks the index $i$ with probability $\beta_i$ and then moves according to $K_i$. In §4 of the paper it is used twice: to form the mixture proposal $Q=\sum_i\beta_iQ_i$ and the mixture $\sum_i\beta_iP_i$ of Metropolis–Hastings kernels.
--
--   **Formalization Note** The weights are nonnegative reals (`ℝ≥0`), so $\beta_i\ge0$ is built in; the theorems add $\sum_i\beta_i=1$. The index type is countable ("a sequence"), which includes finite families. The mixture is Mathlib's countable sum of kernels `Kernel.sum` of the kernels $K_i$ reweighted by the constant density $\beta_i$. The file also records that a mixture of s-finite kernels is s-finite.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, pp. 7–8, §4 (mixtures Q = Σβ_iQ_i and Σβ_iP_i)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace TierneyMH.Mixture

/-- The **mixture** `∑ᵢ βᵢ Kᵢ` of a countable family of kernels `Kᵢ` with nonnegative weights
`βᵢ` (Tierney 1998, §4, pp. 7–8): `(∑ᵢ βᵢ Kᵢ)(x, A) = ∑ᵢ βᵢ Kᵢ(x, A)`. It is formed as the
countable kernel sum of the kernels `Kᵢ` scaled by the constant density `βᵢ`. The weights are
taken in `ℝ≥0`, so `βᵢ ≥ 0` is built in; the theorems add `∑ᵢ βᵢ = 1`. -/
noncomputable def mixKernel {E : Type*} [MeasurableSpace E] {ι : Type*} [Countable ι]
    (β : ι → ℝ≥0) (K : ι → Kernel E E) [∀ i, IsSFiniteKernel (K i)] : Kernel E E :=
  Kernel.sum fun i => (K i).withDensity fun _ _ => (β i : ℝ≥0∞)

/-- A mixture of s-finite kernels is s-finite (structural instance). -/
instance isSFiniteKernel_mixKernel {E : Type*} [MeasurableSpace E] {ι : Type*} [Countable ι]
    (β : ι → ℝ≥0) (K : ι → Kernel E E) [∀ i, IsSFiniteKernel (K i)] :
    IsSFiniteKernel (mixKernel β K) := by
  unfold mixKernel
  have : ∀ i, IsSFiniteKernel ((K i).withDensity fun _ _ => (β i : ℝ≥0∞)) := fun i =>
    Kernel.IsSFiniteKernel.withDensity (K i) fun _ _ => ENNReal.coe_ne_top
  infer_instance

end TierneyMH.Mixture


