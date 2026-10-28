-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization
-- name    : KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:19:04.418455+00:00
-- url     : https://prove2.me/theorems/8547f114-355c-49be-8989-b3003d84814f
-- title:
--   Permutation averages on selected tensor positions
-- statement:
--   For a finite index type $\Omega$, `fixingOutside s` is the finite set of permutations that fix every point outside a finite subset $s$. Given a monoid representation `ρ` of permutations by linear isometric equivalences of an inner-product space, `blockAverage ρ s v` is the normalized average of `ρ σ v` over those permutations, using the real inverse of the cardinality. This bundle contains definitions only and asserts no norm estimate.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.InnerProductSpace.Basic
--   import Mathlib.Analysis.Normed.Operator.LinearIsometry
--   import Mathlib.Data.Nat.Choose.Central
--   import Mathlib.Data.Nat.Choose.Vandermonde
--   import Mathlib.GroupTheory.Perm.Basic
--   import Mathlib.Data.Fintype.Perm
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def fixingOutside (s : Finset Ω) : Finset (Equiv.Perm Ω) :=
--     univ.filter fun σ => ∀ x, x ∉ s → σ x = x
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`card_filter_union_subset`](https://prove2.me/theorems/cf9f5ea2-af4b-45a0-8c9a-cc4df00e06e9)
--   - [`sum_choose_mul_card_filter_subset`](https://prove2.me/theorems/bdbd40ac-1a0c-4040-b7c6-4891fcad5583)
--   - [`sum_norm_sq_sum_filter`](https://prove2.me/theorems/f152e5e8-eec5-438e-bbf0-9dca6ce16fe8)
--   - [`sum_norm_sq_sum_subset_eq`](https://prove2.me/theorems/3f94b763-454c-46a7-862d-4d84329a2ef7)
--   - [`sum_norm_sq_le_sum_norm_sq_sum_subset`](https://prove2.me/theorems/2747bdb8-2573-4a48-9d87-e05edbda390e)
--   - [`exists_mem_fixingOutside_image_eq`](https://prove2.me/theorems/14b5df8e-d013-4b01-a20c-a437a2621fc7)
--   - [`apply_eq_of_image_eq`](https://prove2.me/theorems/d208003e-b651-43c5-a3e4-e5c080e8a606)
--   - [`image_mem_powersetCard_of_mem_fixingOutside`](https://prove2.me/theorems/7bccdbf5-5ef4-4af0-ab13-ffd9fefe2d80)
--   - [`card_fiber_eq`](https://prove2.me/theorems/a6caecd1-c605-4b2f-84a7-1d2e29ee0b3f)
--   - [`sum_fixingOutside_eq_smul_sum`](https://prove2.me/theorems/18cb6a82-9aad-4b06-823d-b31d65e6a497)
--   - [`sum_powersetCard_image_eq`](https://prove2.me/theorems/028b041a-5881-4253-b32d-c4e28e699c0f)
--   - [`norm_le_choose_mul_norm_blockAverage`](https://prove2.me/theorems/ce21f420-f15e-4872-8c85-4a342b34288d)
--   - [`norm_le_four_pow_mul_norm_blockAverage`](https://prove2.me/theorems/9105d9b3-66ee-4045-906c-b84556304fa1)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean) · `FunctionalInequalities.Analysis.Tensor.Symmetrization` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L33-L42 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization`; the repository is private at upload time).

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm

noncomputable section
open Finset
namespace FunctionalInequalities
namespace Analysis
namespace Tensor
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
/-- The permutations of `Ω` fixing every point outside `s`. -/
def fixingOutside (s : Finset Ω) : Finset (Equiv.Perm Ω) :=
  univ.filter fun σ => ∀ x, x ∉ s → σ x = x
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
/-- The average of `ρ σ v` over the permutations fixing every point outside `s` (the operator
`S_q` of the source when `s` is the set of the first `q` positions). -/
def blockAverage (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V)) (s : Finset Ω) (v : V) : V :=
  ((fixingOutside s).card : ℝ)⁻¹ • ∑ σ ∈ fixingOutside s, ρ σ v
end Tensor
end Analysis
end FunctionalInequalities


