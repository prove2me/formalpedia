-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Multilinear
-- name    : KLSModular_FunctionalInequalities_Analysis_Tensor_Multilinear
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:19:16.338261+00:00
-- url     : https://prove2.me/theorems/95acd8c3-b570-4032-a49b-c00dac41b021
-- title:
--   Multilinear symmetrization and appended inner products
-- statement:
--   For a continuous $q$-linear map $\Phi$ from copies of a real inner-product space $E$ to a real normed space $F$, `symmetrizeML Φ` is the average of $\Phi(h\circ\sigma)$ over all permutations of the $q$ arguments, normalized by $(q!)^{-1}$. For a continuous $d$-linear map `Ψ` with values in $E$, `appendInner Ψ` is the continuous $(d+1)$-linear real-valued map obtained by pairing the first $d$-argument output with a final vector through the inner product.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.InnerProductSpace.LinearMap
--   import Mathlib.Analysis.Normed.Module.Multilinear.Curry
--   import Mathlib.Data.Fintype.Perm
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def symmetrizeML {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {q : ℕ}
--       (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) F) :
--       ContinuousMultilinearMap ℝ (fun _ : Fin q => E) F :=
--     ((q.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin q), Φ.domDomCongr σ
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`card_filter_perm_apply_last_eq`](https://prove2.me/theorems/2514fc9f-d962-4adc-9af7-2d50a1e76cfe)
--   - [`exists_perm_init_comp_eq`](https://prove2.me/theorems/85188848-2290-4444-9fa3-ed04c8253b48)
--   - [`sum_perm_inner_init_last`](https://prove2.me/theorems/21685786-ff33-430e-9d2e-110686ae2c53)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/Multilinear.lean) · `FunctionalInequalities.Analysis.Tensor.Multilinear` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Multilinear.lean#L24-L36 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Multilinear`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Tensor_Multilinear`; the repository is private at upload time).

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Data.Fintype.Perm

noncomputable section
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace Analysis
namespace Tensor
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The symmetrization `S_q` of a `q`-linear map with values in a real normed space: the average of
`Φ (h ∘ σ)` over all permutations `σ` of the `q` arguments (BKL Section 2; for a tensor-valued map
the values carry the trailing indices, which are not permuted). -/
def symmetrizeML {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {q : ℕ}
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) F) :
    ContinuousMultilinearMap ℝ (fun _ : Fin q => E) F :=
  ((q.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin q), Φ.domDomCongr σ
/-- For a tensor `Ψ` with `d` Taylor indices and one original vector index (BKL places the Taylor
indices first), the real `(d+1)`-linear map `h ↦ ⟪Ψ (h₀, …, h_{d-1}), h_d⟫`. -/
def appendInner {d : ℕ} (Ψ : ContinuousMultilinearMap ℝ (fun _ : Fin d => E) E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (d + 1) => E) ℝ :=
  ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).compContinuousMultilinearMap Ψ).uncurryRight
end Tensor
end Analysis
end FunctionalInequalities


