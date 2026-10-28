-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Derivatives
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Derivatives
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:11:31.785997+00:00
-- url     : https://prove2.me/theorems/3fa39843-9f8d-446f-806f-25b47f8ada2b
-- title:
--   Spatial slice of the suspension space
-- statement:
--   For natural numbers $N,n$, `jointSpatialSlice N n` is the continuous linear map from $(\mathbb{R}^n)^N$ into the suspension `JointSpace N n` that sends the auxiliary coordinate to $0$ and sends the $(i,j)$ spatial coordinate to the $j$th coordinate of the $i$th copy. The simp theorems `jointSpatialSlice_none` and `jointSpatialSlice_some` state these two coordinate formulas exactly; the module also contains derivative and cumulant auxiliary results for the suspension construction.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.Suspension.Density
--   import FunctionalInequalities.KLS.BKL.Suspension.Cumulant
--   import FunctionalInequalities.KLS.LogConcave.Regular.Basic
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   private noncomputable def jointSpatialSlice (N n : ℕ) :
--       (Fin N → EuclideanSpace ℝ (Fin n)) →L[ℝ]
--         FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n :=
--     (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin N × Fin n) => ℝ)).symm.toContinuousLinearMap.comp
--       (ContinuousLinearMap.pi fun o => match o with
--         | none => 0
--         | some ij => (EuclideanSpace.proj ij.2).comp (ContinuousLinearMap.proj ij.1))
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/Suspension/Density`](https://prove2.me/theorems/34f067f9-b370-4131-a2be-776da314cea2), [`KLS/BKL/Suspension/Cumulant`](https://prove2.me/theorems/01ff1334-f332-41dc-ab58-0fb2ead9dd7b), [`KLS/LogConcave/Regular/Basic`](https://prove2.me/theorems/2380e904-df18-4ce0-91da-7cc8a4c0e342).
--
--   Theorems in source order:
--
--   - [`graph_log_integral_hasDerivAt_zero`](https://prove2.me/theorems/33019b04-662c-4c4b-b629-8d98f5f8344d)
--   - [`joint_first_derivative_of_radii`](https://prove2.me/theorems/36ffa587-610d-4253-bdcc-464589c23e0b)
--   - [`fderiv_logLaplace_jointLaw_none`](https://prove2.me/theorems/c111409b-45db-45b0-903a-b9f1a6b86e12)
--   - [`source_mixed_cumulant_entries`](https://prove2.me/theorems/64ef58a4-ed4b-40d5-9f37-7e5aad5551d2)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Derivatives.lean) · `FunctionalInequalities.KLS.BKL.Suspension.Derivatives` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Derivatives.lean#L675-L688 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Derivatives`, definition bundle `KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Derivatives`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Density
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Cumulant
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Basic

open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Line
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
namespace Suspension
open FunctionalInequalities.KLS.LogConcave.Suspension
open scoped Topology ContDiff
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.KLS.LogConcave.Suspension
open scoped Topology
open FunctionalInequalities
open scoped ContDiff
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
set_option autoImplicit false
open Filter Set
open scoped ContDiff Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
open scoped ContDiff Topology
open Filter Set
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
/-- Actual spatial slice in the source's joint space: auxiliary coordinate zero, copies intact. -/
 noncomputable def jointSpatialSlice (N n : ℕ) :
    (Fin N → EuclideanSpace ℝ (Fin n)) →L[ℝ]
      FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin N × Fin n) => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun o => match o with
      | none => 0
      | some ij => (EuclideanSpace.proj ij.2).comp (ContinuousLinearMap.proj ij.1))
@[simp] theorem jointSpatialSlice_none {N n : ℕ} (x : Fin N → EuclideanSpace ℝ (Fin n)) :
    FunctionalInequalities.KLS.LogConcave.Suspension.jointSpatialSlice N n x none = 0 := rfl
@[simp] theorem jointSpatialSlice_some {N n : ℕ} (x : Fin N → EuclideanSpace ℝ (Fin n))
    (i : Fin N) (j : Fin n) : FunctionalInequalities.KLS.LogConcave.Suspension.jointSpatialSlice N n x (some (i, j)) = x i j := rfl
open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.KLS.LogConcave.Suspension
open scoped RealInnerProductSpace ContDiff Topology
open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.KLS.LogConcave.Suspension
end Suspension
end LogConcave
end KLS
end FunctionalInequalities


