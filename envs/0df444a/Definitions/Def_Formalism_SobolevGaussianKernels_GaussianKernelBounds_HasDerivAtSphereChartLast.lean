-- Prove2me | Definitions.Def_Formalism_SobolevGaussianKernels_GaussianKernelBounds_HasDerivAtSphereChartLast
-- name    : Formalism_SobolevGaussianKernels_GaussianKernelBounds_HasDerivAtSphereChartLast
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:45:55.360345+00:00
-- url     : https://prove2.me/theorems/5a1c6bf0-9b47-42f0-a13f-02eef7712f3c
-- title:
--   Has Deriv At Sphere Chart Last
-- statement:
--   Definitions and structural lemmas for Has Deriv At Sphere Chart Last, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SobolevGaussianKernels/GaussianKernelBounds/HasDerivAtSphereChartLast.lean

import Mathlib
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementSB
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementLF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.SL.P
open MeasureTheory Formalism.SL.SB
open scoped ContDiff
namespace SphereChartDerivatives
variable {n : ℕ}
def sn (t : ℝ) (y : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) y t
noncomputable def snocL (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi (fun j => if h : j = Fin.last n then 0
    else ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) (j.castPred h))
noncomputable def SS {m : ℕ} (δ : ℝ) (g : (Fin m → ℝ) → ℂ) (y : Fin m → ℝ) : ℝ :=
  ∑ α : Finset (Fin m), δ ^ (2 * α.card) * ‖mixed α g y‖ ^ 2
end SphereChartDerivatives
end Formalism.SL.P


