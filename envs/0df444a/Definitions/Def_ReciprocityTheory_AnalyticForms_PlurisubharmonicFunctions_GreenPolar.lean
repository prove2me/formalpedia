-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar
-- name    : ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:02.629967+00:00
-- url     : https://prove2.me/theorems/47a77427-02a9-4770-b047-06b3f537d88b
-- title:
--   Green Polar
-- statement:
--   Definitions and structural lemmas for Green Polar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Filter Topology InnerProductSpace intervalIntegral
open scoped Laplacian
namespace ReciprocityTheory.AnForm.A.GreenFunction
noncomputable section
def ee (θ : ℝ) : ℂ := Real.cos θ + Real.sin θ * Complex.I
section calc1
variable {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (a : ℂ)
include hu
end calc1
def Arad (u : ℂ → ℝ) (a : ℂ) (θ r : ℝ) : ℝ :=
  Real.log r * (r * fderiv ℝ (fderiv ℝ u) (a + r • ee θ) (ee θ) (ee θ)
    + fderiv ℝ u (a + r • ee θ) (ee θ))
def AngularPart (u : ℂ → ℝ) (a : ℂ) (r θ : ℝ) : ℝ :=
  Real.log r * (r * fderiv ℝ (fderiv ℝ u) (a + r • ee θ) (Complex.I * ee θ) (Complex.I * ee θ)
    - fderiv ℝ u (a + r • ee θ) (ee θ))
end
end ReciprocityTheory.AnForm.A.GreenFunction


