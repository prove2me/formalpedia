-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DecompA
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DecompA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:38:08.536518+00:00
-- url     : https://prove2.me/theorems/7cd6177b-28fd-49a9-a5db-56035724ff2e
-- title:
--   Decomp A
-- statement:
--   Definitions and structural lemmas for Decomp A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DecompA.lean

import Mathlib
import Definitions.Def_Lemmata_PowerApplication_PowApp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Finset
namespace ReciprocityTheory.ChartRestriction.DS
section
variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
def dc_cplxPts (B : Finset ℝ) : Finset ℂ := B.image (fun b : ℝ => (b : ℂ))
variable {T : Module.End ℂ Y} {S : Submodule ℂ Y} {B : Finset ℝ}
def dc_lagProj (T : Module.End ℂ Y) (B : Finset ℝ) (z : ℂ) : Module.End ℂ Y :=
  if z ∈ dc_cplxPts B then aeval T (Lagrange.basis (dc_cplxPts B) id z) else 0
end
end ReciprocityTheory.ChartRestriction.DS
end
noncomputable section
open Polynomial Finset
namespace ReciprocityTheory.ChartRestriction.DS
section
variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y] {T : Module.End ℂ Y} {S W : Submodule ℂ Y}
  {Q : Y →ₗ⋆[ℂ] Y →ₗ[ℂ] ℂ}
end
end ReciprocityTheory.ChartRestriction.DS
end


