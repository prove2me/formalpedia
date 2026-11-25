-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetSubMapConj
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetSubMapConj
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:14:09.908235+00:00
-- url     : https://prove2.me/theorems/0f916a35-626b-47d4-9fb9-74b929c8d246
-- title:
--   Det Sub Map Conj
-- statement:
--   Definitions and structural lemmas for Det Sub Map Conj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/DetSubMapConj.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LminorMapConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
def Dsg : Fin r → ℝ := fun a => sgn X.p0 (a : ℕ)
def Xd (z u : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  (mat (nmat X z) τ)⁻¹ * KapPf.Lin X τ u
def Yd (b : Frame X.Ψ r) (z u : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  (mat b τ)⁻¹ * Xd X z u τ * mat b τ
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf


