-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FinMuOfFiniteCovolume
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FinMuOfFiniteCovolume
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:49:26.955799+00:00
-- url     : https://prove2.me/theorems/a961e613-d38d-469a-a937-94c2c746abf6
-- title:
--   Fin Mu Of Finite Covolume
-- statement:
--   Definitions and structural lemmas for Fin Mu Of Finite Covolume, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FinMuOfFiniteCovolume.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
namespace GlobalTheory.FiniteCovolume
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
noncomputable def embGL {r : ℕ} (Ψ : Finset (E →+* ℂ)) : GL (Fin r) E →* (Ψ → GL (Fin r) ℂ) :=
  Pi.monoidHom fun τ : Ψ => Matrix.GeneralLinearGroup.map τ.1
def cellOver {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) : Set (Frame X.Ψ r) :=
  (fun p : V (nd X) × Frame X.Ψ r => rmul (cpt X x0 p.1) p.2) '' (FF ×ˢ Bor X.Ψ r)
end GlobalTheory.FiniteCovolume


