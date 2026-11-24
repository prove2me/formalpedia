-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_HaarDistr
-- name    : Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_HaarDistr
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:48.879013+00:00
-- url     : https://prove2.me/theorems/3407a926-04ea-408c-87bd-d27ae8c86bdf
-- title:
--   Haar Distr
-- statement:
--   Definitions and structural lemmas for Haar Distr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/FrobeniusReciprocity/HaarDistr.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_PowNear
import Theorems.Thm_GroundTheory_Automorphic_indicator_mem_locallyConstantCompactSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob GroundTheory.Automorphic
open scoped Pointwise
namespace PositivityTheory.RgUd.T2.HaarDistr
section Group
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
def mulLC (ψ : G → ℂ) (hψ : IsLocallyConstant ψ) : SB G →ₗ[ℂ] SB G where
  toFun α := ⟨fun x => ψ x * (α : G → ℂ) x,
    hψ.comp₂ α.2.1 (· * ·), HasCompactSupport.mul_left α.2.2⟩
  map_add' α β := by
    apply Subtype.ext; funext x
    show ψ x * ((α : G → ℂ) x + (β : G → ℂ) x) = ψ x * (α : G → ℂ) x + ψ x * (β : G → ℂ) x
    ring
  map_smul' c α := by
    apply Subtype.ext; funext x
    show ψ x * (c * (α : G → ℂ) x) = c * (ψ x * (α : G → ℂ) x)
    ring
def ind (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) : SB G :=
  ⟨(K : Set G).indicator (fun _ => (1 : ℂ)),
    indicator_mem_locallyConstantCompactSupport (R := ℂ) hK K.isOpen 1⟩
variable [MeasurableSpace G] [BorelSpace G]
def intLC (μ : Measure G) [μ.IsHaarMeasure] : SB G →ₗ[ℂ] ℂ where
  toFun α := ∫ x, (α : G → ℂ) x ∂μ
  map_add' α β := integral_add (α.2.1.continuous.integrable_of_hasCompactSupport α.2.2)
    (β.2.1.continuous.integrable_of_hasCompactSupport β.2.2)
  map_smul' c α := integral_const_mul c _
end Group
end PositivityTheory.RgUd.T2.HaarDistr


