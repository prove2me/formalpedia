-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_LineMu
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_LineMu
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T08:33:41.185602+00:00
-- url     : https://prove2.me/theorems/42d42385-698c-5229-a6ac-29949fa33ed6
-- title:
--   Line Mu
-- statement:
--   Definitions and structural lemmas for Line Mu, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/LineMu.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Values
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Weights
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_lineHodge_aMu_944bad2d47be
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isUnitOn_one_762773d2e406

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexConjugate
variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])
variable {II hII}
section Frame
variable {z : (Σ _ : Unit, Fin 2) → ℂ} (d : MuFrameAt (lineHodge II hII) z)
abbrev fb : Fin 2 → Fin 2 → Ω := d.b ()
end Frame
section FrameLemmas
variable {c : Unit → Fin 2} {f : Ω} {b : Fin 2 → Fin 2 → Ω}
variable {z : (Σ _ : Unit, Fin 2) → ℂ}
end FrameLemmas
section Norm
variable {z : (Σ _ : Unit, Fin 2) → ℂ} (d : MuFrameAt (lineHodge II hII) z)
def stdFrameAt {z : (Σ _ : Unit, Fin 2) → ℂ} {i : Fin 2} (hi : z ⟨(), i⟩ ≠ 0) :
    MuFrameAt (lineHodge II hII) z where
  c _ := i
  f := 1
  inDom := inFrameDomain_line hi
  b _ := ⇑(Pi.basisFun Ω (Fin 2))
  adapted _ := ⟨isFrameOver_line i, (Pi.basisFun Ω (Fin 2)).span_eq, by
    show Submodule.span Ω (Set.range (⇑(Pi.basisFun Ω (Fin 2)) ∘ headIdx (show 1 ≤ 2 by decide))) = lineF
    have : Set.range (⇑(Pi.basisFun Ω (Fin 2)) ∘ headIdx (show 1 ≤ 2 by decide)) = {Pi.single 0 1} := by
      ext v
      simp only [Set.mem_range, Function.comp_apply, Set.mem_singleton_iff]
      constructor
      · rintro ⟨a, rfl⟩
        rw [Fin.fin_one_eq_zero a]
        simp [headIdx]
      · rintro rfl
        exact ⟨0, by simp [headIdx]⟩
    rw [this]
    rfl⟩
  u := 1
  unit := isUnitOn_one _ _ _
  eq := by
    show PiTensorProduct.tprod Ω (fun _ => quotWedge lineF (lineData II hII).j_le_N
      ⇑(Pi.basisFun Ω (Fin 2))) = _
    simp only [chartMono, lineHodge_aMu, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul, one_smul]
    rfl
end Norm
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line


