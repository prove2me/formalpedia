-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantCosetInd
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantCosetInd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:13.387363+00:00
-- url     : https://prove2.me/theorems/f572fcf0-d4e6-4be4-ba0f-cf8637f06549
-- title:
--   Is Locally Constant Coset Ind
-- statement:
--   Definitions and structural lemmas for Is Locally Constant Coset Ind, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantCosetInd.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace
noncomputable section
namespace GlobalTheory.InvBilinTest
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
open Classical in

def cosetInd (K : Subgroup G) (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) (g : G) :
    SB G :=
  ⟨fun x => if x * g⁻¹ ∈ K then 1 else 0, by
    constructor
    · have h1 : IsOpen {x : G | x * g⁻¹ ∈ K} := ho.preimage (continuous_id.mul continuous_const)
      have h2 : IsClosed {x : G | x * g⁻¹ ∈ K} :=
        (K.isClosed_of_isOpen ho).preimage (continuous_id.mul continuous_const)
      rw [IsLocallyConstant.iff_exists_open]
      intro y
      by_cases hy : y * g⁻¹ ∈ K
      · exact ⟨_, h1, hy, fun x hx => by rw [if_pos hy]; exact if_pos hx⟩
      · exact ⟨_, h2.isOpen_compl, hy, fun x hx => by rw [if_neg hy]; exact if_neg hx⟩
    · refine HasCompactSupport.intro (hK.image (continuous_id.mul (continuous_const (y := g))))
        fun x hx => if_neg fun h => hx ⟨_, h, by simp⟩⟩
variable [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
  {Y : Type} [AddCommGroup Y] [Module ℂ Y]
end GlobalTheory.InvBilinTest


