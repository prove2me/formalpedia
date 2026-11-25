-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ContinuousOnValue
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_ContinuousOnValue
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:19:07.455968+00:00
-- url     : https://prove2.me/theorems/add2e39e-a5b7-412c-a4ff-9624c2aed904
-- title:
--   Continuous On Value
-- statement:
--   Definitions and structural lemmas for Continuous On Value, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ContinuousOnValue.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsLocalHomeomorphAddMonoidHomOfEventuallyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
namespace GlobalTheory.AbelianExp
@[reducible] def pointTopology (X : Over (Sp ℂ)) : TopologicalSpace (𝟙_ (Over (Sp ℂ)) ⟶ X) :=
  TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ X) | ∃ (U : X.left.Opens)
    (f : Γ(X.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}}
attribute [local instance] pointTopology
def HolOn {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) {X : Over (Sp ℂ)}
    (a : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)) : Prop :=
  ∀ (U : X.left.Opens) (f : Γ(X.left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧
    DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}
section Hol
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
  [NormedSpace ℂ E'] {W : Set E} {X Y : Over (Sp ℂ)} {a : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)}
theorem isOpen_value (U : X.left.Opens) (f : Γ(X.left, U)) {O : Set ℂ} (hO : IsOpen O) :
    IsOpen {x : 𝟙_ (Over (Sp ℂ)) ⟶ X | ⊤ ≤ x.left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O} :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, f, O, hO, rfl⟩
theorem continuousOn_value (U : X.left.Opens) (f : Γ(X.left, U)) :
    ContinuousOn (fun x : 𝟙_ (Over (Sp ℂ)) ⟶ X => valAt' x.left U f) {x | ⊤ ≤ x.left ⁻¹ᵁ U} := by
  rw [continuousOn_iff]
  intro x hx t ht hxt
  exact ⟨_, isOpen_value U f ht, ⟨hx, hxt⟩, fun y hy => hy.1.2⟩
theorem HolOn.continuousAt (h : HolOn W a) {w : E} (hw : w ∈ W) : ContinuousAt a w := by
  unfold ContinuousAt
  refine TopologicalSpace.tendsto_nhds_generateFrom_iff.2 ?_
  rintro _ ⟨U, f, O, hO, rfl⟩ ⟨hU, hfO⟩
  have hN : {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∈ 𝓝 w := (h U f).1.mem_nhds ⟨hw, hU⟩
  have hc : ContinuousAt (fun w => valAt' (a w).left U f) w :=
    ((h U f).2.differentiableAt hN).continuousAt
  filter_upwards [hN, hc.preimage_mem_nhds (hO.mem_nhds hfO)] with z hz hz'
  exact ⟨hz.2, hz'⟩
noncomputable def chart {g : ℕ} {W : Set (Fin g → ℂ)} {σ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)}
    {U : X.left.Opens} (t : Fin g → Γ(X.left, U)) (hW : IsOpen W) (hσ : HolOn W σ)
    (ht : ∀ w ∈ W, ⊤ ≤ (σ w).left ⁻¹ᵁ U ∧ ∀ i, valAt' (σ w).left U (t i) = w i)
    (ho : IsOpen (σ '' W)) : OpenPartialHomeomorph (𝟙_ (Over (Sp ℂ)) ⟶ X) (Fin g → ℂ) where
  toFun x i := valAt' x.left U (t i)
  invFun := σ
  source := σ '' W
  target := W
  map_source' := by
    rintro _ ⟨w, hw, rfl⟩
    rwa [show (fun i => valAt' (σ w).left U (t i)) = w from funext (ht w hw).2]
  map_target' w hw := ⟨w, hw, rfl⟩
  left_inv' := by
    rintro _ ⟨w, hw, rfl⟩
    rw [show (fun i => valAt' (σ w).left U (t i)) = w from funext (ht w hw).2]
  right_inv' w hw := funext (ht w hw).2
  open_source := ho
  open_target := hW
  continuousOn_toFun := continuousOn_pi.mpr fun i => (continuousOn_value U (t i)).mono (by
    rintro _ ⟨w, hw, rfl⟩
    exact (ht w hw).1)
  continuousOn_invFun w hw := (hσ.continuousAt hw).continuousWithinAt
end Hol
end GlobalTheory.AbelianExp


