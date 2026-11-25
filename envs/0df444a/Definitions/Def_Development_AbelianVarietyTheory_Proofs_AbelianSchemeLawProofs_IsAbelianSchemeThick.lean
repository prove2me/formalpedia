-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAbelianSchemeThick
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAbelianSchemeThick
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T14:10:22.910084+00:00
-- url     : https://prove2.me/theorems/c6be3dc2-74ad-4917-9eec-e4c8509c3ae1
-- title:
--   Is Abelian Scheme Thick
-- statement:
--   Definitions and structural lemmas for Is Abelian Scheme Thick, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAbelianSchemeThick.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_O__comp_24bcd133e28a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_div

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
namespace CoordToExt
section Refine
variable {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
def Refines (M : LB Y) (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Prop :=
  ∃ σ : M.ι → K → L.ι, (∀ i, M.U i ≤ LB.wchart L φ (σ i)) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i j : M.ι), r z ∈ M.U i → r z ∈ M.U j →
      gm r z (M.U i ⊓ M.U j) (M.g i j) = trF φ ε r z (σ i) (σ j)
theorem Refines.div {M M' : LB Y} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : Refines M L φ ε) (h' : Refines M' L φ' ε') :
    Refines (LB.div M M') L (Sum.elim φ φ') (Sum.elim ε fun k => - ε' k) := by
  obtain ⟨σ, le, hg⟩ := h
  obtain ⟨σ', le', hg'⟩ := h'
  refine ⟨fun p => Sum.elim (σ p.1) (σ' p.2), fun p y hy => Set.mem_iInter.2 ?_, fun Z r z p q hp hq => ?_⟩
  · rintro (k | k)
    exacts [Set.mem_iInter.1 (le _ hy.1) k, Set.mem_iInter.1 (le' _ hy.2) k]
  · refine (gm_div M' M r z p q ⟨hp, hq⟩).trans ?_
    rw [hg Z r z _ _ hp.1 hq.1, hg' Z r z _ _ hp.2 hq.2, trF, trF, trF, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
    rfl
end Refine
section Present
variable {S : Scheme.{0}}
end Present
section Data
variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ)
abbrev bundle (χ : D.X) : LB (thickObj R I e D.P.A).left :=
  LB.LinComb D.P.L (Y := (thickObj R I e D.P.A).left) (D.Oφ (D.prBe I e) χ) Oε
variable {I D e} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
theorem q_Oφ (χ : D.X) (k : Fin 4) : g.q.left ≫ D.Oφ (D.prBe I e) χ k = D.Oφ g.pG χ k :=
  WeightPf.Oφ_comp ((Over.map (thick R I e)).map g.q) (D.prBe I e) χ k
theorem mem_chart (χ : D.X) (a : Fin 4 → D.P.L.ι) (y : (thickObj R I e G).left)
    (hy : g.q.left y ∈ (bundle I D e χ).U a) : y ∈ LB.wchart D.P.L (D.Oφ g.pG χ) a :=
  Set.mem_iInter.2 fun k => (congrArg (fun f => f y ∈ D.P.L.U (a k)) (q_Oφ g χ k)).mp (Set.mem_iInter.1 hy k)
def coordUnit (χ : D.X) (a : (bundle I D e χ).ι) : Γ((thickObj R I e G).left, g.q.left ⁻¹ᵁ (bundle I D e χ).U a)ˣ :=
  res (fun y hy => mem_chart g χ a y hy) ((g.t χ).s a)
end Data
end CoordToExt
end GlobalTheory


