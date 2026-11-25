-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T13:57:17.087029+00:00
-- url     : https://prove2.me/theorems/e39cfaed-9eee-5710-8dd4-836b55053df7
-- title:
--   Linear Independent Of Is Extension
-- statement:
--   Definitions and structural lemmas for Linear Independent Of Is Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/LinearIndependentOfIsExtension.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sec_ext__7d36e2669680
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sval_add__395e1a61c295
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sval_smul__9bcebbd1d3c5
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_pw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pw_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_trF_self

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
variable {X X' Y Y' Z : Scheme.{0}}
theorem exists_sec_transfer {A B : LB Y} (hB : ∀ y, ∃ q, y ∈ B.U q) (u : ∀ p q, Γ(Y, A.U p ⊓ B.U q)ˣ)
    (h₁ : ∀ (y : Y) p q q', y ∈ A.U p → y ∈ B.U q → y ∈ B.U q' →
      gm (𝟙 Y) y _ (u p q) * gm (𝟙 Y) y _ (B.g q q') = gm (𝟙 Y) y _ (u p q'))
    (h₂ : ∀ (y : Y) p p' q, y ∈ A.U p → y ∈ A.U p' → y ∈ B.U q →
      gm (𝟙 Y) y _ (u p q) = gm (𝟙 Y) y _ (A.g p p') * gm (𝟙 Y) y _ (u p' q)) (b : LB.Sec B) :
    ∃ a : LB.Sec A, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p q, r z ∈ A.U p → r z ∈ B.U q →
      gs r z _ (a.f p) = (gm r z _ (u p q)).val * gs r z _ (b.f q) := by
  have hb : ∀ (y : Y) q q', y ∈ B.U q → y ∈ B.U q' →
      gs (𝟙 Y) y _ (b.f q) = (gm (𝟙 Y) y _ (B.g q q')).val * gs (𝟙 Y) y _ (b.f q') := fun y q q' hq hq' => by
    have hm : (𝟙 Y : Y ⟶ Y) y ∈ B.U q ⊓ B.U q' := ⟨hq, hq'⟩
    exact (gs_res _ y _ hm _).symm.trans ((congrArg (gs _ y _) (b.compat q q')).trans ((gs_mul _ y _ hm _ _).trans
      (congrArg₂ (· * ·) (gs_unit _ y _ hm _) (gs_res _ y _ hm _))))
  have glue : ∀ p, ∃ s : Γ(Y, A.U p), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q, r z ∈ A.U p → r z ∈ B.U q →
      gs r z _ s = (gm r z _ (u p q)).val * gs r z _ (b.f q) := by
    intro p
    have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q, r z ∈ A.U p ⊓ B.U q →
        gs r z (A.U p ⊓ B.U q) ((u p q).val * (Y.presheaf.map (homOfLE inf_le_right).op).hom (b.f q)) =
          (gm r z _ (u p q)).val * gs r z _ (b.f q) := fun Z r z q hz =>
      (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) (gs_unit r z _ hz _) (gs_res r z _ hz _))
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun q => A.U p ⊓ B.U q) (A.U p)
      (fun q => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨q, hq⟩ := hB y
        exact Opens.mem_iSup.2 ⟨q, hy, hq⟩)
      (fun q => (u p q).val * (Y.presheaf.map (homOfLE inf_le_right).op).hom (b.f q))
      (fun q q' => fn_ext (V := (A.U p ⊓ B.U q) ⊓ (A.U p ⊓ B.U q')) fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        refine (hv _ (𝟙 Y) y q hy.1).trans (Eq.trans ?_ (hv _ (𝟙 Y) y q' hy.2).symm)
        rw [hb y q q' hy.1.2 hy.2.2, ← mul_assoc, ← Units.val_mul,
          h₁ y p q q' hy.1.1 hy.1.2 hy.2.2])
    refine ⟨s, fun Z r z q a₁ a₂ => ?_⟩
    have hz : r z ∈ A.U p ⊓ B.U q := ⟨a₁, a₂⟩
    exact (gs_res r z inf_le_left hz s).symm.trans ((congrArg (gs r z _) (hs q)).trans (hv Z r z q hz))
  choose s hs using glue
  refine ⟨⟨s, fun p p' => fn_ext fun y hy => ?_⟩, fun Z r z p q => hs p Z r z q⟩
  obtain ⟨q, hq⟩ := hB y
  refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
    (gs_unit (𝟙 Y) y _ hy _) (gs_res (𝟙 Y) y _ hy _))).symm)
  rw [hs p _ _ y q hy.1 hq, hs p' _ _ y q hy.2 hq, h₂ y p p' q hy.1 hy.2 hq, Units.val_mul, mul_assoc]
variable {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
theorem exists_wchart (hL : L.IsLB) (φ : K → (Y ⟶ X)) (y : Y) : ∃ j, y ∈ LB.wchart L φ j := by
  choose j hj using fun k => exists_chart hL (φ k y)
  exact ⟨j, Set.mem_iInter.2 hj⟩
theorem exists_good' (hL : L.IsLB) (z : Z) : ∃ J, Good L z J := by
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  exact ⟨I, hI⟩
theorem exists_sec_down {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')}
    {ε : K → ℤ} (t : LB.Sec (LB.LinComb L (fun k => φ' k ≫ F) ε)) : ∃ a : LB.Sec (LB.LinComb L' φ' ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι), r z ∈ LB.wchart L (fun k => φ' k ≫ F) p →
        r z ∈ LB.wchart L' φ' q → gs r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.f p) =
          (pw w φ' ε r z p q).val * gs r z (LB.wchart L' φ' q) (a.f q) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have hu' : ∀ q p (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ LB.wchart L' φ' q →
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p →
      gm r z (LB.wchart L' φ' q ⊓ LB.wchart L (fun k => φ' k ≫ F) p) (res (inf_comm _ _).le (u p q))⁻¹ =
        (pw w φ' ε r z p q)⁻¹ := fun q p Z r z hq hp =>
    (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res r z _ (show r z ∈ LB.wchart L' φ' q ⊓
      LB.wchart L (fun k => φ' k ≫ F) p from ⟨hq, hp⟩) _).trans (hu p q Z r z ⟨hp, hq⟩)))
  obtain ⟨a, ha⟩ := exists_sec_transfer (B := LB.LinComb L (fun k => φ' k ≫ F) ε) (A := LB.LinComb L' φ' ε)
    (exists_wchart hL _) (fun q p => (res (inf_comm _ _).le (u p q))⁻¹) (fun y q p p' hq hp hp' => by
      refine (congrArg₂ (· * ·) (hu' q p _ (𝟙 Y) y hq hp) (gm_linComb L _ ε (𝟙 Y) y p p' hp hp')).trans
        (Eq.trans ?_ (hu' q p' _ (𝟙 Y) y hq hp').symm)
      rw [pw_trans hw φ' ε (𝟙 Y) y hp hp' hq hq, trF_self hL' _ ε (𝟙 Y) y hq, inv_one, mul_one, mul_inv]
      exact inv_mul_cancel_comm _ _) (fun y q q' p hq hq' hp => by
      refine (hu' q p _ (𝟙 Y) y hq hp).trans (Eq.trans ?_ (congrArg₂ (· * ·)
        (gm_linComb L' _ ε (𝟙 Y) y q q' hq hq') (hu' q' p _ (𝟙 Y) y hq' hp)).symm)
      rw [pw_trans hw φ' ε (𝟙 Y) y hp hp hq hq', trF_self hL _ ε (𝟙 Y) y hp, one_mul, mul_inv, inv_inv]
      rfl) t
  refine ⟨a, fun Z r z p q hp hq => ?_⟩
  have e := (ha Z r z q p hq hp).trans
    (congrArg (fun v : (Z.presheaf.stalk z)ˣ => v.val * _) (hu' q p Z r z hq hp))
  exact ((Units.eq_inv_mul_iff_mul_eq _).1 e).symm
def SecThrough (w : LB.Iso L' (L.pull F)) (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Sec (LB.LinComb L' φ' ε)) (t : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι), (∀ k, F (φ' k (r z)) ∈ L.U (p k)) →
    (∀ k, φ' k (r z) ∈ L'.U (q k)) →
    gs (r ≫ h) z (LB.wchart L φ p) (t.f p) =
      (∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k).val * gs r z (LB.wchart L' φ' q) (a.f q)
def wVal (w : LB.Iso L' (L.pull F)) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) (ψ : Z ⟶ X') :
    (Z.presheaf.stalk z)ˣ := gw w ψ z (J (ψ ≫ F)) (J' ψ)
variable {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
theorem SecThrough.sval (hψ : ∀ k, φ' k ≫ F = h ≫ φ k) {a : LB.Sec (LB.LinComb L' φ' ε)}
    {t : LB.Sec (LB.LinComb L φ ε)} (H : SecThrough w φ' φ ε a t h) (r : Z ⟶ Y') {z : Z} {J J'} (hJ : Good L z J)
    (hJ' : Good L' z J') : sval t (r ≫ h) z J = (∏ k, wVal w z J J' (r ≫ φ' k) ^ ε k).val * sval a r z J' := by
  rw [sval_of t (r ≫ h) z J (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => by rw [Category.assoc, Category.assoc, hψ])]
  exact H Z r z _ _ (fun k => hJ ((r ≫ φ' k) ≫ F)) (fun k => hJ' (r ≫ φ' k))
theorem exists_secThrough (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k)
    (t : LB.Sec (LB.LinComb L φ ε)) : ∃ a, SecThrough w φ' φ ε a t h := by
  have e : (fun k => φ' k ≫ F) = fun k => h ≫ φ k := funext hψ
  have ex : ∃ t' : LB.Sec (LB.LinComb L (fun k => φ' k ≫ F) ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) p,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → gs r z (LB.wchart L (fun k => φ' k ≫ F) p) (t'.f p) =
        gs (r ≫ h) z (LB.wchart L φ p) (t.f p) := by
    rw [e]
    exact ⟨ReciprocityTheory.ChartRestriction.G.DVR.pullSec L φ ε t h, fun Z r z p hp => (gs_res r z _ hp _).trans
      (gs_pull r h z _ (Out.wchart_comp_le L φ h p hp) _)⟩
  obtain ⟨t', ht'⟩ := ex
  obtain ⟨a, ha⟩ := exists_sec_down ((isGen_iff w).1 hw) hL hL' t'
  exact ⟨a, fun Z r z p q hp hq => (ht' Z r z p (Set.mem_iInter.2 hp)).symm.trans
    (ha Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq))⟩
section Linear
variable {R R' : Type} [CommRing R] [CommRing R'] {π : Y ⟶ Spec (CommRingCat.of R)}
  {π' : Y' ⟶ Spec (CommRingCat.of R')} {f : R →+* R'}
def pullThrough (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k) (ε : K → ℤ)
    (hp : h ≫ π = π' ≫ Spec.map (CommRingCat.ofHom f)) :
    SecOver π (LB.LinComb L φ ε) →ₛₗ[f] SecOver π' (LB.LinComb L' φ' ε) where
  toFun t := (exists_secThrough hw hL hL' hψ t).choose
  map_add' s t := sec_ext' hL' fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good' hL y
    refine (Units.mul_right_inj (∏ k, wVal w y J J' (𝟙 Y' ≫ φ' k) ^ ε k)).1 ?_
    refine ((exists_secThrough hw hL hL' hψ _).choose_spec.sval hψ _ hJ hJ').symm.trans ((sval_add' hJ _ s t).trans
      (Eq.trans ?_ (congrArg _ (sval_add' (π := π') hJ' _ _ _).symm)))
    rw [mul_add, ← (exists_secThrough hw hL hL' hψ s).choose_spec.sval hψ _ hJ hJ',
      ← (exists_secThrough hw hL hL' hψ t).choose_spec.sval hψ _ hJ hJ']
  map_smul' c s := sec_ext' hL' fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good' hL y
    refine (Units.mul_right_inj (∏ k, wVal w y J J' (𝟙 Y' ≫ φ' k) ^ ε k)).1 ?_
    refine ((exists_secThrough hw hL hL' hψ _).choose_spec.sval hψ _ hJ hJ').symm.trans ((sval_smul' hJ _ c s).trans
      (Eq.trans ?_ (congrArg _ (sval_smul' (π := π') hJ' _ _ _).symm)))
    rw [mul_left_comm, ← (exists_secThrough hw hL hL' hψ s).choose_spec.sval hψ _ hJ hJ', Category.assoc, hp,
      ← Category.assoc, constVal_specMap]
variable (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k)
  (hp : h ≫ π = π' ≫ Spec.map (CommRingCat.ofHom f))
end Linear
end GlobalTheory.ConstFam


