-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsFinsetRepresentatives
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsFinsetRepresentatives
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T14:24:48.150989+00:00
-- url     : https://prove2.me/theorems/50d43983-b474-5f1d-8d16-923f6c68b7a4
-- title:
--   Exists Finset Representatives
-- statement:
--   Definitions and structural lemmas for Exists Finset Representatives, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsFinsetRepresentatives.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Theorems.Thm_GlobalTheory_FieldBaseChange_sval_pullOver
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sec_ext__7d36e2669680
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sval_add__395e1a61c295
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sval_smul__9bcebbd1d3c5
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_fe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_secRel_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_pullMulSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
section Shift
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
def famBase : (DegPre.BF D F).left ⟶ Spec (CommRingCat.of F) := (fst (TF (R := R) F) D.P.A).left
abbrev FamTerm (k : ℕ) (α : D.X) : Type :=
  SecOver (famBase D F) (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))
def famProj (k : ℕ) (α : D.X) : Fam D F k →ₗ[F] FamTerm D F k α where
  toFun s := s.s α
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def shiftVal (k : ℕ) (mu α : D.X) {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ DegPre.BF D F) (z : T.left)
    (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) : (T.left.presheaf.stalk z)ˣ :=
  uVal D F k α (cP D _ mu) ρ z J * val (DegPre.famMult D F k mu α) (ρ ≫ fst _ _).left z J
def IsShift (k : ℕ) (mu α : D.X) (Θ : FamTerm D F k α →ₗ[F] FamTerm D F k (α + k • mu)) : Prop :=
  ∀ (s : FamTerm D F k α) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J),
    Good D.P.L z J → sval (Θ s) ρ.left z J =
      sval s (ρ.left ≫ (DegPre.trF D F mu).left) z J * (shiftVal D F k mu α ρ z J).val
theorem trF_famBase (mu : D.X) : (DegPre.trF D F mu).left ≫ famBase D F = famBase D F :=
  congrArg (fun q => q.left) (lift_fst _ _ : DegPre.trF D F mu ≫ fst _ _ = _)
theorem exists_isShift (hG : GlobalFnsSt) (k : ℕ) (mu α : D.X) : ∃ Θ, IsShift D F k mu α Θ := by
  have hL := D.P.isLB
  obtain ⟨⟨v, hv, hc⟩, hu⟩ := gen_fe (D := D) (F := F) hG k mu α
  have tr : ∀ σ : FamTerm D F k α, ∃ t : FamTerm D F k (α + k • mu),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
        sval t r z J = sval σ (r ≫ (DegPre.trF D F mu).left) z J * (val v r z J).val := fun σ => by
    obtain ⟨t, ht⟩ := exists_sec hL (fun U _ h => by
        rw [Fintype.prod_sum_type]
        simp only [DegPre.deltaφ, DegPre.deltaε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg,
          Finset.prod_inv_distrib]
        try (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel))
      (φ' := DegPre.famφ D F (α + k • mu)) (ε' := DegPre.famε k) (pullMulSec σ (DegPre.trF D F mu).left v hv)
    exact ⟨t, fun Z r z J hJ => (ht Z r z J hJ).trans (sval_pullMulSec _ _ _ hv r z hJ)⟩
  choose t ht using tr
  refine ⟨{ toFun := t
            map_add' := fun a b => sec_ext' hL fun y J hJ => ?_
            map_smul' := fun c a => sec_ext' hL fun y J hJ => ?_ }, fun s T ρ z J hJ => ?_⟩
  · rw [sval_add' hJ, ht _ _ _ y J hJ, ht _ _ _ y J hJ, ht _ _ _ y J hJ, sval_add' hJ, add_mul]
  · rw [sval_smul' hJ, ht _ _ _ y J hJ, ht _ _ _ y J hJ, sval_smul' hJ, Category.assoc, trF_famBase,
      _root_.mul_assoc]
    rfl
  · exact (ht s _ _ z J hJ).trans (congrArg (fun u : (T.left.presheaf.stalk z)ˣ => _ * u.val)
      (hu v hv hc T ρ z J hJ))
variable {D F}
theorem famFE_iff (hG : GlobalFnsSt) {k : ℕ}
    {Θ : ∀ mu α, FamTerm D F k α →ₗ[F] FamTerm D F k (α + k • mu)} (hΘ : ∀ mu α, IsShift D F k mu α (Θ mu α))
    (s : ∀ α, FamTerm D F k α) : DegPre.FamFE D F k s ↔ ∀ mu α, s (α + k • mu) = Θ mu α (s α) := by
  have hL := D.P.isLB
  constructor
  · intro H mu α
    obtain ⟨⟨v, hv, hc⟩, hu⟩ := gen_fe (D := D) (F := F) hG k mu α
    refine sec_ext' hL fun y J hJ => ?_
    refine ((secRel_iff hL _ _ _ _ _ _ _ _ _ v).1 (H mu α v hv hc) _ (𝟙 _) y J hJ).trans ?_
    exact (congrArg (fun u : ((DegPre.BF D F).left.presheaf.stalk y)ˣ => _ * u.val)
      (hu v hv hc _ (𝟙 _) y J hJ)).trans (hΘ mu α (s α) _ (𝟙 _) y J hJ).symm
  · intro H mu α u hu hc
    refine (secRel_iff hL _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
    refine (congrArg (fun t => sval t (𝟙 _) y J) (H mu α)).trans ((hΘ mu α (s α) _ (𝟙 _) y J hJ).trans ?_)
    exact (congrArg (fun u : ((DegPre.BF D F).left.presheaf.stalk y)ˣ => _ * u.val)
      ((gen_fe (D := D) (F := F) hG k mu α).2 u hu hc _ (𝟙 _) y J hJ)).symm
end Shift
section Pull
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (E F : Type) [Field F] [Algebra (FractionRing R) F]
  [Field E] [Algebra (FractionRing R) E] [Algebra E F]
  [IsScalarTower (FractionRing R) E F]
theorem specMap_jFK : Spec.map (CommRingCat.ofHom (algebraMap E F)) ≫ jFK (R := R) E = jFK (R := R) F := by
  rw [jFK, jFK, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
def baseMap : TF (R := R) F ⟶ TF (R := R) E :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap E F))) (by
    show Spec.map (CommRingCat.ofHom (algebraMap E F)) ≫ jFK (R := R) E ≫ jK R = jFK (R := R) F ≫ jK R
    rw [← Category.assoc, specMap_jFK])
def famMap : DegPre.BF D F ⟶ DegPre.BF D E := lift (fst _ _ ≫ baseMap (R := R) E F) (snd _ _)
theorem famMap_fst : famMap D E F ≫ fst _ _ = fst _ _ ≫ baseMap (R := R) E F := lift_fst _ _
theorem famMap_snd : famMap D E F ≫ DegPre.prB D _ = DegPre.prB D F := lift_snd _ _
theorem isPullback_famMap : IsPullback (famMap D E F).left (famBase D F) (famBase D E)
    (Spec.map (CommRingCat.ofHom (algebraMap E F))) := by
  have h₁ : IsPullback (snd (TF (R := R) E) D.P.A).left (famBase D E)
      D.P.A.hom (TF (R := R) E).hom := (IsPullback.of_hasPullback _ _).flip
  have h₂ : IsPullback (snd (TF (R := R) F) D.P.A).left (famBase D F)
      D.P.A.hom (TF (R := R) F).hom := (IsPullback.of_hasPullback _ _).flip
  refine IsPullback.of_right ?_ (congrArg (fun q => q.left) (famMap_fst D E F)) h₁
  have e₁ : (famMap D E F).left ≫ (snd (TF (R := R) E) D.P.A).left =
      (snd (TF (R := R) F) D.P.A).left := congrArg (fun q => q.left) (famMap_snd D E F)
  have e₂ : Spec.map (CommRingCat.ofHom (algebraMap E F)) ≫
      (TF (R := R) E).hom = (TF (R := R) F).hom := Over.w (baseMap (R := R) E F)
  rw [e₁, e₂]
  exact h₂
theorem famφ_famMap (α : D.X) (i : Fin 4) :
    DegPre.famφ D F α i = (famMap D E F).left ≫ DegPre.famφ D E α i := by
  fin_cases i
  · exact congrArg (fun q => q.left) (famMap_snd D E F).symm
  · refine congrArg (fun q => q.left) (Eq.symm ((MonObj.comp_mul (famMap D E F) (DegPre.prB D _) (cP D _ α)).trans ?_))
    rw [comp_cP, famMap_snd]; rfl
  · exact congrArg (fun q => q.left) (comp_cP D (famMap D E F) α).symm
  · exact congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (famMap D E F)).symm
theorem trF_famMap (mu : D.X) :
    DegPre.trF D F mu ≫ famMap D E F = famMap D E F ≫ DegPre.trF D E mu := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, Category.assoc, famMap_fst, DegPre.trF, DegPre.trF, lift_fst, lift_fst_assoc, famMap_fst]
  · rw [Category.assoc, Category.assoc, famMap_snd, DegPre.trF, DegPre.trF, lift_snd, lift_snd]
    refine Eq.symm ((MonObj.comp_mul (famMap D E F) (DegPre.prB D _) (cP D _ mu)).trans ?_)
    rw [comp_cP, famMap_snd]; rfl
theorem shiftVal_famMap (k : ℕ) (mu α : D.X) {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ DegPre.BF D F)
    (z : T.left) {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) :
    shiftVal D E k mu α (ρ ≫ famMap D E F) z J = shiftVal D F k mu α ρ z J := by
  refine congrArg₂ (· * ·) ?_ ?_
  · simp only [uVal, comp_cP, Category.assoc, famMap_snd]
  · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    congr 1
    rw [Category.assoc, famMap_fst, ← specMap_jFK (R := R) E F]
    simp only [Over.comp_left, Category.assoc]
    rfl
instance : NoetherianSpace (DegPre.BF D F).left := by
  have := D.P.isAb.proper
  have : IsProper (famBase D F) := inferInstanceAs (IsProper (pullback.fst _ _))
  have : IsLocallyNoetherian (DegPre.BF D F).left := LocallyOfFiniteType.isLocallyNoetherian (famBase D F)
  have : CompactSpace (DegPre.BF D F).left := QuasiCompact.compactSpace_of_compactSpace (famBase D F)
  have : IsNoetherian (DegPre.BF D F).left := {}
  infer_instance
def termPull (k : ℕ) (α : D.X) :
    FamTerm D E k α →ₛₗ[algebraMap E F] FamTerm D F k α :=
  pullOver D.P.L (DegPre.famε k) (isPullback_famMap D E F).w (famφ_famMap D E F α)
variable {D E F} in
theorem shift_termPull {k : ℕ} {mu α : D.X} {Θ Θ'} (hΘ : IsShift D E k mu α Θ)
    (hΘ' : IsShift D F k mu α Θ') (s : FamTerm D E k α) :
    Θ' (termPull D E F k α s) = termPull D E F k _ (Θ s) := by
  refine sec_ext' D.P.isLB fun y J hJ => ?_
  refine (hΘ' _ _ (𝟙 _) y J hJ).trans (Eq.trans ?_ ((sval_pullOver _ _ _ _ hJ).trans
    (hΘ s _ (𝟙 _ ≫ famMap D E F) y J hJ)).symm)
  refine congrArg₂ (· * ·) ((sval_pullOver _ _ _ _ hJ).trans ?_)
    (congrArg Units.val (shiftVal_famMap D E F k mu α _ y hJ).symm)
  congr 1
  rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, Category.assoc, Category.assoc, trF_famMap]
def famPull (hG : GlobalFnsSt) (k : ℕ) :
    Fam D E k →ₛₗ[algebraMap E F] Fam D F k where
  toFun s := ⟨fun α => termPull D E F k α (s.s α), by
    choose Θ hΘ using exists_isShift D E hG k
    choose Θ' hΘ' using exists_isShift D F hG k
    refine (famFE_iff hG hΘ' _).2 fun mu α => ?_
    exact (congrArg (termPull D E F k _) ((famFE_iff hG hΘ s.s).1 s.fe mu α)).trans
      (shift_termPull (hΘ mu α) (hΘ' mu α) _).symm⟩
  map_add' s t := fam_ext fun α j => congrArg (fun q => LB.Sec.f q j)
    (map_add (termPull D E F k α) (famProj D _ k α s) (famProj D _ k α t))
  map_smul' c s := fam_ext fun α j => congrArg (fun q => LB.Sec.f q j)
    (map_smulₛₗ (termPull D E F k α) c (famProj D _ k α s))
end Pull
end GlobalTheory.FieldBaseChange


