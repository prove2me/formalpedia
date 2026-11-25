-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T15:00:41.287219+00:00
-- url     : https://prove2.me/theorems/e47d575c-0886-5ded-8600-526234e3719d
-- title:
--   Is FETranslate Fe Translate
-- statement:
--   Definitions and structural lemmas for Is FETranslate Fe Translate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsFETranslateFeTranslate.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Theorems.Thm_GlobalTheory_FamFree_exists_fam_single
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_GC_fam__eq_3a137bedd551
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_UUA_val_powGen__89687e20c37b
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_cQ_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_exists_eB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_powGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tau_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_val_famMult
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_pullMulSec

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
section General
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
abbrev toF : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
abbrev strF : (DegPre.BF D F).left ⟶ Spec (CommRingCat.of F) := (fst (TF (R := R) F) D.P.A).left
abbrev SecBMod (j : ℕ) (α : D.X) : Type :=
  SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB α) (DegPre.famε j))
abbrev SecFMod (j : ℕ) (α : D.X) : Type :=
  SecOver (strF D F) (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε j))
theorem TF_hom : (TF (R := R) F).hom = Spec.map (CommRingCat.ofHom (toF (R := R) F)) := by
  show Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
theorem isPullback_prB : IsPullback (DegPre.prB D F).left (strF D F) D.P.A.hom
    (Spec.map (CommRingCat.ofHom (toF (R := R) F))) := by
  rw [← TF_hom]
  exact (IsPullback.of_hasPullback (TF (R := R) F).hom D.P.A.hom).flip
def resF (j : ℕ) (α : D.X) : SecBMod D j α →ₛₗ[toF (R := R) F] SecFMod D F j α :=
  pullOver D.P.L (DegPre.famε j) (isPullback_prB D F).w (GC.famφ_eq D F α)
def famComp (j : ℕ) (α : D.X) : Fam D F j →ₗ[F] SecFMod D F j α where
  toFun s := s.s α
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def IsFETranslate (j : ℕ) (mu α : D.X) (s : SecBMod D j α) (t : SecBMod D j (α + j • mu)) : Prop :=
  ∀ u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D (FractionRing R) j α mu) (DegPre.deltaε j)), u.IsGen →
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D (FractionRing R)).left)
      (DegPre.famMult D (FractionRing R) j mu α) →
    GeneratorPullback.SecRel D.P.L (DegPre.famφ D (FractionRing R) (α + j • mu)) (DegPre.famε j)
      (resF D (FractionRing R) j (α + j • mu) t) (DegPre.famφ D (FractionRing R) α) (DegPre.famε j)
      (resF D (FractionRing R) j α s) (DegPre.trF D (FractionRing R) mu).left
      (DegPre.deltaφ D (FractionRing R) j α mu) (DegPre.deltaε j) u
abbrev trB (mu : D.X) : D.P.A ⟶ D.P.A := 𝟙 D.P.A * cP D D.P.A mu
end General
section OverField
variable {k : Type} [Field k] (D : DegPre k)
theorem exists_feGen (j : ℕ) (mu α : D.X) :
    ∃ u : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.famφB (α + j • mu)) (fun i => (trB D mu).left ≫ D.famφB α i))
      (DegPre.deltaε j)), u.IsGen ∧ ∀ (T : Over (Spec (CommRingCat.of k))) (ρ : T ⟶ D.P.A) (κ : T ⟶ TK k)
      (z : T.left) (J), Good D.P.L z J →
      val u ρ.left z J = cubN (th D z J) j (cP D T α) (cP D T mu) ρ * (th D z J (cP D T α) ρ (cP D T mu))⁻¹ *
        (val (D.tau mu α) κ.left z J * (val (D.psi mu) κ.left z J ^ j * val D.rigK κ.left z J ^ j)) := by
  let _ : Algebra (FractionRing k) k := (FractionRing.algEquiv k k).toRingEquiv.toRingHom.toAlgebra
  have h₁ : jFK (R := k) k ≫ jK k = 𝟙 _ := by
    refine (TF_hom (R := k) k).trans ?_
    rw [show toF (R := k) k = RingHom.id k from RingHom.ext fun x => (FractionRing.algEquiv k k).commutes x,
      CommRingCat.ofHom_id, Spec.map_id]
  have h₂ : jK k ≫ jFK (R := k) k = 𝟙 _ := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, show (algebraMap k (FractionRing k)).comp
      (algebraMap (FractionRing k) k) = RingHom.id _ from RingHom.ext fun x =>
        ((FractionRing.algEquiv k k).symm.commutes _).symm.trans ((FractionRing.algEquiv k k).symm_apply_apply x),
      CommRingCat.ofHom_id, Spec.map_id]
  obtain ⟨u, hu, hv⟩ := SectionScalarValuation.exists_eB D j α mu (DegPre.famMult D k j mu α)
    (pullGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
      (powGen_isGen _ _ _ _ (D.psi_gen mu) j) (tau_isGen D mu α))
      (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) j)) _) (fun U _ h => by
    have a₁ : ∀ χ, D.P.A.hom ≫ jFK (R := k) k ≫ D.xK χ = (SectionScalarValuation.cQ D D.P.A χ).left := fun χ => by
      show D.P.A.hom ≫ jFK (R := k) k ≫ jK k ≫ (D.c χ).left = D.P.A.hom ≫ (D.c χ).left
      rw [← Category.assoc (jFK (R := k) k), h₁, Category.id_comp]
    have a₂ : D.P.A.hom ≫ jFK (R := k) k ≫ (toUnit (TK k)).left ≫ eSec D.P.A = (1 : D.P.A ⟶ D.P.A).left := by
      show D.P.A.hom ≫ jFK (R := k) k ≫ jK k ≫ eSec D.P.A = D.P.A.hom ≫ eSec D.P.A
      rw [← Category.assoc (jFK (R := k) k), h₁, Category.id_comp]
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
    rw [add_comm mu α, SectionScalarValuation.cQ_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
    module)
  refine ⟨u, hu, fun T ρ κ z J hJ => (hv T ρ z J hJ).trans (congrArg₂ (· * ·) rfl ?_)⟩
  let σ : T ⟶ TF (R := k) k := Over.homMk T.hom (by
    show T.hom ≫ jFK (R := k) k ≫ jK k = _
    rw [h₁, Category.comp_id])
  have e : σ.left ≫ jFK (R := k) k = κ.left := by
    show T.hom ≫ _ = _
    rw [← Over.w κ]
    show (κ.left ≫ jK k) ≫ _ = _
    rw [Category.assoc, h₂]; exact Category.comp_id _
  rw [Over.w ρ]
  refine (val_famMult σ hJ j mu α).trans ?_
  rw [UUA.val_powGen', UUA.val_powGen', e]
def feGen (j : ℕ) (mu α : D.X) := (exists_feGen D j mu α).choose
theorem feGen_isGen (j : ℕ) (mu α : D.X) : (feGen D j mu α).IsGen := (exists_feGen D j mu α).choose_spec.1
theorem exists_feTranslate (j : ℕ) (mu α : D.X) (s : SecBMod D j α) : ∃ t : SecBMod D j (α + j • mu),
    ∀ (Z : Scheme.{0}) (ρ : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
      sval t ρ z J = sval s (ρ ≫ (trB D mu).left) z J * (val (feGen D j mu α) ρ z J).val := by
  obtain ⟨t, ht⟩ := exists_sec D.P.isLB (φ' := D.famφB (α + j • mu)) (ε' := DegPre.famε j) (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [DegPre.deltaε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg,
        Finset.prod_inv_distrib]
      exact (mul_comm _ _).trans (inv_mul_cancel_right _ _))
    (pullMulSec s (trB D mu).left (feGen D j mu α) (feGen_isGen D j mu α))
  exact ⟨t, fun Z ρ z J hJ => (ht Z ρ z J hJ).trans (sval_pullMulSec _ _ _ _ ρ z hJ)⟩
def feTranslate (j : ℕ) (mu α : D.X) (s : SecBMod D j α) : SecBMod D j (α + j • mu) :=
  (exists_feTranslate D j mu α s).choose
end OverField
section ThetaShiftProofs
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k} {a : ArcIn D l β k b}
  {P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
  {oP : letI := H.starRing; P.toPre.OAct (𝓞 E)} {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
  {he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A}
  {w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)} {e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X} (hW : WitData a P oP φ he w e)
include hW
theorem push_cP (T : Over (Spec (CommRingCat.of (PowerSeries k)))) (χ : a.D₀.X) :
    pushHom hW.1 T (cP P.toPre T (e χ)) = cP a.D₀ _ χ := Over.OverMorphism.ext (by
  show (T.hom ≫ (P.toPre.c (e χ)).left) ≫ φ = (T.hom ≫ spMap (PowerSeries.C (R := k))) ≫ (a.D₀.c χ).left
  rw [Category.assoc, hW.2.2.2.2.1, Category.assoc])
theorem famφB_comp (α : a.D₀.X) (i : Fin 4) : P.toPre.famφB (e α) i ≫ φ = φ ≫ a.D₀.famφB α i := by
  let ρ := pushHom hW.1 P.toPre.P.A (𝟙 _)
  have hρ : ρ.left = φ := Category.id_comp _
  fin_cases i
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · have e₁ : pushHom hW.1 _ (𝟙 _ * cP P.toPre _ (e α)) = ρ ≫ (𝟙 _ * cP a.D₀ _ α) := by
      rw [map_mul, push_cP hW, MonObj.comp_mul, comp_cP, Category.comp_id]
    exact (congrArg (fun q => q.left) e₁).trans (congrArg (· ≫ _) hρ)
  · have e₁ : pushHom hW.1 _ (cP P.toPre _ (e α)) = ρ ≫ cP a.D₀ _ α := by rw [push_cP hW, comp_cP]
    exact (congrArg (fun q => q.left) e₁).trans (congrArg (· ≫ _) hρ)
  · have e₁ : pushHom hW.1 P.toPre.P.A 1 = ρ ≫ (1 : a.D₀.P.A ⟶ a.D₀.P.A) := by rw [map_one, MonObj.comp_one]
    exact (congrArg (fun q => q.left) e₁).trans (congrArg (· ≫ _) hρ)
def pullB (j : ℕ) (α : a.D₀.X) :
    SecBMod a.D₀ j α →ₛₗ[PowerSeries.C (R := k)] SecBMod P.toPre j (e α) :=
  pullThrough hW.2.1 a.D₀.P.isLB P.toPre.P.isLB (famφB_comp hW α) (DegPre.famε j) hW.1.1.w
variable (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F]
omit hW in

abbrev constF (k : Type) [Field k] (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F] : k →+* F :=
  (toF (R := PowerSeries k) F).comp (PowerSeries.C (R := k))
theorem famφ_comp (α : a.D₀.X) (i : Fin 4) :
    DegPre.famφ P.toPre F (e α) i ≫ φ = ((DegPre.prB P.toPre F).left ≫ φ) ≫ a.D₀.famφB α i := by
  rw [GC.famφ_eq, Category.assoc, famφB_comp hW, Category.assoc]
theorem isPullback_prB_comp : IsPullback ((DegPre.prB P.toPre F).left ≫ φ) (strF P.toPre F) a.D₀.P.A.hom
    (Spec.map (CommRingCat.ofHom (constF k F))) := by
  have := (isPullback_prB P.toPre F).paste_horiz hW.1.1
  rwa [← Spec.map_comp, ← CommRingCat.ofHom_comp] at this
def pullF (j : ℕ) (α : a.D₀.X) : SecBMod a.D₀ j α →ₛₗ[constF k F] SecFMod P.toPre F j (e α) :=
  pullThrough hW.2.1 a.D₀.P.isLB P.toPre.P.isLB (famφ_comp hW F α) (DegPre.famε j) (isPullback_prB_comp hW F).w
variable (hG : GlobalFnsSt) {j : ℕ} (hj : 1 ≤ j)
def constFam (α : a.D₀.X) (s₀ : SecBMod a.D₀ j α) : Fam P.toPre F j :=
  (FamFree.exists_fam_single hG P.tau_bimult hj (e α) (pullF hW F j α s₀)).choose
omit hW in

def expo (a : ArcIn D l β k b) (j : ℕ) (α mu : a.D₀.X) : ℤ := j * (a.be mu mu / 2) + a.be mu α
def IsIntegralForm (j : ℕ) (α : a.D₀.X) (s₀ : SecBMod a.D₀ j α) (m : ℕ) (f : ∀ χ, SecBMod P.toPre j χ) : Prop :=
  (∀ mu, 0 ≤ (m : ℤ) + expo a j α mu ∧ f (e (α + j • mu)) =
    (PowerSeries.X : PowerSeries k) ^ ((m : ℤ) + expo a j α mu).toNat •
      pullB hW j (α + j • mu) (feTranslate a.D₀ j mu α s₀)) ∧
  ∀ χ, (∀ mu, e α + j • mu ≠ χ) → f χ = 0
end ThetaShiftProofs
end GlobalTheory.ConstFam


