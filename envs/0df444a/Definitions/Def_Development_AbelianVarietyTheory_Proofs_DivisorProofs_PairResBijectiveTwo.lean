-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PairResBijectiveTwo
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_PairResBijectiveTwo
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:09:53.728485+00:00
-- url     : https://prove2.me/theorems/833e3103-cb62-4fcb-bfda-de1951279578
-- title:
--   Pair Res Bijective Two
-- statement:
--   Definitions and structural lemmas for Pair Res Bijective Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PairResBijectiveTwo.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitMpOmjExtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommaDescentInjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommaDescentRestrictionEquivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwoCocycleCoboundaryOfBasisFunctorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneFormsTwoCocycleCoboundaryOfRestrictStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOneFormsCocycleRestrictSubCoboundaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HigherFormsOneCocycleCoboundaryOfRestrictStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompatibleHigherFormsExtendAlongFunctorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasLocalisationAtElementsTrivSqZeroExtFormsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommaFirstOrderCocycleLiftStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommaSecondOrderCocycleLiftStatement
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_restrict_pull1_injective_of_sep_glue
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Basis_oneCocycle_vanishing_comma_of_basis
import Theorems.Thm_GlobalTheory_CatCoh_Desc_glue_comma_of_basis
import Theorems.Thm_GlobalTheory_CatCoh_pull1_restrict_surjective_of_comma
import Theorems.Thm_GlobalTheory_CechDR_FormExtJ_isUnit_mp_omjExt_iff
import Theorems.Thm_GlobalTheory_CechDR_FormExtJ_mp_omjExt_inr
import Theorems.Thm_GlobalTheory_CechDR_FormExtJ_span_inlJ_eq_top
import Theorems.Thm_GlobalTheory_CechDR_FormExt_glue_one_forms
import Theorems.Thm_GlobalTheory_CechDR_FormExt_hasLoc_omExt
import Theorems.Thm_GlobalTheory_CechDR_FormExt_isUnit_mp_omExt_iff
import Theorems.Thm_GlobalTheory_CechDR_FormExt_span_inl_eq_top
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_CechDR_exists_pair_below_two
import Theorems.Thm_GlobalTheory_CechDR_form_eq_zero_of_basis_cover
import Theorems.Thm_GlobalTheory_CechDR_hasLoc_OAff
import Theorems.Thm_GlobalTheory_CechDR_pair_cover_affine
import Theorems.Thm_GlobalTheory_CechDR_twoForm_sep_of_basis
import Theorems.Thm_GlobalTheory_T_comma_descent_injective
import Theorems.Thm_GlobalTheory_T_comma_descent_restriction_equiv
import Theorems.Thm_GlobalTheory_T_comma_first_order_cocycle_lift
import Theorems.Thm_GlobalTheory_T_comma_second_order_cocycle_lift
import Theorems.Thm_GlobalTheory_T_compatible_higherForms_extend_along_functor
import Theorems.Thm_GlobalTheory_T_exists_oneForms_cocycle_restrict_sub_coboundary
import Theorems.Thm_GlobalTheory_T_hasLocalisationAtElements_trivSqZeroExtForms
import Theorems.Thm_GlobalTheory_T_higherForms_oneCocycle_coboundary_of_restrict
import Theorems.Thm_GlobalTheory_T_oneForms_twoCocycle_coboundary_of_restrict
import Theorems.Thm_GlobalTheory_T_twoCocycle_coboundary_of_basisFunctor
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_cocycle_one_forms_coboundary_of_restrict
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_GlobalTheory_restrict_glob1_bijective
import Theorems.Thm_GlobalTheory_sep_of_factoring_cover
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
namespace GlobalTheory.CechDR
open FormExt FormExtJ
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
theorem pairRes_bijective_two {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R') : Function.Bijective (pullHyp2 (pairRes φ s')) := by
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s'
  have hcov := _root_.GlobalTheory.CechDR.pair_cover_affine φ s'
  have hdir := _root_.GlobalTheory.CechDR.exists_pair_below_two φ s'

  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s') (pairFst φ) H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s') (pairFst φ) H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s') (pairFst φ) H hcov hdir
  have hv2 := GlobalTheory.T.twoCocycle_coboundary_of_basisFunctor (OAff s') (pairFst φ) H hcov hdir

  have hs1 := _root_.GlobalTheory.CechDR.form_eq_zero_of_basis_cover s' (pairFst φ) hcov
  have hg1 := _root_.GlobalTheory.CechDR.FormExt.glue_one_forms s' (pairFst φ) hcov hdir
  have unitE : ∀ {S S' : AffOp X'} (u : S ⟶ S') (b : (OAff s').obj S),
      IsUnit (mp (omExt (OAff s')) u (TrivSqZeroExt.inl b)) → IsUnit (mp (OAff s') u b) :=
    fun u b h ↦ ((isUnit_mp_omExt_iff (OAff s') u _).1 h)
  have HE := hasLoc_omExt (OAff s') H
  have hcovE : ∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (omExt (OAff s')).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S),
        IsUnit (mp (omExt (OAff s')) u (b i)) →
          ∃ (t : (Pair φ)ᵒᵖ) (v : T ⟶ (pairFst φ).obj t) (w : (pairFst φ).obj t ⟶ S), v ≫ w = u :=
    fun T ↦ by
      obtain ⟨n, b, hb, h⟩ := hcov T
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inl_eq_top (OAff s') hb,
        fun i S u hu ↦ h i S u (unitE u _ hu)⟩
  have hdirE : ∀ (t₁ t₂ : (Pair φ)ᵒᵖ) (S : AffOp X'), ((pairFst φ).obj t₁ ⟶ S) →
      ((pairFst φ).obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (omExt (OAff s')).obj S),
        Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'),
          IsUnit (mp (omExt (OAff s')) u (b i)) →
            ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty ((pairFst φ).obj t₃ ⟶ S') :=
    fun t₁ t₂ S a₁ a₂ ↦ by
      obtain ⟨n, b, hb, h⟩ := hdir t₁ t₂ S a₁ a₂
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inl_eq_top (OAff s') hb,
        fun i S' u hu ↦ h i S' u (unitE u _ hu)⟩
  have hsE := _root_.GlobalTheory.sep_of_factoring_cover (omExt (OAff s')) (pairFst φ) HE hcovE
  have hgE := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (omExt (OAff s')) (pairFst φ) HE hcovE hdirE
  have hvE := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (omExt (OAff s')) (pairFst φ) HE hcovE hdirE

  have hcovJ : ∀ j : ℕ, ∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (omjExt (OAff s') j).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S),
        IsUnit (mp (omjExt (OAff s') j) u (b i)) →
          ∃ (t : (Pair φ)ᵒᵖ) (v : T ⟶ (pairFst φ).obj t) (w : (pairFst φ).obj t ⟶ S), v ≫ w = u :=
    fun j T ↦ by
      obtain ⟨n, b, hb, h⟩ := hcov T
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inlJ_eq_top (OAff s') j hb,
        fun i S u hu ↦ h i S u ((isUnit_mp_omjExt_iff (OAff s') j u _).1 hu)⟩
  have hdirJ : ∀ j : ℕ, ∀ (t₁ t₂ : (Pair φ)ᵒᵖ) (S : AffOp X'), ((pairFst φ).obj t₁ ⟶ S) →
      ((pairFst φ).obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (omjExt (OAff s') j).obj S),
        Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'),
          IsUnit (mp (omjExt (OAff s') j) u (b i)) →
            ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty ((pairFst φ).obj t₃ ⟶ S') :=
    fun j t₁ t₂ S a₁ a₂ ↦ by
      obtain ⟨n, b, hb, h⟩ := hdir t₁ t₂ S a₁ a₂
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inlJ_eq_top (OAff s') j hb,
        fun i S' u hu ↦ h i S' u ((isUnit_mp_omjExt_iff (OAff s') j u _).1 hu)⟩
  have hsJ := fun j ↦ _root_.GlobalTheory.sep_of_factoring_cover (omjExt (OAff s') j) (pairFst φ)
    (GlobalTheory.T.hasLocalisationAtElements_trivSqZeroExtForms (OAff s') j H) (hcovJ j)
  have hgJ := fun j ↦ _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (omjExt (OAff s') j) (pairFst φ)
    (GlobalTheory.T.hasLocalisationAtElements_trivSqZeroExtForms (OAff s') j H) (hcovJ j) (hdirJ j)
  have hs3 : ∀ (T : AffOp X') (x : Om R' ((OAff s').obj T) 3),
      (∀ t (u : T ⟶ (pairFst φ).obj t), pOm (OAff s') 3 u x = 0) → x = 0 := by
    intro T x hx
    have h0 : (TrivSqZeroExt.inr x : (omjExt (OAff s') 3).obj T) = 0 :=
      hsJ 3 T _ fun t u ↦ (mp_omjExt_inr (OAff s') 3 u x).trans (by rw [hx t u]; exact TrivSqZeroExt.inr_zero _)
    simpa using congrArg TrivSqZeroExt.snd h0

  have b1 : Function.Bijective (pairRes φ s').pull1 :=
    ⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
      _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩
  have bg := _root_.GlobalTheory.restrict_glob1_bijective _ _ hs1 hg1
  have hs2 := _root_.GlobalTheory.CechDR.twoForm_sep_of_basis s' (pairFst φ) hcov
  refine ⟨GlobalTheory.T.comma_first_order_cocycle_lift _ _ (GlobalTheory.T.comma_descent_injective _ _ hs hg hv) b1.2
      (_root_.GlobalTheory.cocycle_one_forms_coboundary_of_restrict _ _ hs1 hg1) bg.2 hs2,
    GlobalTheory.T.comma_second_order_cocycle_lift _ _ (GlobalTheory.T.comma_descent_restriction_equiv _ _ hs hg hv hv2)
      (GlobalTheory.T.oneForms_twoCocycle_coboundary_of_restrict _ _ (GlobalTheory.T.comma_descent_injective _ _ hsE hgE hvE))
      (GlobalTheory.T.exists_oneForms_cocycle_restrict_sub_coboundary _ _ (_root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hsE hgE hvE))
      (GlobalTheory.T.higherForms_oneCocycle_coboundary_of_restrict _ _ 2 (_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ (hsJ 2) (hgJ 2)))
      (GlobalTheory.T.compatible_higherForms_extend_along_functor _ _ 2 (hsJ 2) (hgJ 2)) hs3⟩
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ)
def pairResEquiv2 (φ : X' ⟶ X) (s' : X' ⟶ Sp R') : HH2 s' ≃ₗ[R'] Hyp2 (OPair φ s') :=
  LinearEquiv.ofBijective (pullHyp2 (pairRes φ s')) (pairRes_bijective_two φ s')
def pullHH2 : HH2 s →ₛₗ[σ] HH2 s' :=
  (pairResEquiv2 φ s').symm.toLinearMap.comp (pullHyp2 (pairPull h))
end GlobalTheory.CechDR


