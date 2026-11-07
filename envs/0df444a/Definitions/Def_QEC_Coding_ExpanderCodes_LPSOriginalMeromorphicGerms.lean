-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicGerms
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicGerms
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:56:40.6162+00:00
-- url     : https://prove2.me/theorems/061939cd-04c4-44be-ba6d-c55b5b91ec3e
-- title:
--   LPSOriginal Meromorphic Germs
-- statement:
--   Definitions and structural lemmas for LPSOriginal Meromorphic Germs, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicGerms.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Algebra.Field.Basic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
def lpsOriginalMeromorphicGermSubring (U : Set ℂ) :
    Subring (Filter.Germ (Filter.codiscreteWithin U) ℂ) where
  carrier := {A | ∃ f : ℂ → ℂ, MeromorphicOn f U ∧
    A = (f : Filter.Germ (Filter.codiscreteWithin U) ℂ)}
  zero_mem' := ⟨0, MeromorphicOn.const 0, rfl⟩
  one_mem' := ⟨1, MeromorphicOn.const 1, rfl⟩
  add_mem' := by
    rintro A B ⟨f,hf,rfl⟩ ⟨g,hg,rfl⟩
    exact ⟨f+g,hf.add hg,rfl⟩
  neg_mem' := by
    rintro A ⟨f,hf,rfl⟩
    exact ⟨-f,hf.neg,rfl⟩
  mul_mem' := by
    rintro A B ⟨f,hf,rfl⟩ ⟨g,hg,rfl⟩
    exact ⟨f*g,hf.mul hg,rfl⟩
abbrev LPSOriginalMeromorphicGermRing (U : Set ℂ) :=
  ↥(lpsOriginalMeromorphicGermSubring U)
lemma lpsOriginalMeromorphicGerm_zero_of_orders_top
    (U : Set ℂ) (f : ℂ → ℂ)
    (h : ∀ x ∈ U, meromorphicOrderAt f x = ⊤) :
    (f : Filter.Germ (Filter.codiscreteWithin U) ℂ) = 0 := by
  change (f : Filter.Germ (Filter.codiscreteWithin U) ℂ) =
    (0 : ℂ → ℂ)
  apply Filter.Germ.coe_eq.mpr
  change {z : ℂ | f z = 0} ∈ Filter.codiscreteWithin U
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro x hx
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp (h x hx)] with z hz
  exact Or.inl hz
lemma lpsOriginalMeromorphicGerm_isUnit
    (U : Set ℂ) (hU : IsConnected U)
    (A : LPSOriginalMeromorphicGermRing U) (hA : A ≠ 0) : IsUnit A := by
  obtain ⟨f,hf,he⟩ := A.property
  have hf0 : (f : Filter.Germ (Filter.codiscreteWithin U) ℂ) ≠ 0 := by
    intro h
    apply hA
    apply Subtype.ext
    exact he.trans h
  have hex : ∃ x ∈ U, meromorphicOrderAt f x ≠ ⊤ := by
    by_contra! hn
    exact hf0 (lpsOriginalMeromorphicGerm_zero_of_orders_top U f hn)
  have hall := (hf.exists_meromorphicOrderAt_ne_top_iff_forall_mem hU).mp hex
  have hne := MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero hf hall
  let B : LPSOriginalMeromorphicGermRing U :=
    ⟨(f⁻¹ : Filter.Germ (Filter.codiscreteWithin U) ℂ), f⁻¹, hf.inv, rfl⟩
  have hab : A*B=1 := by
    apply Subtype.ext
    change A.val * (f⁻¹ : Filter.Germ (Filter.codiscreteWithin U) ℂ)=1
    rw [he]
    change ((f*f⁻¹ : ℂ → ℂ) : Filter.Germ (Filter.codiscreteWithin U) ℂ) =
      (1 : ℂ → ℂ)
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hne] with z hz
    exact mul_inv_cancel₀ hz
  exact isUnit_iff_exists_inv.mpr ⟨B,hab⟩
@[instance_reducible]
def lpsOriginalMeromorphicGermField
    (U : Set ℂ) [NeBot (Filter.codiscreteWithin U)] (hU : IsConnected U) :
    Field (LPSOriginalMeromorphicGermRing U) :=
  Field.ofIsUnitOrEqZero (fun A => by
    by_cases hA : A=0
    · exact Or.inr hA
    · exact Or.inl (lpsOriginalMeromorphicGerm_isUnit U hU A hA))
lemma lpsOriginalUpperHalfMeromorphicFilter_neBot :
    NeBot (Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet) := by
  have hi : Complex.I ∈ UpperHalfPlane.upperHalfPlaneSet := by
    simp [UpperHalfPlane.upperHalfPlaneSet]
  have hh : NeBot (𝓝[UpperHalfPlane.upperHalfPlaneSet \ {Complex.I}] Complex.I) := by
    rw [Set.sdiff_eq, nhdsWithin_inter_of_mem
      (nhdsWithin_le_nhds (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hi))]
    infer_instance
  let := hh
  apply Filter.neBot_of_le
    (show 𝓝[UpperHalfPlane.upperHalfPlaneSet \ {Complex.I}] Complex.I ≤
      Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet from ?_)
  exact le_iSup_of_le Complex.I (le_iSup_of_le hi le_rfl)
instance lpsOriginalUpperHalfMeromorphicField :
    Field (LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet) := by
  letI := lpsOriginalUpperHalfMeromorphicFilter_neBot
  exact lpsOriginalMeromorphicGermField UpperHalfPlane.upperHalfPlaneSet
    (Complex.isConnected_of_upperHalfPlane subset_rfl (by
      intro z hz
      exact (show 0 < z.im from hz).le))
lemma lpsOriginalHolomorphic_ofComplex_meromorphic (f : LPSOriginalHolomorphicRing) :
    MeromorphicOn (f.val ∘ UpperHalfPlane.ofComplex) UpperHalfPlane.upperHalfPlaneSet :=
  ((UpperHalfPlane.mdifferentiable_iff.mp f.property).analyticOnNhd
    UpperHalfPlane.isOpen_upperHalfPlaneSet).meromorphicOn
def lpsOriginalHolomorphicToMeromorphicGerm :
    LPSOriginalHolomorphicRing →+*
      LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet where
  toFun f := ⟨(f.val ∘ UpperHalfPlane.ofComplex :
    Filter.Germ (Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet) ℂ),
      f.val ∘ UpperHalfPlane.ofComplex,lpsOriginalHolomorphic_ofComplex_meromorphic f,rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
lemma lpsOriginalHolomorphicToMeromorphicGerm_injective :
    Function.Injective lpsOriginalHolomorphicToMeromorphicGerm := by
  intro f g h
  have hh := congrArg (fun A :
    LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet => A.val) h
  have he : (f.val ∘ UpperHalfPlane.ofComplex) =ᶠ[
      Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet]
      (g.val ∘ UpperHalfPlane.ofComplex) := Filter.Germ.coe_eq.mp hh
  apply Subtype.ext
  funext τ
  have hnear : (f.val ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝[≠] (τ : ℂ)]
      (g.val ∘ UpperHalfPlane.ofComplex) := by
    have hm := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp he (τ : ℂ) τ.im_pos
    have hH : ∀ᶠ z : ℂ in 𝓝[≠] (τ : ℂ), z ∈ UpperHalfPlane.upperHalfPlaneSet :=
      nhdsWithin_le_nhds (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
    filter_upwards [hm,hH] with z hz hzin
    exact hz.resolve_right (by simpa using hzin)
  have hf := (UpperHalfPlane.mdifferentiableAt_iff.mp (f.property τ)).continuousAt
  have hg := (UpperHalfPlane.mdifferentiableAt_iff.mp (g.property τ)).continuousAt
  have heq := tendsto_nhds_unique
    (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' hnear.symm)
  simpa only [Function.comp_apply,UpperHalfPlane.ofComplex_apply] using heq
instance lpsOriginalUpperHalfMeromorphicAlgebra :
    Algebra ℂ (LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet) :=
  (lpsOriginalHolomorphicToMeromorphicGerm.comp
    (algebraMap ℂ LPSOriginalHolomorphicRing)).toAlgebra
def lpsOriginalHolomorphicFractionToMeromorphicGerm :
    LPSOriginalHolomorphicFractionField →+*
      LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet :=
  IsFractionRing.lift lpsOriginalHolomorphicToMeromorphicGerm_injective
end
end QEC.Coding.TannerLiftedProduct


