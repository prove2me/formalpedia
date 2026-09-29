-- Prove2me | solution 1 for AutomorphicForm.exists_forall_lintegral_comp_flowChart_le_mul_lintegral_of_forall_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b2df316b-f7ef-59bd-a8de-064705a46726

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar

import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_ArchType
import Theorems.Thm_NumberField_AdelicHaar_exists_map_adelicGLHaar_eq_smul_prod
import Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_lintegral_comp_glArch_flowChart_mul_le
import Theorems.Thm_AutomorphicForm_continuous_archFlowAt_and_continuous_archFlowAtComplex
import Theorems.Thm_AutomorphicForm_isCompact_principalLevel_inf_finiteAdelicGL2Subgroup
import Theorems.Thm_AutomorphicForm_isOpen_principalLevel
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_lintegral_comp_flowChart_le_mul_lintegral_of_forall_mul_eq
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.InfinitePlace
open AutomorphicForm
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel
open Topology
open scoped Classical NNReal ENNReal

noncomputable section

namespace H3Proof

section SC

variable (K : Type) [Field K] [NumberField K]

theorem secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology K
  have hf : IsEmbedding (fun a : InfiniteAdeleRing K => ((a, 0) : AdeleRing (𝓞 K) K)) :=
    IsEmbedding.of_comp (continuous_id.prodMk continuous_const) continuous_fst IsEmbedding.id
  exact hf.secondCountableTopology

theorem secondCountableTopology_finiteAdeleRing : SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) := by
  haveI : SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology K
  have hf : IsEmbedding (fun b : FiniteAdeleRing (𝓞 K) K => ((0, b) : AdeleRing (𝓞 K) K)) :=
    IsEmbedding.of_comp (continuous_const.prodMk continuous_id) continuous_snd IsEmbedding.id
  exact hf.secondCountableTopology

theorem secondCountableTopology_gl (n : Type) [Fintype n] [DecidableEq n]
    (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R] :
    SecondCountableTopology (GL n R) := by
  haveI : SecondCountableTopology (Matrix n n R) := inferInstanceAs (SecondCountableTopology (n → n → R))
  haveI : SecondCountableTopology (Matrix n n R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem locallyCompactSpace_gl (n : Type) [Fintype n] [DecidableEq n]
    (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] :
    LocallyCompactSpace (GL n R) := by
  haveI : LocallyCompactSpace (Matrix n n R) := inferInstanceAs (LocallyCompactSpace (n → n → R))
  haveI : T2Space (Matrix n n R) := inferInstanceAs (T2Space (n → n → R))
  haveI : LocallyCompactSpace (Matrix n n R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

end SC

section Split

variable (n : Type) [Fintype n] [DecidableEq n] (K : Type) [Field K] [NumberField K]

def fwd : GL n (AdeleRing (𝓞 K) K) →* GL n (InfiniteAdeleRing K) × GL n (FiniteAdeleRing (𝓞 K) K) :=
  MonoidHom.prod (Matrix.GeneralLinearGroup.map (adeleArch (𝓞 K) K))
    (Matrix.GeneralLinearGroup.map (adeleFin (𝓞 K) K))

def glue (a : Matrix n n (InfiniteAdeleRing K)) (b : Matrix n n (FiniteAdeleRing (𝓞 K) K)) :
    Matrix n n (AdeleRing (𝓞 K) K) :=
  Matrix.of fun i j => ((a i j, b i j) : AdeleRing (𝓞 K) K)

omit [DecidableEq n] in
theorem glue_mul (a a' : Matrix n n (InfiniteAdeleRing K)) (b b' : Matrix n n (FiniteAdeleRing (𝓞 K) K)) :
    glue n K a b * glue n K a' b' = glue n K (a * a') (b * b') := by
  ext i j
  simp only [glue, Matrix.mul_apply, Matrix.of_apply]
  change (_ : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) = _
  rw [Prod.ext_iff]
  refine ⟨?_, ?_⟩
  · show (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) (∑ x, _) = _
    rw [map_sum]; rfl
  · show (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) (∑ x, _) = _
    rw [map_sum]; rfl

omit [Fintype n] in
theorem glue_one : glue n K (1 : Matrix n n (InfiniteAdeleRing K)) (1 : Matrix n n (FiniteAdeleRing (𝓞 K) K)) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [glue]; rfl
  · simp [glue, Matrix.one_apply_ne h]; rfl

def bwd (p : GL n (InfiniteAdeleRing K) × GL n (FiniteAdeleRing (𝓞 K) K)) : GL n (AdeleRing (𝓞 K) K) where
  val := glue n K (p.1 : Matrix n n (InfiniteAdeleRing K)) (p.2 : Matrix n n (FiniteAdeleRing (𝓞 K) K))
  inv := glue n K ((p.1⁻¹ : GL n (InfiniteAdeleRing K)) : Matrix n n (InfiniteAdeleRing K))
    ((p.2⁻¹ : GL n (FiniteAdeleRing (𝓞 K) K)) : Matrix n n (FiniteAdeleRing (𝓞 K) K))
  val_inv := by rw [glue_mul, Units.mul_inv, Units.mul_inv, glue_one]
  inv_val := by rw [glue_mul, Units.inv_mul, Units.inv_mul, glue_one]

theorem fwd_bwd (p : GL n (InfiniteAdeleRing K) × GL n (FiniteAdeleRing (𝓞 K) K)) : fwd n K (bwd n K p) = p :=
  Prod.ext (Units.ext (Matrix.ext fun _ _ => rfl)) (Units.ext (Matrix.ext fun _ _ => rfl))

theorem bwd_fwd (x : GL n (AdeleRing (𝓞 K) K)) : bwd n K (fwd n K x) = x :=
  Units.ext (Matrix.ext fun _ _ => Prod.ext rfl rfl)

def splitMulEquiv : GL n (AdeleRing (𝓞 K) K) ≃* GL n (InfiniteAdeleRing K) × GL n (FiniteAdeleRing (𝓞 K) K) :=
  { toFun := fwd n K
    invFun := bwd n K
    left_inv := bwd_fwd n K
    right_inv := fwd_bwd n K
    map_mul' := map_mul (fwd n K) }

theorem continuous_fwd : Continuous (fwd n K) := by
  refine Continuous.prodMk ?_ ?_
  · refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact (continuous_id.matrix_map continuous_fst).comp Units.continuous_val
    · have : (fun x : GL n (AdeleRing (𝓞 K) K) =>
          ((↑(Matrix.GeneralLinearGroup.map (adeleArch (𝓞 K) K) x)⁻¹ : Matrix n n (InfiniteAdeleRing K))))
          = fun x => (RingHom.mapMatrix (adeleArch (𝓞 K) K)) ((x⁻¹ : GL n (AdeleRing (𝓞 K) K)) : Matrix _ _ _) := by
        funext x; rw [← map_inv]; rfl
      rw [this]
      exact (continuous_id.matrix_map continuous_fst).comp Units.continuous_coe_inv
  · refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact (continuous_id.matrix_map continuous_snd).comp Units.continuous_val
    · have : (fun x : GL n (AdeleRing (𝓞 K) K) =>
          ((↑(Matrix.GeneralLinearGroup.map (adeleFin (𝓞 K) K) x)⁻¹ : Matrix n n (FiniteAdeleRing (𝓞 K) K))))
          = fun x => (RingHom.mapMatrix (adeleFin (𝓞 K) K)) ((x⁻¹ : GL n (AdeleRing (𝓞 K) K)) : Matrix _ _ _) := by
        funext x; rw [← map_inv]; rfl
      rw [this]
      exact (continuous_id.matrix_map continuous_snd).comp Units.continuous_coe_inv

omit [Fintype n] [DecidableEq n] in
theorem continuous_glue : Continuous (fun p : Matrix n n (InfiniteAdeleRing K) × Matrix n n (FiniteAdeleRing (𝓞 K) K) =>
    glue n K p.1 p.2) := by
  refine continuous_matrix fun i j => ?_
  exact ((continuous_apply_apply i j).comp continuous_fst).prodMk ((continuous_apply_apply i j).comp continuous_snd)

theorem continuous_bwd : Continuous (bwd n K) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_glue n K).comp
      ((Units.continuous_val.comp continuous_fst).prodMk (Units.continuous_val.comp continuous_snd))
  · exact (continuous_glue n K).comp
      ((Units.continuous_coe_inv.comp continuous_fst).prodMk (Units.continuous_coe_inv.comp continuous_snd))

def splitEquiv : GL n (AdeleRing (𝓞 K) K) ≃ₜ* GL n (InfiniteAdeleRing K) × GL n (FiniteAdeleRing (𝓞 K) K) :=
  { splitMulEquiv n K with
    continuous_toFun := continuous_fwd n K
    continuous_invFun := continuous_bwd n K }

theorem splitEquiv_apply (x : GL n (AdeleRing (𝓞 K) K)) :
    splitEquiv n K x = (Matrix.GeneralLinearGroup.map (adeleArch (𝓞 K) K) x,
      Matrix.GeneralLinearGroup.map (adeleFin (𝓞 K) K) x) := rfl

end Split

section Receipts

variable (K : Type) [Field K] [NumberField K]

theorem fwd_eq (g : AdelicGL2 (𝓞 K) K) : fwd (Fin 2) K g = (glArch (𝓞 K) K g, glFin (𝓞 K) K g) := rfl

theorem glArch_bwd (p : GL (Fin 2) (InfiniteAdeleRing K) × GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    glArch (𝓞 K) K (bwd (Fin 2) K p) = p.1 := congrArg Prod.fst (fwd_bwd (Fin 2) K p)

theorem glFin_bwd (p : GL (Fin 2) (InfiniteAdeleRing K) × GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    glFin (𝓞 K) K (bwd (Fin 2) K p) = p.2 := congrArg Prod.snd (fwd_bwd (Fin 2) K p)

theorem bwd_mul (p q : GL (Fin 2) (InfiniteAdeleRing K) × GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    bwd (Fin 2) K (p * q) = bwd (Fin 2) K p * bwd (Fin 2) K q :=
  map_mul (splitMulEquiv (Fin 2) K).symm p q

theorem bwd_glArch_of_glFin_eq_one {a : AdelicGL2 (𝓞 K) K} (ha : glFin (𝓞 K) K a = 1) :
    bwd (Fin 2) K (glArch (𝓞 K) K a, 1) = a := by
  rw [← ha]; exact bwd_fwd (Fin 2) K a

theorem eq_bwd_one_glFin_of_glArch_eq_one {u : AdelicGL2 (𝓞 K) K} (hu : glArch (𝓞 K) K u = 1) :
    u = bwd (Fin 2) K (1, glFin (𝓞 K) K u) := by
  rw [← hu]; exact (bwd_fwd (Fin 2) K u).symm

theorem mul_bwd (x : AdelicGL2 (𝓞 K) K) (p : GL (Fin 2) (InfiniteAdeleRing K) × GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    x * bwd (Fin 2) K p = bwd (Fin 2) K ((glArch (𝓞 K) K x, glFin (𝓞 K) K x) * p) := by
  rw [bwd_mul, ← fwd_eq, bwd_fwd]

end Receipts

end H3Proof

namespace H3Proof

section ProductFormula

variable (K : Type) [Field K] [NumberField K]

scoped instance mSpArch : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K)) := borel _
scoped instance bSpArch : BorelSpace (GL (Fin 2) (InfiniteAdeleRing K)) := ⟨rfl⟩
scoped instance mSpFin : MeasurableSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := borel _
scoped instance bSpFin : BorelSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := ⟨rfl⟩
scoped instance scArch : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing K)) := by
  haveI := secondCountableTopology_infiniteAdeleRing K; exact secondCountableTopology_gl (Fin 2) (InfiniteAdeleRing K)
scoped instance scFin : SecondCountableTopology (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := by
  haveI := secondCountableTopology_finiteAdeleRing K; exact secondCountableTopology_gl (Fin 2) (FiniteAdeleRing (𝓞 K) K)
scoped instance lcArch : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing K)) := locallyCompactSpace_gl (Fin 2) (InfiniteAdeleRing K)
scoped instance lcFin : LocallyCompactSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := locallyCompactSpace_gl (Fin 2) (FiniteAdeleRing (𝓞 K) K)

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

def splitMeas : AdelicGL2 (𝓞 K) K ≃ᵐ GL (Fin 2) (InfiniteAdeleRing K) × GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) :=
  (splitEquiv (Fin 2) K).toHomeomorph.toMeasurableEquiv

theorem splitMeas_apply (g : AdelicGL2 (𝓞 K) K) : splitMeas K g = (glArch (𝓞 K) K g, glFin (𝓞 K) K g) := rfl

theorem splitMeas_symm_apply (p : GL (Fin 2) (InfiniteAdeleRing K) × GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    (splitMeas K).symm p = bwd (Fin 2) K p := rfl

theorem measurable_bwd : Measurable (bwd (Fin 2) K) := (continuous_bwd (Fin 2) K).measurable

theorem setLIntegral_image_mul_left {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [IsTopologicalGroup G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (a : G) (s : Set G) (hs : MeasurableSet s) (f : G → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ y in (fun z => a * z) '' s, f y ∂μ = ∫⁻ z in s, f (a * z) ∂μ := by
  have himg : (fun z => a * z) '' s = (fun z => a⁻¹ * z) ⁻¹' s := by
    ext y; constructor
    · rintro ⟨z, hz, rfl⟩; simpa using hz
    · intro hy; exact ⟨a⁻¹ * y, hy, by simp⟩
  have hms : MeasurableSet ((fun z => a * z) '' s) := by rw [himg]; exact hs.preimage (measurable_const_mul _)
  rw [← lintegral_indicator hms, ← lintegral_indicator hs, ← lintegral_mul_left_eq_self (((fun z => a * z) '' s).indicator f) a]
  congr 1; funext z
  simp only [himg, Set.indicator, Set.mem_preimage, inv_mul_cancel_left]

theorem product_formula
    (μa : Measure (GL (Fin 2) (InfiniteAdeleRing K))) [μa.IsHaarMeasure] [μa.Regular] :
    ∃ μf : Measure (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)), μf.IsHaarMeasure ∧
    ∃ c₀ : ℝ≥0, 0 < c₀ ∧
      ∀ (x : AdelicGL2 (𝓞 K) K) (S : Set (GL (Fin 2) (InfiniteAdeleRing K))), MeasurableSet S →
        ∀ (V : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))), MeasurableSet V →
        ∀ (G : AdelicGL2 (𝓞 K) K → ℝ≥0∞), Measurable G →
        (∀ (y : AdelicGL2 (𝓞 K) K) (z : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)), z ∈ V → G (y * bwd (Fin 2) K (1, z)) = G y) →
          ∫⁻ g in (fun θ => x * θ) '' (bwd (Fin 2) K '' (S ×ˢ V)), G g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
            (c₀ : ℝ≥0∞) * μf V * ∫⁻ y in S, G (x * bwd (Fin 2) K (y, 1)) ∂μa := by
  set μf : Measure (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := Measure.haar with hμf
  haveI : μf.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μf
  obtain ⟨c₀, hc₀, hmap⟩ := NumberField.AdelicHaar.exists_map_adelicGLHaar_eq_smul_prod (Fin 2) K μa μf
  refine ⟨μf, inferInstance, c₀, hc₀, fun x S hS V hV G hG hGV => ?_⟩
  set xa := glArch (𝓞 K) K x with hxa
  set xf := glFin (𝓞 K) K x with hxf

  set T : Set (GL (Fin 2) (InfiniteAdeleRing K) × GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :=
    ((fun y => xa * y) '' S) ×ˢ ((fun z => xf * z) '' V) with hT
  have hSa : MeasurableSet ((fun y => xa * y) '' S) := by
    have : (fun y => xa * y) '' S = (fun y => xa⁻¹ * y) ⁻¹' S := by
      ext y; constructor
      · rintro ⟨z, hz, rfl⟩; simpa using hz
      · intro hy; exact ⟨xa⁻¹ * y, hy, by simp⟩
    rw [this]; exact hS.preimage (measurable_const_mul _)
  have hVf : MeasurableSet ((fun z => xf * z) '' V) := by
    have : (fun z => xf * z) '' V = (fun z => xf⁻¹ * z) ⁻¹' V := by
      ext y; constructor
      · rintro ⟨z, hz, rfl⟩; simpa using hz
      · intro hy; exact ⟨xf⁻¹ * y, hy, by simp⟩
    rw [this]; exact hV.preimage (measurable_const_mul _)
  have hTm : MeasurableSet T := hSa.prod hVf
  have hset : (fun θ => x * θ) '' (bwd (Fin 2) K '' (S ×ˢ V)) = (splitMeas K) ⁻¹' T := by
    ext g
    constructor
    · rintro ⟨θ, ⟨p, ⟨hp1, hp2⟩, rfl⟩, rfl⟩
      show splitMeas K (x * bwd (Fin 2) K p) ∈ T
      rw [splitMeas_apply, mul_bwd, glArch_bwd, glFin_bwd]
      exact ⟨⟨p.1, hp1, rfl⟩, ⟨p.2, hp2, rfl⟩⟩
    · rintro ⟨⟨s, hs, hs'⟩, ⟨v, hv, hv'⟩⟩
      refine ⟨bwd (Fin 2) K (s, v), ⟨(s, v), ⟨hs, hv⟩, rfl⟩, ?_⟩
      show x * bwd (Fin 2) K (s, v) = g
      rw [mul_bwd]
      have : (glArch (𝓞 K) K g, glFin (𝓞 K) K g) = (xa, xf) * (s, v) := Prod.ext hs'.symm hv'.symm
      rw [← hxa, ← hxf, ← this]
      exact bwd_fwd (Fin 2) K g

  have hF : Measurable fun p : GL (Fin 2) (InfiniteAdeleRing K) × GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => G (bwd (Fin 2) K p) :=
    hG.comp (measurable_bwd K)
  have step1 : ∫⁻ g in (fun θ => x * θ) '' (bwd (Fin 2) K '' (S ×ˢ V)), G g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫⁻ p in T, G (bwd (Fin 2) K p) ∂(Measure.map (splitMeas K) (adelicGLHaar (Fin 2) (𝓞 K) K)) := by
    rw [hset, ← lintegral_indicator hTm, ← lintegral_indicator ((splitMeas K).measurable hTm),
      lintegral_map_equiv]
    refine lintegral_congr fun g => ?_
    simp only [Set.indicator, Set.mem_preimage]
    split_ifs with h
    · show G g = G (bwd (Fin 2) K (splitMeas K g)); rw [splitMeas_apply, ← fwd_eq, bwd_fwd]
    · rfl
  have hmap' : Measure.map (splitMeas K) (adelicGLHaar (Fin 2) (𝓞 K) K) = c₀ • μa.prod μf := hmap
  rw [step1, hmap', Measure.restrict_smul, lintegral_smul_measure, hT, ← Measure.prod_restrict,
    lintegral_prod _ hF.aemeasurable]

  have hinner : ∀ y : GL (Fin 2) (InfiniteAdeleRing K),
      ∫⁻ z, G (bwd (Fin 2) K (y, z)) ∂(μf.restrict ((fun z => xf * z) '' V)) = μf V * G (bwd (Fin 2) K (y, xf)) := by
    intro y
    have h1 := setLIntegral_image_mul_left μf xf V hV (fun z => G (bwd (Fin 2) K (y, z)))
      (hF.comp (measurable_const.prodMk measurable_id))
    rw [h1]
    have h2 : ∀ z ∈ V, G (bwd (Fin 2) K (y, xf * z)) = G (bwd (Fin 2) K (y, xf)) := by
      intro z hz
      have : bwd (Fin 2) K (y, xf * z) = bwd (Fin 2) K (y, xf) * bwd (Fin 2) K (1, z) := by
        rw [← bwd_mul]; simp
      rw [this, hGV _ z hz]
    rw [setLIntegral_congr_fun hV h2, setLIntegral_const, mul_comm]
  simp_rw [hinner]

  rw [lintegral_const_mul (μf V) (show Measurable (fun y : GL (Fin 2) (InfiniteAdeleRing K) => G (bwd (Fin 2) K (y, xf))) from
    hF.comp (measurable_id.prodMk measurable_const))]
  have h3 := setLIntegral_image_mul_left μa xa S hS (fun y => G (bwd (Fin 2) K (y, xf)))
    (hF.comp (measurable_id.prodMk measurable_const))
  rw [h3]
  have h4 : ∀ y ∈ S, G (bwd (Fin 2) K (xa * y, xf)) = G (x * bwd (Fin 2) K (y, 1)) := by
    intro y _
    rw [mul_bwd]
    congr 2
    exact Prod.ext (by simp [hxa]) (by simp [hxf])
  rw [setLIntegral_congr_fun hS h4]
  simp only [ENNReal.smul_def, smul_eq_mul]
  ring

end ProductFormula
end H3Proof
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_lintegral_comp_flowChart_le_mul_lintegral_of_forall_mul_eq.H3Proof"

namespace H3Proof

section Assembly

open NumberField.InfinitePlace.Completion

variable (K : Type) [Field K] [NumberField K]

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

abbrev Letter : Type :=
  (Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕ (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)

def flowd : Letter K → ℝ → AdelicGL2 (𝓞 K) K :=
  fun d t => Sum.elim (fun d => archFlowAt d.2.1 d.2.2 t) (fun d => archFlowAtComplex d.2.1 d.2.2 t) d

theorem glFin_flowd (d : Letter K) (t : ℝ) : glFin (𝓞 K) K (flowd K d t) = 1 := by
  rcases d with ⟨w, hw, dir⟩ | ⟨w, hw, dir⟩
  · exact glFin_adelicArchGLIncl K _
  · exact glFin_adelicArchGLIncl K _

theorem continuous_flowd (d : Letter K) : Continuous (flowd K d) := by
  obtain ⟨hR, hC⟩ := AutomorphicForm.continuous_archFlowAt_and_continuous_archFlowAtComplex K
  rcases d with ⟨w, hw, dir⟩ | ⟨w, hw, dir⟩
  · exact hR w hw dir
  · exact hC w hw dir

theorem glFin_list_prod_eq_one (L : List (AdelicGL2 (𝓞 K) K)) (h : ∀ g ∈ L, glFin (𝓞 K) K g = 1) :
    glFin (𝓞 K) K L.prod = 1 := by
  rw [map_list_prod]
  exact List.prod_eq_one fun x hx => by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    exact h g hg

theorem continuous_adelicArchGLInclAt_comp {X : Type*} [TopologicalSpace X] {w : InfinitePlace K} (k : X → GL (Fin 2) w.Completion)
    (hk : ∀ i j, Continuous fun t => (k t : Matrix (Fin 2) (Fin 2) w.Completion) i j)
    (hki : ∀ i j, Continuous fun t => (((k t)⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j) :
    Continuous fun t => (adelicArchGLInclAt K w (k t) : AdelicGL2 (𝓞 K) K) := by
  have key : ∀ (m : X → Matrix (Fin 2) (Fin 2) w.Completion), (∀ i j, Continuous fun t => m t i j) →
      Continuous fun t => fun i j => ((fun v => (Function.update (1 : Π v : InfinitePlace K, Matrix (Fin 2) (Fin 2) v.Completion) w
        (m t)) v i j, (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) : AdeleRing (𝓞 K) K) := by
    intro m hm
    have hM : Continuous fun t => (fun i j => m t i j : Matrix (Fin 2) (Fin 2) w.Completion) :=
      continuous_pi fun i => continuous_pi fun j => hm i j
    have hU : Continuous fun t => Function.update (1 : Π v : InfinitePlace K, Matrix (Fin 2) (Fin 2) v.Completion) w (m t) :=
      continuous_const.update w hM
    refine continuous_pi fun i => continuous_pi fun j => ?_
    refine Continuous.prodMk ?_ continuous_const
    exact continuous_pi fun v => ((continuous_apply j).comp ((continuous_apply i).comp ((continuous_apply v).comp hU)))
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have : (fun t => ((adelicArchGLInclAt K w (k t) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) =
        fun t => fun i j => ((fun v => (Function.update (1 : Π v : InfinitePlace K, Matrix (Fin 2) (Fin 2) v.Completion) w
          ((k t : Matrix (Fin 2) (Fin 2) w.Completion))) v i j, (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) : AdeleRing (𝓞 K) K) := by
      funext t; ext i j; rfl
    change Continuous fun t => ((adelicArchGLInclAt K w (k t) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
    rw [this]; exact key _ hk
  · have : (fun t => (((adelicArchGLInclAt K w (k t))⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) =
        fun t => fun i j => ((fun v => (Function.update (1 : Π v : InfinitePlace K, Matrix (Fin 2) (Fin 2) v.Completion) w
          (((k t)⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)) v i j,
            (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) : AdeleRing (𝓞 K) K) := by
      funext t; rw [← map_inv]; ext i j; rfl
    change Continuous fun t => (((adelicArchGLInclAt K w (k t))⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
    rw [this]; exact key _ hki

def sR (w : {w : InfinitePlace K // w.IsReal}) (a : ℝ) : AdelicGL2 (𝓞 K) K :=
  archRealGLAt w.2 (Units.map (Matrix.scalar (Fin 2) : ℝ →+* Matrix (Fin 2) (Fin 2) ℝ).toMonoidHom
    (Units.mk0 (Real.exp a) (Real.exp_ne_zero a)))

def sC (w : {w : InfinitePlace K // w.IsComplex}) (b : ℂ) : AdelicGL2 (𝓞 K) K :=
  archComplexGLAt w.2 (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom
    (Units.mk0 (Complex.exp b) (Complex.exp_ne_zero b)))

theorem glFin_sR (w : {w : InfinitePlace K // w.IsReal}) (a : ℝ) : glFin (𝓞 K) K (sR K w a) = 1 := glFin_adelicArchGLIncl K _
theorem glFin_sC (w : {w : InfinitePlace K // w.IsComplex}) (b : ℂ) : glFin (𝓞 K) K (sC K w b) = 1 := glFin_adelicArchGLIncl K _

theorem continuous_archRealGLAt {w : InfinitePlace K} (hw : w.IsReal) : Continuous (archRealGLAt (F := K) hw) := by
  have hdef : archRealGLAt (F := K) hw = (adelicArchGLInclAt K w).comp (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm).toMonoidHom := rfl
  rw [hdef, MonoidHom.coe_comp]
  refine continuous_adelicArchGLInclAt_comp K _ (fun i j => ?_) (fun i j => ?_)
  · show Continuous fun m : GL (Fin 2) ℝ => (ringEquivRealOfIsReal hw).symm (((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j)
    have hv : Continuous (fun m : GL (Fin 2) ℝ => ((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) := Units.continuous_val
    exact (isometryEquivRealOfIsReal hw).symm.continuous.comp (hv.matrix_elem i j)
  · have : (fun m : GL (Fin 2) ℝ => ((((glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm).toMonoidHom m)⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j) =
        fun m : GL (Fin 2) ℝ => (ringEquivRealOfIsReal hw).symm (((m⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
      funext m; rw [← map_inv]; rfl
    rw [this]
    have hi : Continuous (fun m : GL (Fin 2) ℝ => (((m⁻¹ : GL (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)) := Units.continuous_coe_inv
    exact (isometryEquivRealOfIsReal hw).symm.continuous.comp (hi.matrix_elem i j)

theorem continuous_archComplexGLAt {w : InfinitePlace K} (hw : w.IsComplex) : Continuous (archComplexGLAt (F := K) hw) := by
  have hdef : archComplexGLAt (F := K) hw = (adelicArchGLInclAt K w).comp (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm).toMonoidHom := rfl
  rw [hdef, MonoidHom.coe_comp]
  refine continuous_adelicArchGLInclAt_comp K _ (fun i j => ?_) (fun i j => ?_)
  · show Continuous fun m : GL (Fin 2) ℂ => (ringEquivComplexOfIsComplex hw).symm (((m : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j)
    have hv : Continuous (fun m : GL (Fin 2) ℂ => ((m : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) := Units.continuous_val
    exact (isometryEquivComplexOfIsComplex hw).symm.continuous.comp (hv.matrix_elem i j)
  · have : (fun m : GL (Fin 2) ℂ => ((((glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm).toMonoidHom m)⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j) =
        fun m : GL (Fin 2) ℂ => (ringEquivComplexOfIsComplex hw).symm (((m⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j) := by
      funext m; rw [← map_inv]; rfl
    rw [this]
    have hi : Continuous (fun m : GL (Fin 2) ℂ => (((m⁻¹ : GL (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)) := Units.continuous_coe_inv
    exact (isometryEquivComplexOfIsComplex hw).symm.continuous.comp (hi.matrix_elem i j)

theorem continuous_scalarUnit_real : Continuous fun a : ℝ =>
    Units.map (Matrix.scalar (Fin 2) : ℝ →+* Matrix (Fin 2) (Fin 2) ℝ).toMonoidHom (Units.mk0 (Real.exp a) (Real.exp_ne_zero a)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    show Continuous fun a : ℝ => (Matrix.scalar (Fin 2) (Real.exp a)) i j
    by_cases hij : i = j
    · subst hij; simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq]; exact Real.continuous_exp
    · simp only [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]; exact continuous_const
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    have : ∀ a : ℝ, (((Units.map (Matrix.scalar (Fin 2) : ℝ →+* Matrix (Fin 2) (Fin 2) ℝ).toMonoidHom (Units.mk0 (Real.exp a) (Real.exp_ne_zero a)))⁻¹ :
        GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = (Matrix.scalar (Fin 2) (Real.exp (-a))) i j := by
      intro a
      rw [← map_inv]
      show (Matrix.scalar (Fin 2) (((Units.mk0 (Real.exp a) (Real.exp_ne_zero a))⁻¹ : ℝˣ) : ℝ)) i j = _
      congr 2
      rw [Units.val_inv_eq_inv_val, Real.exp_neg]; rfl
    simp_rw [this]
    by_cases hij : i = j
    · subst hij; simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq]; exact Real.continuous_exp.comp continuous_neg
    · simp only [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]; exact continuous_const

theorem continuous_scalarUnit_complex : Continuous fun b : ℂ =>
    Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom (Units.mk0 (Complex.exp b) (Complex.exp_ne_zero b)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    show Continuous fun b : ℂ => (Matrix.scalar (Fin 2) (Complex.exp b)) i j
    by_cases hij : i = j
    · subst hij; simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq]; exact Complex.continuous_exp
    · simp only [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]; exact continuous_const
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    have : ∀ b : ℂ, (((Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom (Units.mk0 (Complex.exp b) (Complex.exp_ne_zero b)))⁻¹ :
        GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j = (Matrix.scalar (Fin 2) (Complex.exp (-b))) i j := by
      intro b
      rw [← map_inv]
      show (Matrix.scalar (Fin 2) (((Units.mk0 (Complex.exp b) (Complex.exp_ne_zero b))⁻¹ : ℂˣ) : ℂ)) i j = _
      congr 2
      rw [Units.val_inv_eq_inv_val, Complex.exp_neg]; rfl
    simp_rw [this]
    by_cases hij : i = j
    · subst hij; simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq]; exact Complex.continuous_exp.comp continuous_neg
    · simp only [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]; exact continuous_const

theorem continuous_sR (w : {w : InfinitePlace K // w.IsReal}) : Continuous (sR K w) := by
  unfold sR
  exact (continuous_archRealGLAt K w.2).comp (continuous_scalarUnit_real)

theorem continuous_sC (w : {w : InfinitePlace K // w.IsComplex}) : Continuous (sC K w) := by
  unfold sC
  exact (continuous_archComplexGLAt K w.2).comp (continuous_scalarUnit_complex)

theorem le_apply_mul_list_prod (G : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (κ : ℝ≥0∞) :
    ∀ (L : List (AdelicGL2 (𝓞 K) K)), (∀ s ∈ L, ∀ y, κ * G y ≤ G (y * s)) →
      ∀ y, κ ^ L.length * G y ≤ G (y * L.prod)
  | [], _, y => by simp
  | s :: L, h, y => by
    rw [List.prod_cons, List.length_cons, pow_succ, ← mul_assoc y]
    have h1 := h s List.mem_cons_self y
    have h2 := le_apply_mul_list_prod G κ L (fun s' hs' => h s' (List.mem_cons_of_mem _ hs')) (y * s)
    calc κ ^ L.length * κ * G y = κ ^ L.length * (κ * G y) := by ring
      _ ≤ κ ^ L.length * G (y * s) := mul_le_mul_right h1 _
      _ ≤ G (y * s * L.prod) := h2

theorem exp_mem_collar {a ℓ : ℝ} (hℓ : ℓ ≤ 1 / 4) (ha : a ∈ Set.Icc (-ℓ) ℓ) : Real.exp a ∈ Set.Icc (1 / 2 : ℝ) 2 := by
  have h1 : |a| ≤ 1 / 4 := abs_le.mpr ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have h2 := Real.abs_exp_sub_one_le (x := a) (by linarith)
  have h3 := abs_le.mp h2
  constructor <;> linarith [h3.1, h3.2]

theorem cexp_mem_collar {b : ℂ} {ℓ : ℝ} (hℓ : ℓ ≤ 1 / 4) (hb : b ∈ Metric.closedBall (0 : ℂ) ℓ) :
    ‖((Units.mk0 (Complex.exp b) (Complex.exp_ne_zero b) : ℂˣ) : ℂ) - 1‖ ≤ 1 / 2 := by
  have hb' : ‖b‖ ≤ ℓ := by simpa using hb
  have h := Complex.norm_exp_sub_one_le (x := b) (by linarith)
  show ‖Complex.exp b - 1‖ ≤ 1 / 2
  linarith

end Assembly
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_lintegral_comp_flowChart_le_mul_lintegral_of_forall_mul_eq.H3Proof"

end H3Proof
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_lintegral_comp_flowChart_le_mul_lintegral_of_forall_mul_eq.H3Proof"

namespace H3Proof
section Final
open NumberField.InfinitePlace.Completion
variable (K : Type) [Field K] [NumberField K]
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

theorem card_infinitePlace_eq :
    Fintype.card (InfinitePlace K) =
      (Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).toList.length +
        (Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).toList.length := by
  rw [Finset.length_toList, Finset.length_toList, Finset.card_univ, Finset.card_univ]
  have h1 : Fintype.card {w : InfinitePlace K // w.IsComplex} = Fintype.card {w : InfinitePlace K // ¬ w.IsReal} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun w => (not_isReal_iff_isComplex (w := w)).symm)
  rw [h1, Fintype.card_subtype_compl, ← Nat.add_sub_assoc (Fintype.card_subtype_le _), Nat.add_sub_cancel_left]

theorem volume_abox_pos_lt_top (ℓ : ℝ) (hℓ : 0 < ℓ) :
    0 < (volume : Measure (({w : InfinitePlace K // w.IsReal} → ℝ) × ({w : InfinitePlace K // w.IsComplex} → ℂ)))
        ((Set.pi Set.univ fun _ => Set.Icc (-ℓ) ℓ) ×ˢ (Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) ℓ)) ∧
    (volume : Measure (({w : InfinitePlace K // w.IsReal} → ℝ) × ({w : InfinitePlace K // w.IsComplex} → ℂ)))
        ((Set.pi Set.univ fun _ => Set.Icc (-ℓ) ℓ) ×ˢ (Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) ℓ)) < ⊤ := by
  constructor
  · rw [show (volume : Measure (({w : InfinitePlace K // w.IsReal} → ℝ) × ({w : InfinitePlace K // w.IsComplex} → ℂ))) =
        (volume : Measure ({w : InfinitePlace K // w.IsReal} → ℝ)).prod volume from rfl, Measure.prod_prod]
    refine ENNReal.mul_pos ?_ ?_
    · have hsub : (Set.pi Set.univ fun _ : {w : InfinitePlace K // w.IsReal} => Set.Ioo (-ℓ) ℓ) ⊆
          Set.pi Set.univ fun _ : {w : InfinitePlace K // w.IsReal} => Set.Icc (-ℓ) ℓ := Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self
      have hpos := IsOpen.measure_pos (volume : Measure ({w : InfinitePlace K // w.IsReal} → ℝ))
        (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo) ⟨fun _ => 0, fun i _ => show (0 : ℝ) ∈ Set.Ioo (-ℓ) ℓ from ⟨by linarith, hℓ⟩⟩
      exact (hpos.trans_le (measure_mono hsub)).ne'
    · have hsub : (Set.pi Set.univ fun _ : {w : InfinitePlace K // w.IsComplex} => Metric.ball (0 : ℂ) ℓ) ⊆
          Set.pi Set.univ fun _ : {w : InfinitePlace K // w.IsComplex} => Metric.closedBall (0 : ℂ) ℓ :=
        Set.pi_mono fun _ _ => Metric.ball_subset_closedBall
      have hpos := IsOpen.measure_pos (volume : Measure ({w : InfinitePlace K // w.IsComplex} → ℂ))
        (isOpen_set_pi Set.finite_univ fun _ _ => Metric.isOpen_ball) ⟨fun _ => 0, fun i _ => show (0 : ℂ) ∈ Metric.ball (0 : ℂ) ℓ from Metric.mem_ball_self hℓ⟩
      exact (hpos.trans_le (measure_mono hsub)).ne'
  · exact ((isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_closedBall _ _)).measure_lt_top

end Final
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_lintegral_comp_flowChart_le_mul_lintegral_of_forall_mul_eq.H3Proof"
end H3Proof
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_lintegral_comp_flowChart_le_mul_lintegral_of_forall_mul_eq.H3Proof"

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

open H3Proof in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (L₀ : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)))
    (hL₀ : L₀.Nodup) (hL₀' : ∀ d, d ∈ L₀) :
    let flow : ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) → ℝ → AdelicGL2 (𝓞 K) K :=
      fun d t => Sum.elim (fun d => archFlowAt d.2.1 d.2.2 t) (fun d => archFlowAtComplex d.2.1 d.2.2 t) d
    let chart : (Fin L₀.length → ℝ) → AdelicGL2 (𝓞 K) K :=
      fun t => (List.ofFn fun j => flow (L₀.get j) (t j)).prod
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ Θ : Set (AdelicGL2 (𝓞 K) K), IsCompact Θ ∧ ∃ c : NNReal,
      ∀ (x : AdelicGL2 (𝓞 K) K) (κ : ENNReal) (G : AdelicGL2 (𝓞 K) K → ENNReal), Measurable G →
        (∀ y : AdelicGL2 (𝓞 K) K, ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, G (y * u) = G y) →
        (∀ (y : AdelicGL2 (𝓞 K) K) (w : InfinitePlace K) (hw : w.IsReal) (t : ℝˣ), (t : ℝ) ∈ Set.Icc (1 / 2) 2 →
          κ * G y ≤ G (y * archRealGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℝ →+* Matrix (Fin 2) (Fin 2) ℝ).toMonoidHom t))) →
        (∀ (y : AdelicGL2 (𝓞 K) K) (w : InfinitePlace K) (hw : w.IsComplex) (z : ℂˣ), ‖(z : ℂ) - 1‖ ≤ 1 / 2 →
          κ * G y ≤ G (y * archComplexGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom z))) →
        κ ^ Fintype.card (InfinitePlace K) *
            ∫⁻ t in Set.pi Set.univ (fun _ : Fin L₀.length => Set.Icc (-ℓ) ℓ), G (x * chart t) ≤
          (c : ENNReal) * ∫⁻ y in (fun θ => x * θ) '' Θ, G y ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  intro flow chart
  classical

  obtain ⟨μa, hμa, hreg, ℓ, hℓ, hℓ4, S, hS, c₁, hH2⟩ :=
    AutomorphicForm.exists_isHaarMeasure_lintegral_comp_glArch_flowChart_mul_le K L₀ hL₀ hL₀'
  haveI := hμa
  haveI := hreg
  obtain ⟨μf, hμf, c₀, hc₀, hPF⟩ := product_formula K μa
  haveI := hμf

  set U : Set (AdelicGL2 (𝓞 K) K) :=
    ((principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)) with hU
  set Uf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := glFin (𝓞 K) K '' U with hUf
  have hUc : IsCompact U := AutomorphicForm.isCompact_principalLevel_inf_finiteAdelicGL2Subgroup K N
  have hUfc : IsCompact Uf := hUc.image (continuous_glFin (𝓞 K) K)
  have hUf_iff : ∀ z : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K), z ∈ Uf ↔ bwd (Fin 2) K (1, z) ∈ (principalLevel (𝓞 K) K N : Set (AdelicGL2 (𝓞 K) K)) := by
    intro z
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu' := Subgroup.mem_inf.mp hu
      have h1 : glArch (𝓞 K) K u = 1 := (mem_finiteAdelicGL2Subgroup_iff K u).mp hu'.2
      rw [← eq_bwd_one_glFin_of_glArch_eq_one K h1]
      exact hu'.1
    · intro hz
      refine ⟨bwd (Fin 2) K (1, z), Subgroup.mem_inf.mpr ⟨hz, ?_⟩, glFin_bwd K _⟩
      exact (mem_finiteAdelicGL2Subgroup_iff K _).mpr (glArch_bwd K _)
  have hUfo : IsOpen Uf := by
    have : Uf = (fun z => bwd (Fin 2) K (1, z)) ⁻¹' (principalLevel (𝓞 K) K N : Set (AdelicGL2 (𝓞 K) K)) :=
      Set.ext fun z => hUf_iff z
    rw [this]
    exact (AutomorphicForm.isOpen_principalLevel K N hN).preimage
      ((continuous_bwd (Fin 2) K).comp (continuous_const.prodMk continuous_id))
  have hUf1 : (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) ∈ Uf := by
    rw [hUf_iff]; simpa [show ((1 : GL (Fin 2) (InfiniteAdeleRing K)), (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) = (1 : _ × _) from rfl,
      show bwd (Fin 2) K 1 = 1 from map_one (splitMulEquiv (Fin 2) K).symm] using (principalLevel (𝓞 K) K N).one_mem
  have hμUf_pos : 0 < μf Uf := hUfo.measure_pos μf ⟨1, hUf1⟩
  have hμUf_top : μf Uf < ⊤ := hUfc.measure_lt_top
  obtain ⟨hvab_pos, hvab_top⟩ := volume_abox_pos_lt_top K ℓ hℓ
  set abox : Set (({w : InfinitePlace K // w.IsReal} → ℝ) × ({w : InfinitePlace K // w.IsComplex} → ℂ)) :=
    (Set.pi Set.univ fun _ => Set.Icc (-ℓ) ℓ) ×ˢ (Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) ℓ) with habox
  set tbox : Set (Fin L₀.length → ℝ) := Set.pi Set.univ fun _ => Set.Icc (-ℓ) ℓ with htbox
  have htboxm : MeasurableSet tbox := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have haboxm : MeasurableSet abox :=
    (MeasurableSet.univ_pi fun _ => measurableSet_Icc).prod (MeasurableSet.univ_pi fun _ => Metric.isClosed_closedBall.measurableSet)

  refine ⟨ℓ, hℓ, bwd (Fin 2) K '' (S ×ˢ Uf), (hS.prod hUfc).image (continuous_bwd (Fin 2) K), ?_⟩
  set cE : ℝ≥0∞ := (c₁ : ℝ≥0∞) / ((c₀ : ℝ≥0∞) * μf Uf * volume abox) with hcE
  have hden0 : (c₀ : ℝ≥0∞) * μf Uf * volume abox ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by exact_mod_cast hc₀.ne') hμUf_pos.ne') hvab_pos.ne'
  have hdentop : (c₀ : ℝ≥0∞) * μf Uf * volume abox ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hμUf_top.ne) hvab_top.ne
  have hcEtop : cE ≠ ⊤ := ENNReal.div_ne_top ENNReal.coe_ne_top hden0
  refine ⟨cE.toNNReal, ?_⟩
  intro x κ G hGm hGU hGR hGC
  rw [ENNReal.coe_toNNReal hcEtop]

  have hinv : ∀ (y : AdelicGL2 (𝓞 K) K) (z : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)), z ∈ Uf → G (y * bwd (Fin 2) K (1, z)) = G y := by
    rintro y z ⟨u, hu, rfl⟩
    have h1 : glArch (𝓞 K) K u = 1 := (mem_finiteAdelicGL2Subgroup_iff K u).mp (Subgroup.mem_inf.mp hu).2
    rw [← eq_bwd_one_glFin_of_glArch_eq_one K h1]
    exact hGU y u hu
  have hPF' := hPF x S hS.measurableSet Uf hUfc.measurableSet G hGm hinv

  have hHm : Measurable fun y : GL (Fin 2) (InfiniteAdeleRing K) => G (x * bwd (Fin 2) K (y, 1)) :=
    hGm.comp ((continuous_const.mul ((continuous_bwd (Fin 2) K).comp (continuous_id.prodMk continuous_const))).measurable)
  set scal : ({w : InfinitePlace K // w.IsReal} → ℝ) → ({w : InfinitePlace K // w.IsComplex} → ℂ) → AdelicGL2 (𝓞 K) K :=
    fun a b => ((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).toList.map fun w => sR K w (a w)).prod *
      ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).toList.map fun w => sC K w (b w)).prod with hscal
  have h2 : ∫⁻ v in tbox ×ˢ abox, G (x * bwd (Fin 2) K (glArch (𝓞 K) K (chart v.1 * scal v.2.1 v.2.2), 1)) ≤
      (c₁ : ℝ≥0∞) * ∫⁻ y in S, G (x * bwd (Fin 2) K (y, 1)) ∂μa := hH2 _ hHm

  have hfinchart : ∀ t, glFin (𝓞 K) K (chart t) = 1 := fun t =>
    glFin_list_prod_eq_one K _ fun g hg => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
      exact glFin_flowd K (L₀.get j) (t j)
  have hfinscal : ∀ a b, glFin (𝓞 K) K (scal a b) = 1 := fun a b => by
    rw [hscal, map_mul, glFin_list_prod_eq_one K _ fun g hg => ?_, glFin_list_prod_eq_one K _ fun g hg => ?_, one_mul]
    · obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg; exact glFin_sC K w _
    · obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg; exact glFin_sR K w _
  have h2' : ∫⁻ v in tbox ×ˢ abox, G (x * (chart v.1 * scal v.2.1 v.2.2)) ≤ (c₁ : ℝ≥0∞) * ∫⁻ y in S, G (x * bwd (Fin 2) K (y, 1)) ∂μa := by
    refine le_of_eq_of_le (setLIntegral_congr_fun (htboxm.prod haboxm) fun v _ => ?_) h2
    rw [bwd_glArch_of_glFin_eq_one K (by rw [map_mul, hfinchart, hfinscal, one_mul])]

  have hcollar : ∀ t, ∀ ab ∈ abox, κ ^ Fintype.card (InfinitePlace K) * G (x * chart t) ≤ G (x * (chart t * scal ab.1 ab.2)) := by
    rintro t ⟨a, b⟩ hab
    obtain ⟨ha, hb⟩ := Set.mem_prod.mp hab
    have hRlist := le_apply_mul_list_prod K G κ ((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).toList.map fun w => sR K w (a w))
      (fun s hs y => by
        obtain ⟨w, -, rfl⟩ := List.mem_map.mp hs
        exact hGR y w.1 w.2 _ (exp_mem_collar hℓ4 ((Set.mem_univ_pi.mp ha) w)))
    have hClist := le_apply_mul_list_prod K G κ ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).toList.map fun w => sC K w (b w))
      (fun s hs y => by
        obtain ⟨w, -, rfl⟩ := List.mem_map.mp hs
        exact hGC y w.1 w.2 _ (cexp_mem_collar hℓ4 ((Set.mem_univ_pi.mp hb) w)))
    rw [card_infinitePlace_eq K, pow_add]
    calc κ ^ (Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).toList.length *
          κ ^ (Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).toList.length * G (x * chart t)
        = κ ^ ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).toList.map fun w => sC K w (b w)).length *
          (κ ^ ((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).toList.map fun w => sR K w (a w)).length * G (x * chart t)) := by
          rw [List.length_map, List.length_map]; ring
      _ ≤ κ ^ ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).toList.map fun w => sC K w (b w)).length *
          G (x * chart t * ((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).toList.map fun w => sR K w (a w)).prod) :=
          mul_le_mul_right (hRlist _) _
      _ ≤ G (x * chart t * ((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).toList.map fun w => sR K w (a w)).prod *
          ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).toList.map fun w => sC K w (b w)).prod) := hClist _
      _ = G (x * (chart t * scal a b)) := by simp only [hscal, mul_assoc]
  have hchartm : Measurable fun t : Fin L₀.length → ℝ => G (x * chart t) := by
    refine hGm.comp ((continuous_const.mul ?_).measurable)
    have : chart = fun t => (((List.finRange L₀.length).map fun j => flowd K (L₀.get j) (t j))).prod := by
      funext t
      show (List.ofFn fun j => flow (L₀.get j) (t j)).prod = _
      rw [List.ofFn_eq_map]; rfl
    rw [this]
    exact continuous_list_prod _ fun j _ => (continuous_flowd K _).comp (continuous_apply j)
  have h3 : κ ^ Fintype.card (InfinitePlace K) * volume abox * ∫⁻ t in tbox, G (x * chart t) ≤
      ∫⁻ v in tbox ×ˢ abox, G (x * (chart v.1 * scal v.2.1 v.2.2)) := by
    have hvol : (volume : Measure ((Fin L₀.length → ℝ) × (({w : InfinitePlace K // w.IsReal} → ℝ) × ({w : InfinitePlace K // w.IsComplex} → ℂ)))) =
        (volume : Measure (Fin L₀.length → ℝ)).prod volume := rfl
    have hpm := lintegral_prod_mul (μ := (volume : Measure (Fin L₀.length → ℝ)).restrict tbox)
      (ν := (volume : Measure (({w : InfinitePlace K // w.IsReal} → ℝ) × ({w : InfinitePlace K // w.IsComplex} → ℂ))).restrict abox)
      (f := fun t => κ ^ Fintype.card (InfinitePlace K) * G (x * chart t)) (g := fun _ => (1 : ℝ≥0∞))
      ((measurable_const.mul hchartm).aemeasurable) aemeasurable_const
    rw [lintegral_const, Measure.restrict_apply_univ] at hpm
    simp only [mul_one] at hpm ⊢
    calc κ ^ Fintype.card (InfinitePlace K) * volume abox * ∫⁻ t in tbox, G (x * chart t)
        = ∫⁻ v in tbox ×ˢ abox, κ ^ Fintype.card (InfinitePlace K) * G (x * chart v.1) := by
          rw [hvol, ← Measure.prod_restrict, hpm, lintegral_const_mul _ hchartm]
          ring
      _ ≤ ∫⁻ v in tbox ×ˢ abox, G (x * (chart v.1 * scal v.2.1 v.2.2)) :=
          setLIntegral_mono' (htboxm.prod haboxm) fun v hv => hcollar v.1 v.2 (Set.mem_prod.mp hv).2

  have hmain : κ ^ Fintype.card (InfinitePlace K) * volume abox * ∫⁻ t in tbox, G (x * chart t) ≤
      (c₁ : ℝ≥0∞) * ∫⁻ y in S, G (x * bwd (Fin 2) K (y, 1)) ∂μa := h3.trans h2'
  rw [hPF']

  have hIS : (c₁ : ℝ≥0∞) * ∫⁻ y in S, G (x * bwd (Fin 2) K (y, 1)) ∂μa =
      volume abox * (cE * ((c₀ : ℝ≥0∞) * μf Uf * ∫⁻ y in S, G (x * bwd (Fin 2) K (y, 1)) ∂μa)) := by
    rw [hcE]
    have : volume abox * ((c₁ : ℝ≥0∞) / ((c₀ : ℝ≥0∞) * μf Uf * volume abox) * ((c₀ : ℝ≥0∞) * μf Uf * ∫⁻ y in S, G (x * bwd (Fin 2) K (y, 1)) ∂μa)) =
        (c₁ : ℝ≥0∞) * (((c₀ : ℝ≥0∞) * μf Uf * volume abox) / ((c₀ : ℝ≥0∞) * μf Uf * volume abox)) *
          ∫⁻ y in S, G (x * bwd (Fin 2) K (y, 1)) ∂μa := by
      rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]; ring
    rw [this, ENNReal.div_self hden0 hdentop, mul_one]
  rw [hIS] at hmain
  have hv0 : volume abox ≠ 0 := hvab_pos.ne'
  have hvt : volume abox ≠ ⊤ := hvab_top.ne
  calc κ ^ Fintype.card (InfinitePlace K) * ∫⁻ t in tbox, G (x * chart t)
      = (volume abox)⁻¹ * (κ ^ Fintype.card (InfinitePlace K) * volume abox * ∫⁻ t in tbox, G (x * chart t)) := by
        rw [show κ ^ Fintype.card (InfinitePlace K) * volume abox * ∫⁻ t in tbox, G (x * chart t) =
          volume abox * (κ ^ Fintype.card (InfinitePlace K) * ∫⁻ t in tbox, G (x * chart t)) by ring,
          ← mul_assoc, ENNReal.inv_mul_cancel hv0 hvt, one_mul]
    _ ≤ (volume abox)⁻¹ * (volume abox * (cE * ((c₀ : ℝ≥0∞) * μf Uf * ∫⁻ y in S, G (x * bwd (Fin 2) K (y, 1)) ∂μa))) :=
        mul_le_mul_right hmain _
    _ = cE * ((c₀ : ℝ≥0∞) * μf Uf * ∫⁻ y in S, G (x * bwd (Fin 2) K (y, 1)) ∂μa) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hv0 hvt, one_mul]

end
end S_AutomorphicForm_exists_forall_lintegral_comp_flowChart_le_mul_lintegral_of_forall_mul_eq
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_lintegral_comp_flowChart_le_mul_lintegral_of_forall_mul_eq (solution)
