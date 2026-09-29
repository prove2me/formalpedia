-- Prove2me | solution 1 for AutomorphicForm.exists_isTwistedWeightedOrbitalIntegralOn_baseChange_eq_mul_sum_prod_of_isSemiLocalFactorization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/63ae5fa8-b40d-58c6-8105-84cc52f1a28a

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Theorems.Thm_AutomorphicForm_exists_finset_forall_isTwistedSectionFnOn_indicator_semiLocalIntegralSet_of_isTwistedSectionFnOn_baseChange
import Theorems.Thm_AutomorphicForm_isTwistedSectionFnOn_baseChange_indicator_prod_of_forall_isTwistedSectionFnOn
import Theorems.Thm_MeasureTheory_exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul
import Theorems.Thm_MeasureTheory_integrable_and_integral_mul_mul_eq_of_integral_subgroup_translate_eq_one_of_continuous
import Theorems.Thm_AutomorphicForm_exists_finset_mem_nhds_forall_tensorPlace_mem_semiLocalIntegralSet
import Theorems.Thm_AutomorphicForm_exists_tensorArch_eq_and_forall_tensorPlace_eq_of_finset
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isTwistedWeightedOrbitalIntegralOn_baseChange_eq_mul_sum_prod_of_isSemiLocalFactorization
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter
open NumberField.AdelicLevel NumberField.AdelicHaar TensorProduct
open scoped TensorProduct.RightActions NNReal ENNReal Pointwise Classical

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "tensorArch tensorPlace baseChangeGL glArch_baseChangeGL semiLocalComponent_glFin_baseChangeGL tensorArch_sigmaGL tensorPlace_sigmaGL continuous_glMap baseChangeGLEquiv archIdentGLEquiv continuous_tensorArch continuous_tensorPlace isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf semiLocalHomeomorph semiLocalIntegers semiLocalIntegers_eq_preimage zero_mem_semiLocalIntegers semiLocalIntegralSet isOpen_semiLocalIntegralSet semiLocalHaar semiLocalHaar_semiLocalIntegralSet sigmaTensor sigmaGL normString twistedCentralizer twistedCentralizerBorel IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn IsTwistedOrbitalIntegral archIdentGL semiLocalComponent IsSemiLocalFactorization integralUnitsSet IsRegularSemisimple archEntries IsArchTestFactor mem_sigmaCentralizer_iff mem_sigmaCentralizer_iff_inv LocalWeight.weight IsTwistedWeightedOrbitalIntegralOn semiLocalPlaceComponent semiLocalWeight IsTwistedWeightedOrbitalIntegral exists_finset_forall_isTwistedSectionFnOn_indicator_semiLocalIntegralSet_of_isTwistedSectionFnOn_baseChange isTwistedSectionFnOn_baseChange_indicator_prod_of_forall_isTwistedSectionFnOn exists_finset_mem_nhds_forall_tensorPlace_mem_semiLocalIntegralSet exists_tensorArch_eq_and_forall_tensorPlace_eq_of_finset"
namespace TwistedWeightedEuler
p2m_open "AutomorphicForm"

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev Garch (L : Type) [Field L] [NumberField L] : Type := GL (Fin 2) (InfiniteAdeleRing L)

abbrev Gfin (L : Type) [Field L] [NumberField L] : Type := GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)

abbrev Gad (L : Type) [Field L] [NumberField L] : Type := GL (Fin 2) (AdeleRing (𝓞 L) L)

abbrev SL (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Type :=
  L ⊗[K] v.adicCompletion K

abbrev Gsl (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Type :=
  GL (Fin 2) (SL K L v)

abbrev Gt (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] : Type :=
  GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)

abbrev Ht (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] : Type :=
  GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)

section Instances

scoped instance instSecondCountableCompletion (w : InfinitePlace L) : SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

scoped instance instSecondCountableInfiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing L) :=
  show SecondCountableTopology ((w : InfinitePlace L) → w.Completion) from inferInstance

scoped instance instSecondCountableMulOpposite (X : Type*) [TopologicalSpace X] [Mul X]
    [SecondCountableTopology X] : SecondCountableTopology Xᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

theorem secondCountable_gl (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [SecondCountableTopology A] : SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  exact Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance instSecondCountableGarch : SecondCountableTopology (Garch L) := secondCountable_gl _

scoped instance instIsTopologicalRingSL (v : HeightOneSpectrum (𝓞 K)) : IsTopologicalRing (SL K L v) :=
  isTopologicalRing_tensor K L _
scoped instance instT2SL (v : HeightOneSpectrum (𝓞 K)) : T2Space (SL K L v) := t2Space_tensor K L _
scoped instance instLocallyCompactSL (v : HeightOneSpectrum (𝓞 K)) : LocallyCompactSpace (SL K L v) :=
  locallyCompactSpace_tensor K L _
scoped instance instFiniteExtension (v : HeightOneSpectrum (𝓞 K)) : Finite (v.Extension (𝓞 L)) :=
  HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
scoped instance instSecondCountableSL (v : HeightOneSpectrum (𝓞 K)) : SecondCountableTopology (SL K L v) :=
  (semiLocalHomeomorph K L v).secondCountableTopology
scoped instance instSecondCountableGsl (v : HeightOneSpectrum (𝓞 K)) : SecondCountableTopology (Gsl K L v) :=
  secondCountable_gl _
scoped instance instLocallyCompactGsl (v : HeightOneSpectrum (𝓞 K)) : LocallyCompactSpace (Gsl K L v) :=
  locallyCompactSpace_tensorGL K L _
scoped instance instIsTopologicalGroupGsl (v : HeightOneSpectrum (𝓞 K)) : IsTopologicalGroup (Gsl K L v) :=
  isTopologicalGroup_tensorGL K L _

scoped instance instIsTopologicalRingTA : IsTopologicalRing (L ⊗[K] AdeleRing (𝓞 K) K) :=
  isTopologicalRing_tensor K L _
scoped instance instT2TA : T2Space (L ⊗[K] AdeleRing (𝓞 K) K) := t2Space_tensor K L _
scoped instance instIsTopologicalGroupGt : IsTopologicalGroup (Gt K L) := isTopologicalGroup_tensorGL K L _

scoped instance instIsTopologicalRingTI : IsTopologicalRing (L ⊗[K] InfiniteAdeleRing K) :=
  isTopologicalRing_tensor K L _
scoped instance instT2TI : T2Space (L ⊗[K] InfiniteAdeleRing K) := t2Space_tensor K L _
scoped instance instLocallyCompactTI : LocallyCompactSpace (L ⊗[K] InfiniteAdeleRing K) :=
  locallyCompactSpace_tensor K L _
scoped instance instIsTopologicalGroupHt : IsTopologicalGroup (Ht K L) := isTopologicalGroup_tensorGL K L _
scoped instance instLocallyCompactHt : LocallyCompactSpace (Ht K L) := locallyCompactSpace_tensorGL K L _
scoped instance instSecondCountableHt : SecondCountableTopology (Ht K L) :=
  (archIdentGLEquiv K L).toHomeomorph.secondCountableTopology

scoped instance instMeasurableSpaceHt : MeasurableSpace (Ht K L) := borel _
scoped instance instBorelSpaceHt : BorelSpace (Ht K L) := ⟨rfl⟩
scoped instance instMeasurableSpaceGsl (v : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (Gsl K L v) := borel _
scoped instance instBorelSpaceGsl (v : HeightOneSpectrum (𝓞 K)) : BorelSpace (Gsl K L v) := ⟨rfl⟩
scoped instance instMeasurableSpaceGt : MeasurableSpace (Gt K L) := borel _
scoped instance instBorelSpaceGt : BorelSpace (Gt K L) := ⟨rfl⟩

scoped instance instT2Ht : T2Space (Ht K L) := t2Space_tensorGL K L _
scoped instance instT2Gsl (v : HeightOneSpectrum (𝓞 K)) : T2Space (Gsl K L v) := t2Space_tensorGL K L _
scoped instance instT2Gt : T2Space (Gt K L) := t2Space_tensorGL K L _
scoped instance instLocallyCompactTA : LocallyCompactSpace (L ⊗[K] AdeleRing (𝓞 K) K) := locallyCompactSpace_tensor K L _

end Instances

section IntegralSubgroup

variable {A : Type*} [CommRing A]

theorem mul_mem_integralUnitsSet (U : Subring A) {g h : GL (Fin 2) A}
    (hg : g ∈ integralUnitsSet (U : Set A)) (hh : h ∈ integralUnitsSet (U : Set A)) :
    g * h ∈ integralUnitsSet (U : Set A) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    exact U.sum_mem fun k _ => U.mul_mem (hg.1 i k) (hh.1 k j)
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    exact U.sum_mem fun k _ => U.mul_mem (hh.2 i k) (hg.2 k j)

theorem inv_mem_integralUnitsSet (U : Set A) {g : GL (Fin 2) A} (hg : g ∈ integralUnitsSet U) :
    g⁻¹ ∈ integralUnitsSet U :=
  ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

end IntegralSubgroup

def semiLocalSubring (v : HeightOneSpectrum (𝓞 K)) : Subring (SL K L v) :=
  (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).toRingHom.range

theorem coe_semiLocalSubring (v : HeightOneSpectrum (𝓞 K)) :
    (semiLocalSubring (K := K) (L := L) v : Set (SL K L v)) = semiLocalIntegers K L v := by
  ext x
  simp only [semiLocalSubring, RingHom.coe_range, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    semiLocalIntegers, Set.mem_range]

theorem mul_mem_semiLocalIntegralSet (v : HeightOneSpectrum (𝓞 K)) {g h : Gsl K L v}
    (hg : g ∈ semiLocalIntegralSet K L v) (hh : h ∈ semiLocalIntegralSet K L v) :
    g * h ∈ semiLocalIntegralSet K L v := by
  have h' := mul_mem_integralUnitsSet (semiLocalSubring (K := K) (L := L) v)
    (by rw [coe_semiLocalSubring]; exact hg) (by rw [coe_semiLocalSubring]; exact hh)
  rwa [coe_semiLocalSubring] at h'

theorem inv_mem_semiLocalIntegralSet (v : HeightOneSpectrum (𝓞 K)) {g : Gsl K L v}
    (hg : g ∈ semiLocalIntegralSet K L v) : g⁻¹ ∈ semiLocalIntegralSet K L v :=
  inv_mem_integralUnitsSet _ hg

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

section More

scoped instance (priority := 10000) instMeasurableSpaceSubgroupGt (H : Subgroup (Gt K L)) : MeasurableSpace H :=
  borel _
scoped instance instBorelSpaceSubgroupGt (H : Subgroup (Gt K L)) : BorelSpace H := ⟨rfl⟩
scoped instance (priority := 10000) instMeasurableSpaceSubgroupHt (H : Subgroup (Ht K L)) : MeasurableSpace H :=
  borel _
scoped instance instBorelSpaceSubgroupHt (H : Subgroup (Ht K L)) : BorelSpace H := ⟨rfl⟩
scoped instance (priority := 10000) instMeasurableSpaceSubgroupGsl (v : HeightOneSpectrum (𝓞 K))
    (H : Subgroup (Gsl K L v)) : MeasurableSpace H := borel _
scoped instance instBorelSpaceSubgroupGsl (v : HeightOneSpectrum (𝓞 K)) (H : Subgroup (Gsl K L v)) :
    BorelSpace H := ⟨rfl⟩

end More

section Regular

variable {A : Type*} [CommRing A]

theorem entries_of_commute (g X : Matrix (Fin 2) (Fin 2) A) (h : X * g = g * X) (u : A)
    (hu : u * (Matrix.trace g ^ 2 - 4 * Matrix.det g) = 1) :
    ∃ α β : A, X = α • (1 : Matrix (Fin 2) (Fin 2) A) + β • g := by
  rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hu
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  let B : A := u * (2 * g 1 0 * X 0 1 + 2 * g 0 1 * X 1 0 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1))
  refine ⟨X 0 0 - B * g 0 0, B, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, B, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, if_true, one_ne_zero, zero_ne_one, if_false, mul_one, mul_zero, zero_add]
  · ring
  · linear_combination (-(X 0 1)) * hu - (u * (g 0 0 - g 1 1)) * e01 + (2 * u * g 0 1) * e00
  · linear_combination (-(X 1 0)) * hu + (u * (g 0 0 - g 1 1)) * e10 - (2 * u * g 1 0) * e00
  · linear_combination (X 0 0 - X 1 1) * hu - (2 * u * g 1 0) * e01 + (2 * u * g 0 1) * e10

theorem mul_comm_of_mem_centralizer {g : GL (Fin 2) A} (hg : IsRegularSemisimple g) {s z : GL (Fin 2) A}
    (hs : s ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) A)))
    (hz : z ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) A))) : s * z = z * s := by
  obtain ⟨u, hu⟩ := hg.exists_left_inv
  rw [Subgroup.mem_centralizer_singleton_iff] at hs hz
  have hs' : (s : Matrix (Fin 2) (Fin 2) A) * g = g * s := by rw [← Units.val_mul, hs, Units.val_mul]
  have hz' : (z : Matrix (Fin 2) (Fin 2) A) * g = g * z := by rw [← Units.val_mul, hz, Units.val_mul]
  obtain ⟨α, β, hS⟩ := entries_of_commute _ _ hs' u hu
  obtain ⟨α', β', hZ⟩ := entries_of_commute _ _ hz' u hu
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hS, hZ]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_add, smul_smul]
  rw [mul_comm α' α, mul_comm α' β, mul_comm β' α, mul_comm β' β]
  abel

theorem isRegularSemisimple_map {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T)
    {g : GL (Fin 2) R} (hg : IsRegularSemisimple g) :
    IsRegularSemisimple (Matrix.GeneralLinearGroup.map f g) := by
  unfold IsRegularSemisimple at hg ⊢
  have hval : ((Matrix.GeneralLinearGroup.map f g : GL (Fin 2) T) : Matrix (Fin 2) (Fin 2) T) =
      f.mapMatrix (g : Matrix (Fin 2) (Fin 2) R) := rfl
  rw [hval, ← RingHom.map_det, RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace]
  have := hg.map f
  simpa [map_ofNat] using this

theorem isMulRightInvariant_of_comm {G : Type*} [Group G] (T : Subgroup G) (hcomm : ∀ s t : T, s * t = t * s)
    [MeasurableSpace T] (τ : Measure T) [τ.IsMulLeftInvariant] : τ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have : (fun t : T => t * g) = fun t : T => g * t := funext fun t => hcomm t g
  rw [this]
  exact map_mul_left_eq_self τ g

theorem continuous_twistedConj {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (g : G)
    (s : G →* G) (hs : Continuous s) : Continuous fun x : G => x⁻¹ * g * s x :=
  (continuous_id.inv.mul continuous_const).mul hs

end Regular

section Twist

variable (K L) (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)

omit [NumberField K] [NumberField L] in
theorem map_normString {B : Type} [CommRing B] [Algebra K B] (F : GL (Fin 2) (L ⊗[K] A) →* GL (Fin 2) (L ⊗[K] B))
    (hF : ∀ x, F (sigmaGL K L A σ x) = sigmaGL K L B σ (F x)) (δ : GL (Fin 2) (L ⊗[K] A)) :
    F (normString K L A σ δ) = normString K L B σ (F δ) := by
  unfold normString
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  show F ((sigmaGL K L A σ)^[i] δ) = (sigmaGL K L B σ)^[i] (F δ)
  exact (Function.Semiconj.iterate_right (f := F) (ga := sigmaGL K L A σ) (gb := sigmaGL K L B σ) hF i δ)

omit [NumberField K] [NumberField L] in
theorem sigmaTensor_iterate (k : ℕ) (y : L ⊗[K] A) :
    (sigmaTensor K L A σ)^[k] y = Algebra.TensorProduct.map (σ ^ k).toAlgHom (AlgHom.id K A) y := by
  induction k generalizing y with
  | zero =>
      simp only [Function.iterate_zero, id_eq, pow_zero]
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [Algebra.TensorProduct.map_tmul]
      | add x y hx hy => rw [map_add, ← hx, ← hy]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
          simp [sigmaTensor, Algebra.TensorProduct.map_tmul, pow_succ', AlgEquiv.mul_apply]
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

omit [NumberField K] [NumberField L] in
theorem sigmaGL_iterate_finrank (hσ : σ ^ Module.finrank K L = 1) (x : GL (Fin 2) (L ⊗[K] A)) :
    (sigmaGL K L A σ)^[Module.finrank K L] x = x := by
  have hentry : ∀ (k : ℕ) (x : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2),
      ((sigmaGL K L A σ)^[k] x) i j = (sigmaTensor K L A σ)^[k] (x i j) := by
    intro k
    induction k with
    | zero => intro x i j; rfl
    | succ k ih =>
        intro x i j
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', sigmaGL,
          Matrix.GeneralLinearGroup.map_apply, ← sigmaGL, ih]
  apply Units.ext
  ext i j
  rw [hentry, sigmaTensor_iterate, hσ]
  induction (x i j) using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add, hx, hy]

omit [NumberField K] [NumberField L] in

theorem twistedCentralizer_le_centralizer_normString (hσ : σ ^ Module.finrank K L = 1)
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    twistedCentralizer K L A σ δ ≤ Subgroup.centralizer ({normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  intro t ht
  set s := sigmaGL K L A σ with hs
  have htδ : t * δ = δ * s t := by
    have h := (mem_sigmaCentralizer_iff).1 ht
    rw [← hs] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  have hmul : ∀ (k : ℕ) (x y : GL (Fin 2) (L ⊗[K] A)), s^[k] (x * y) = s^[k] x * s^[k] y := by
    intro k
    induction k with
    | zero => intro x y; rfl
    | succ k ih => intro x y; simp only [Function.iterate_succ_apply', ih, map_mul]
  have hP : ∀ k : ℕ, t * ((List.range k).map fun i => s^[i] δ).prod =
      ((List.range k).map fun i => s^[i] δ).prod * s^[k] t := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
          List.prod_singleton, ← mul_assoc, ih, mul_assoc, mul_assoc]
        congr 1
        have h1 : s^[k] t * s^[k] δ = s^[k] (t * δ) := (hmul k t δ).symm
        rw [h1, htδ, hmul, ← Function.iterate_succ_apply s k t]
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := hP (Module.finrank K L)
  rw [sigmaGL_iterate_finrank K L A σ hσ] at h
  exact h

omit [NumberField K] [NumberField L] in

theorem twistedCentralizer_comm (hσ : σ ^ Module.finrank K L = 1) {δ : GL (Fin 2) (L ⊗[K] A)}
    (hδ : IsRegularSemisimple (normString K L A σ δ)) (s t : twistedCentralizer K L A σ δ) : s * t = t * s :=
  Subtype.ext (mul_comm_of_mem_centralizer hδ
    (twistedCentralizer_le_centralizer_normString K L A σ hσ δ s.2)
    (twistedCentralizer_le_centralizer_normString K L A σ hσ δ t.2))

variable [TopologicalSpace A] [IsTopologicalRing A]

theorem continuous_sigmaTensor : Continuous (sigmaTensor K L A σ) := by
  haveI := isTopologicalRing_tensor K L A
  exact IsModuleTopology.continuous_of_linearMap
    (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap

theorem continuous_sigmaGL : Continuous (sigmaGL K L A σ) := by
  haveI := isTopologicalRing_tensor K L A
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map (continuous_sigmaTensor K L A σ)

theorem isClosed_twistedCentralizer [T2Space A] (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) : Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := isTopologicalGroup_tensorGL K L A
  haveI := t2Space_tensorGL K L A
  have hc : Continuous fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (sigmaGL K L A σ t)⁻¹ :=
    (continuous_id.mul continuous_const).mul (continuous_sigmaGL K L A σ).inv
  have : ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) : Set (GL (Fin 2) (L ⊗[K] A))) =
      (fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (sigmaGL K L A σ t)⁻¹) ⁻¹' {δ} := by
    ext t
    exact mem_sigmaCentralizer_iff
  rw [this]
  exact (isClosed_singleton).preimage hc

end Twist

section SigmaStable

variable (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)

theorem sigmaTensor_mem_semiLocalIntegers {x : SL K L v} (hx : x ∈ semiLocalIntegers K L v) :
    sigmaTensor K L (v.adicCompletion K) σ x ∈ semiLocalIntegers K L v := by
  obtain ⟨z, rfl⟩ := hx
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact zero_mem_semiLocalIntegers K L v
  | tmul b y =>
      refine ⟨(galRestrict (𝓞 K) K L (𝓞 L) σ b) ⊗ₜ y, ?_⟩
      rw [HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul, HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul,
        algebraMap_galRestrict_apply]
      simp [sigmaTensor]
  | add x y hx hy =>
      rw [map_add, map_add]
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb]⟩

theorem sigmaGL_mem_semiLocalIntegralSet {g : Gsl K L v} (hg : g ∈ semiLocalIntegralSet K L v) :
    sigmaGL K L (v.adicCompletion K) σ g ∈ semiLocalIntegralSet K L v := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · exact sigmaTensor_mem_semiLocalIntegers v σ (hg.1 i j)
  · rw [← map_inv]
    exact sigmaTensor_mem_semiLocalIntegers v σ (hg.2 i j)

end SigmaStable

section TestFn

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

omit [NumberField L] in
theorem continuous_ringEquiv_mixedSpace : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace L) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

omit [NumberField L] in
theorem continuous_archEntries : Continuous (archEntries L : Garch L → _) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_ringEquiv_mixedSpace (L := L)).comp (Units.continuous_val.matrix_elem i j)

namespace IsArchTestFactor
private theorem _root_.AutomorphicForm.TwistedWeightedEuler.IsArchTestFactor.continuous {φa : Garch L → ℂ} (h : IsArchTestFactor L φa) : Continuous φa := by
  obtain ⟨⟨Φ, hΦ, hφa⟩, -⟩ := h
  have : φa = Φ ∘ archEntries L := funext hφa
  rw [this]
  exact hΦ.continuous.comp continuous_archEntries

end IsArchTestFactor
p2m_export "AutomorphicForm.TwistedWeightedEuler" "IsArchTestFactor.continuous"
variable {S : Finset (HeightOneSpectrum (𝓞 K))} {φ : Gad L → ℂ} {φa : Garch L → ℂ} {φf : Gfin L → ℂ}
  {φS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ}

theorem continuous_of_isSemiLocalFactorization (hφ : IsSemiLocalFactorization K L S φ φa φf φS) : Continuous φ := by
  have h : φ = fun g => φa (glArch (𝓞 L) L g) * φf (glFin (𝓞 L) L g) := funext hφ.2.2.2.2.2
  rw [h]
  exact ((IsArchTestFactor.continuous hφ.1).comp (continuous_glArch (𝓞 L) L)).mul
    (hφ.2.1.1.continuous.comp (continuous_glFin (𝓞 L) L))

theorem bounded_of_isSemiLocalFactorization (hφ : IsSemiLocalFactorization K L S φ φa φf φS) :
    ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C := by
  obtain ⟨Ca, hCa⟩ := ((IsArchTestFactor.continuous hφ.1).norm).bddAbove_range_of_hasCompactSupport hφ.1.2.norm
  obtain ⟨Cf, hCf⟩ := (hφ.2.1.1.continuous.norm).bddAbove_range_of_hasCompactSupport hφ.2.1.2.norm
  refine ⟨Ca * Cf, fun g => ?_⟩
  rw [hφ.2.2.2.2.2 g, norm_mul]
  have ha : ‖φa (glArch (𝓞 L) L g)‖ ≤ Ca := hCa ⟨_, rfl⟩
  have hb : ‖φf (glFin (𝓞 L) L g)‖ ≤ Cf := hCf ⟨_, rfl⟩
  have hCa0 : 0 ≤ Ca := (norm_nonneg _).trans ha
  exact mul_le_mul ha hb (norm_nonneg _) hCa0

end TestFn

section Shape

variable (S : Finset (HeightOneSpectrum (𝓞 K))) (φ : Gad L → ℂ) (φa : Garch L → ℂ) (φf : Gfin L → ℂ)
  (φS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ)

def φSp (v : HeightOneSpectrum (𝓞 K)) : Gsl K L v → ℂ :=
  if v ∈ S then φS v else (semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)

theorem φSp_of_mem {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) : φSp S φS v = φS v := by
  simp only [φSp, hv, if_true]

theorem φSp_of_not_mem {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) :
    φSp S φS v = (semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ) := by
  simp only [φSp, hv, if_false]

abbrev φat : Ht K L → ℂ := φa ∘ archIdentGL K L

abbrev φt : Gt K L → ℂ := φ ∘ baseChangeGL K L

variable {S φ φa φf φS}

theorem shape_of_subset (hφ : IsSemiLocalFactorization K L S φ φa φf φS) {S' : Finset (HeightOneSpectrum (𝓞 K))}
    (hSS' : S ⊆ S') (x : Gt K L) (hx : ∀ v ∉ S', tensorPlace K L v x ∈ semiLocalIntegralSet K L v) :
    φt φ x = φat φa (tensorArch K L x) * ∏ v ∈ S', φSp S φS v (tensorPlace K L v x) := by
  show φ (baseChangeGL K L x) = φa (archIdentGL K L (tensorArch K L x)) * _
  rw [hφ.2.2.2.2.2, glArch_baseChangeGL]
  by_cases hall : ∀ v ∈ S', v ∉ S → tensorPlace K L v x ∈ semiLocalIntegralSet K L v
  · have hint : ∀ v ∉ S, semiLocalComponent K L v (glFin (𝓞 L) L (baseChangeGL K L x)) ∈ semiLocalIntegralSet K L v := by
      intro v hv
      rw [semiLocalComponent_glFin_baseChangeGL]
      by_cases hv' : v ∈ S'
      · exact hall v hv' hv
      · exact hx v hv'
    rw [hφ.2.2.2.1 _ hint]
    congr 1
    rw [← Finset.prod_subset hSS' (fun v hv' hv => ?_)]
    · exact Finset.prod_congr rfl fun v hv => by rw [φSp_of_mem S φS hv, semiLocalComponent_glFin_baseChangeGL]
    · rw [φSp_of_not_mem S φS hv, Set.indicator_of_mem (hall v hv' hv)]
  · push Not at hall
    obtain ⟨v, hv', hv, hgv⟩ := hall
    rw [hφ.2.2.2.2.1 _ ⟨v, hv, by rwa [semiLocalComponent_glFin_baseChangeGL]⟩, mul_zero]
    symm
    apply mul_eq_zero_of_right
    exact Finset.prod_eq_zero hv' (by rw [φSp_of_not_mem S φS hv, Set.indicator_of_notMem hgv])

theorem vanish_of_subset (hφ : IsSemiLocalFactorization K L S φ φa φf φS) {S' : Finset (HeightOneSpectrum (𝓞 K))}
    (hSS' : S ⊆ S') (x : Gt K L) (hx : ∃ v ∉ S', tensorPlace K L v x ∉ semiLocalIntegralSet K L v) : φt φ x = 0 := by
  obtain ⟨v, hv', hgv⟩ := hx
  show φ (baseChangeGL K L x) = 0
  rw [hφ.2.2.2.2.2, hφ.2.2.2.2.1 _ ⟨v, fun hv => hv' (hSS' hv), by rwa [semiLocalComponent_glFin_baseChangeGL]⟩,
    mul_zero]

theorem measurable_φSp (hφ : IsSemiLocalFactorization K L S φ φa φf φS) (v : HeightOneSpectrum (𝓞 K)) :
    Measurable (φSp S φS v) := by
  by_cases hv : v ∈ S
  · rw [φSp_of_mem S φS hv]
    exact (hφ.2.2.1 v hv).1.continuous.measurable
  · rw [φSp_of_not_mem S φS hv]
    exact measurable_const.indicator (isOpen_semiLocalIntegralSet K L v).measurableSet

theorem continuous_φat (hφ : IsSemiLocalFactorization K L S φ φa φf φS) : Continuous (φat φa : Ht K L → ℂ) :=
  (IsArchTestFactor.continuous hφ.1).comp (archIdentGLEquiv K L).continuous

theorem continuous_φt (hφ : IsSemiLocalFactorization K L S φ φa φf φS) : Continuous (φt φ : Gt K L → ℂ) :=
  (continuous_of_isSemiLocalFactorization hφ).comp (baseChangeGLEquiv K L).continuous

theorem bounded_φt (hφ : IsSemiLocalFactorization K L S φ φa φf φS) : ∃ C : ℝ, ∀ x : Gt K L, ‖φt φ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := bounded_of_isSemiLocalFactorization hφ
  exact ⟨C, fun x => hC _⟩

end Shape

section TConj

variable (σ : L ≃ₐ[K] L)

theorem tensorArch_tconj (δ x : Gt K L) :
    tensorArch K L (x⁻¹ * δ * sigmaGL K L _ σ x) =
      (tensorArch K L x)⁻¹ * tensorArch K L δ * sigmaGL K L _ σ (tensorArch K L x) := by
  rw [map_mul, map_mul, map_inv, tensorArch_sigmaGL]

theorem tensorPlace_tconj (v : HeightOneSpectrum (𝓞 K)) (δ x : Gt K L) :
    tensorPlace K L v (x⁻¹ * δ * sigmaGL K L _ σ x) =
      (tensorPlace K L v x)⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ (tensorPlace K L v x) := by
  rw [map_mul, map_mul, map_inv, tensorPlace_sigmaGL]

end TConj

namespace LocalWeightKit

open AutomorphicForm.LocalWeight

variable {F : Type*} [NormedField F]

theorem det_norm_pos (x : GL (Fin 2) F) : 0 < ‖(x : Matrix (Fin 2) (Fin 2) F).det‖ :=
  norm_pos_iff.mpr (Matrix.isUnits_det_units x).ne_zero

theorem row0_ne_zero (x : GL (Fin 2) F) :
    ¬ ((x : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 ∧ (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0) := by
  rintro ⟨h0, h1⟩
  have hdet : (x : Matrix (Fin 2) (Fin 2) F).det = 0 := by
    rw [Matrix.det_fin_two, h0, h1]; ring
  exact (Matrix.isUnits_det_units x).ne_zero hdet

theorem topMax_pos (x : GL (Fin 2) F) :
    0 < max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ := by
  rcases lt_or_ge 0 (max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖) with h | h
  · exact h
  · exfalso
    have h0 : ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ≤ 0 := (le_max_left _ _).trans h
    have h1 : ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ ≤ 0 := (le_max_right _ _).trans h
    exact row0_ne_zero x ⟨norm_le_zero_iff.mp h0, norm_le_zero_iff.mp h1⟩

theorem arg_pos (x : GL (Fin 2) F) :
    0 < max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ *
        AdelicHeight.rowMaxNorm (x : Matrix (Fin 2) (Fin 2) F) / ‖(x : Matrix (Fin 2) (Fin 2) F).det‖ :=
  div_pos (mul_pos (topMax_pos x) (AdelicHeight.rowMaxNorm_pos x)) (det_norm_pos x)

theorem continuous_weight : Continuous (weight : GL (Fin 2) F → ℝ) := by
  have hc : ∀ i j : Fin 2, Continuous fun x : GL (Fin 2) F => ‖(x : Matrix (Fin 2) (Fin 2) F) i j‖ :=
    fun i j => (Units.continuous_val.matrix_elem i j).norm
  have hdet : Continuous fun x : GL (Fin 2) F => ‖(x : Matrix (Fin 2) (Fin 2) F).det‖ :=
    (Units.continuous_val.matrix_det).norm
  unfold weight
  refine continuous_const.mul (Continuous.log ?_ fun x => (arg_pos x).ne')
  exact (((hc 0 0).max (hc 0 1)).mul ((hc 1 0).max (hc 1 1))).div hdet fun x => (det_norm_pos x).ne'

section Ultrametric

variable [IsUltrametricDist F]

omit [IsUltrametricDist F] in
theorem norm_det_le (M : Matrix (Fin 2) (Fin 2) F) [IsUltrametricDist F] :
    ‖M.det‖ ≤ max ‖M 0 0‖ ‖M 0 1‖ * max ‖M 1 0‖ ‖M 1 1‖ := by
  rw [Matrix.det_fin_two, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact mul_le_mul (le_max_left _ _) (le_max_right _ _) (norm_nonneg _)
      ((norm_nonneg _).trans (le_max_left _ _))
  · rw [norm_neg, norm_mul]
    exact mul_le_mul (le_max_right _ _) (le_max_left _ _) (norm_nonneg _)
      ((norm_nonneg _).trans (le_max_left _ _))

theorem weight_eq_zero_of_forall_norm_le_one (x : GL (Fin 2) F)
    (h : ∀ i j, ‖(x : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ 1)
    (h' : ∀ i j, ‖((x⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ 1) : weight x = 0 := by
  have hM0 : max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ ≤ 1 :=
    max_le (h 0 0) (h 0 1)
  have hM1 : AdelicHeight.rowMaxNorm (x : Matrix (Fin 2) (Fin 2) F) ≤ 1 := max_le (h 1 0) (h 1 1)
  have hd1 : ‖(x : Matrix (Fin 2) (Fin 2) F).det‖ ≤ 1 :=
    (norm_det_le _).trans (mul_le_one₀ hM0 (AdelicHeight.rowMaxNorm_nonneg _) hM1)
  have hd1' : ‖((x⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det‖ ≤ 1 :=
    (norm_det_le _).trans (mul_le_one₀ (max_le (h' 0 0) (h' 0 1)) (AdelicHeight.rowMaxNorm_nonneg _)
      (max_le (h' 1 0) (h' 1 1)))
  have hprod : ‖(x : Matrix (Fin 2) (Fin 2) F).det‖ * ‖((x⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one,
      norm_one]
  have hdet : ‖(x : Matrix (Fin 2) (Fin 2) F).det‖ = 1 := by
    refine le_antisymm hd1 ?_
    have hpos' : 0 < ‖((x⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det‖ := det_norm_pos _
    nlinarith
  have hMM : max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ *
      AdelicHeight.rowMaxNorm (x : Matrix (Fin 2) (Fin 2) F) = 1 := by
    refine le_antisymm (mul_le_one₀ hM0 (AdelicHeight.rowMaxNorm_nonneg _) hM1) ?_
    have := norm_det_le (x : Matrix (Fin 2) (Fin 2) F)
    rw [hdet] at this
    exact this
  unfold weight
  rw [hMM, hdet, div_one, Real.log_one, mul_zero]

end Ultrametric

end LocalWeightKit

section SemiLocal

variable (v : HeightOneSpectrum (𝓞 K))

theorem semiLocalPlaceComponent_apply (w : v.Extension (𝓞 L)) (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (i j : Fin 2) :
    ((semiLocalPlaceComponent K L v w x : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) _) i j =
      semiLocalHomeomorph K L v ((x : Matrix (Fin 2) (Fin 2) _) i j) w := rfl

theorem norm_le_one_of_mem_semiLocalIntegers {a : L ⊗[K] v.adicCompletion K}
    (ha : a ∈ semiLocalIntegers K L v) (w : v.Extension (𝓞 L)) :
    ‖semiLocalHomeomorph K L v a w‖ ≤ 1 := by
  rw [semiLocalIntegers_eq_preimage] at ha
  have hw : semiLocalHomeomorph K L v a w ∈ (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L)) :=
    ha w (Set.mem_univ _)
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at hw
  exact Valued.toNormedField.norm_le_one_iff.mpr hw

theorem semiLocalWeight_eq_zero_of_mem {x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hx : x ∈ semiLocalIntegralSet K L v) : semiLocalWeight K L v x = 0 := by
  unfold semiLocalWeight
  refine finsum_eq_zero_of_forall_eq_zero fun w => ?_
  refine LocalWeightKit.weight_eq_zero_of_forall_norm_le_one _ (fun i j => ?_) (fun i j => ?_)
  · rw [semiLocalPlaceComponent_apply]
    exact norm_le_one_of_mem_semiLocalIntegers v (hx.1 i j) w
  · rw [← map_inv, semiLocalPlaceComponent_apply]
    exact norm_le_one_of_mem_semiLocalIntegers v (hx.2 i j) w

theorem continuous_semiLocalPlaceComponent (w : v.Extension (𝓞 L)) :
    Continuous (semiLocalPlaceComponent K L v w) := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  refine continuous_glMap _ ?_
  exact (continuous_apply w).comp (semiLocalHomeomorph K L v).continuous

theorem continuous_semiLocalWeight : Continuous (semiLocalWeight K L v) := by
  haveI : Fintype (v.Extension (𝓞 L)) := Fintype.ofFinite _
  have h : semiLocalWeight K L v = fun x => ∑ w : v.Extension (𝓞 L),
      LocalWeight.weight (semiLocalPlaceComponent K L v w x) := by
    funext x; exact finsum_eq_sum_of_fintype _
  rw [h]
  exact continuous_finsetSum _ fun w _ =>
    LocalWeightKit.continuous_weight.comp (continuous_semiLocalPlaceComponent v w)

end SemiLocal

section WeightedSection

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem integral_mul_mul_eq_of_continuous_weight
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (μ : Measure G) [μ.IsHaarMeasure] (τ : Measure T) [τ.IsHaarMeasure] [τ.IsInvInvariant]
    (F : G → ℂ) (hFm : Measurable F) (hFb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C)
    (hFT : ∀ (t : T) (x : G), F ((t : G) * x) = F x)
    (W : G → ℝ) (hWc : Continuous W) (hWT : ∀ (t : T) (x : G), W ((t : G) * x) = W x)
    (w₁ w₂ : G → ℝ)
    (hw₁ : (∀ x, 0 ≤ w₁ x) ∧ Measurable w₁ ∧ HasCompactSupport w₁ ∧
      ∀ x, F x ≠ 0 → ∫ t : T, w₁ ((t : G) * x) ∂τ = 1)
    (hw₂ : (∀ x, 0 ≤ w₂ x) ∧ Measurable w₂ ∧ HasCompactSupport w₂ ∧
      ∀ x, F x ≠ 0 → ∫ t : T, w₂ ((t : G) * x) ∂τ = 1) :
    ∫ x, F x * (W x : ℂ) * (w₁ x : ℂ) ∂μ = ∫ x, F x * (W x : ℂ) * (w₂ x : ℂ) ∂μ :=
  (MeasureTheory.integrable_and_integral_mul_mul_eq_of_integral_subgroup_translate_eq_one_of_continuous T hT μ τ
    F hFm hFb hFT W hWc hWT w₁ w₂ hw₁ hw₂).2

theorem integrable_mul_mul_of_continuous_weight
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (μ : Measure G) [μ.IsHaarMeasure] (τ : Measure T) [τ.IsHaarMeasure] [τ.IsInvInvariant]
    (F : G → ℂ) (hFm : Measurable F) (hFb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C)
    (hFT : ∀ (t : T) (x : G), F ((t : G) * x) = F x)
    (W : G → ℝ) (hWc : Continuous W) (hWT : ∀ (t : T) (x : G), W ((t : G) * x) = W x)
    (w : G → ℝ)
    (hw : (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
      ∀ x, F x ≠ 0 → ∫ t : T, w ((t : G) * x) ∂τ = 1) :
    Integrable (fun x => F x * (W x : ℂ) * (w x : ℂ)) μ :=
  (MeasureTheory.integrable_and_integral_mul_mul_eq_of_integral_subgroup_translate_eq_one_of_continuous T hT μ τ
    F hFm hFb hFT W hWc hWT w w hw hw).1

end WeightedSection

section GlobalWeight

theorem exists_finset_mem_nhds_forall_tensorPlace_mem (x₀ : Gt K L) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)), ∃ U ∈ nhds x₀, ∀ x ∈ U, ∀ v ∉ S₀,
      tensorPlace K L v x ∈ semiLocalIntegralSet K L v :=
  AutomorphicForm.exists_finset_mem_nhds_forall_tensorPlace_mem_semiLocalIntegralSet K L x₀

theorem finite_setOf_tensorPlace_not_mem (x : Gt K L) :
    {v | tensorPlace K L v x ∉ semiLocalIntegralSet K L v}.Finite := by
  obtain ⟨S₀, U, hU, h⟩ := exists_finset_mem_nhds_forall_tensorPlace_mem x
  refine (S₀.finite_toSet).subset fun v hv => ?_
  by_contra hvS
  exact hv (h x (mem_of_mem_nhds hU) v (by simpa using hvS))

def finWeight (x : Gt K L) : ℝ :=
  ∑ᶠ v : HeightOneSpectrum (𝓞 K), semiLocalWeight K L v (tensorPlace K L v x)

theorem finWeight_eq_sum (S₁ : Finset (HeightOneSpectrum (𝓞 K))) (x : Gt K L)
    (hx : ∀ v ∉ S₁, tensorPlace K L v x ∈ semiLocalIntegralSet K L v) :
    finWeight x = ∑ v ∈ S₁, semiLocalWeight K L v (tensorPlace K L v x) := by
  unfold finWeight
  refine finsum_eq_sum_of_support_subset _ fun v hv => ?_
  by_contra hvS
  exact hv (semiLocalWeight_eq_zero_of_mem v (hx v (by simpa using hvS)))

theorem continuous_finWeight : Continuous (finWeight : Gt K L → ℝ) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨S₀, U, hU, hUint⟩ := exists_finset_mem_nhds_forall_tensorPlace_mem x₀
  have hcont : Continuous fun x : Gt K L => ∑ v ∈ S₀, semiLocalWeight K L v (tensorPlace K L v x) :=
    continuous_finsetSum _ fun v _ => (continuous_semiLocalWeight v).comp (continuous_tensorPlace K L v)
  refine (hcont.continuousAt).congr_of_eventuallyEq ?_
  exact Filter.eventuallyEq_of_mem hU fun x hx => finWeight_eq_sum S₀ x (hUint x hx)

end GlobalWeight

section Dichotomy

variable {S : Finset (HeightOneSpectrum (𝓞 K))} {φ : Gad L → ℂ} {φa : Garch L → ℂ} {φf : Gfin L → ℂ}
  {φS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ} (σ : L ≃ₐ[K] L)

theorem exists_ne_zero_of_local (hφ : IsSemiLocalFactorization K L S φ φa φf φS) (δ : Gt K L)
    (ha : ∃ x : Ht K L, φat φa (x⁻¹ * tensorArch K L δ * sigmaGL K L _ σ x) ≠ 0)
    (hS : ∀ v ∈ S, ∃ x : Gsl K L v, φS v (x⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ x) ≠ 0)
    (hnS : ∀ v ∉ S, ∃ x : Gsl K L v, x⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ x ∈ semiLocalIntegralSet K L v) :
    ∃ x : Gt K L, φt φ (x⁻¹ * δ * sigmaGL K L _ σ x) ≠ 0 := by
  obtain ⟨xa, hxa⟩ := ha
  have hloc : ∀ v : HeightOneSpectrum (𝓞 K), ∃ x : Gsl K L v,
      (v ∈ S → φS v (x⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ x) ≠ 0) ∧
      (v ∉ S → x⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ x ∈ semiLocalIntegralSet K L v) := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨x, hx⟩ := hS v hv
      exact ⟨x, fun _ => hx, fun h => absurd hv h⟩
    · obtain ⟨x, hx⟩ := hnS v hv
      exact ⟨x, fun h => absurd h hv, fun _ => hx⟩
  choose xv hxvS hxvnS using hloc
  obtain ⟨B, hB⟩ : ∃ B : Finset (HeightOneSpectrum (𝓞 K)), B = S ∪ (finite_setOf_tensorPlace_not_mem δ).toFinset :=
    ⟨_, rfl⟩
  obtain ⟨x, hxa', hxB, hxnB⟩ :=
    AutomorphicForm.exists_tensorArch_eq_and_forall_tensorPlace_eq_of_finset K L B xa xv
  have hδint : ∀ v ∉ B, tensorPlace K L v δ ∈ semiLocalIntegralSet K L v := by
    intro v hv
    by_contra h
    exact hv (by rw [hB]; exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h))
  have hSB : S ⊆ B := by rw [hB]; exact Finset.subset_union_left
  refine ⟨x, ?_⟩
  have hint : ∀ v ∉ S, tensorPlace K L v (x⁻¹ * δ * sigmaGL K L _ σ x) ∈ semiLocalIntegralSet K L v := by
    intro v hv
    rw [tensorPlace_tconj]
    by_cases hvB : v ∈ B
    · rw [hxB v hvB]; exact hxvnS v hv
    · rw [hxnB v hvB, inv_one, one_mul, map_one, mul_one]; exact hδint v hvB
  rw [shape_of_subset hφ (Finset.Subset.refl S) _ hint, tensorArch_tconj, hxa']
  refine mul_ne_zero hxa (Finset.prod_ne_zero_iff.2 fun v hv => ?_)
  rw [φSp_of_mem S φS hv, tensorPlace_tconj, hxB v (hSB hv)]
  exact hxvS v hv

theorem tensorArch_mem_twistedCentralizer {δ : Gt K L} {t : Gt K L}
    (ht : t ∈ twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ) :
    tensorArch K L t ∈ twistedCentralizer K L (InfiniteAdeleRing K) σ (tensorArch K L δ) := by
  rw [mem_sigmaCentralizer_iff] at ht ⊢
  have h := congrArg (tensorArch K L) ht
  rwa [map_mul, map_mul, map_inv, tensorArch_sigmaGL] at h

theorem tensorPlace_mem_twistedCentralizer (v : HeightOneSpectrum (𝓞 K)) {δ : Gt K L} {t : Gt K L}
    (ht : t ∈ twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ) :
    tensorPlace K L v t ∈ twistedCentralizer K L (v.adicCompletion K) σ (tensorPlace K L v δ) := by
  rw [mem_sigmaCentralizer_iff] at ht ⊢
  have h := congrArg (tensorPlace K L v) ht
  rwa [map_mul, map_mul, map_inv, tensorPlace_sigmaGL] at h

end Dichotomy

section InvInvariant

theorem isInvInvariant_of_comm {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) (hcomm : ∀ s t : T, s * t = t * s)
    [MeasurableSpace T] [BorelSpace T] (τ : Measure T) [τ.IsHaarMeasure] : τ.IsInvInvariant := by
  letI : CommGroup T := { mul_comm := hcomm }
  haveI : LocallyCompactSpace T := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology T :=
    (Topology.IsInducing.subtypeVal : Topology.IsInducing (Subtype.val : T → G)).secondCountableTopology
  haveI : PseudoMetrizableSpace T := PseudoMetrizableSpace.of_regularSpace_secondCountableTopology T
  haveI : SigmaCompactSpace T := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : τ.InnerRegular := inferInstance
  exact Measure.IsHaarMeasure.isInvInvariant_of_innerRegular τ

theorem secondCountableTopology_TA [SecondCountableTopology (AdeleRing (𝓞 K) K)] :
    SecondCountableTopology (L ⊗[K] AdeleRing (𝓞 K) K) := by
  let ι := Module.Free.ChooseBasisIndex (AdeleRing (𝓞 K) K) (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI : Fintype ι := Module.Free.ChooseBasisIndex.fintype (AdeleRing (𝓞 K) K) (L ⊗[K] AdeleRing (𝓞 K) K)
  let b : Module.Basis ι (AdeleRing (𝓞 K) K) (L ⊗[K] AdeleRing (𝓞 K) K) :=
    Module.Free.chooseBasis (AdeleRing (𝓞 K) K) (L ⊗[K] AdeleRing (𝓞 K) K)
  let e : (L ⊗[K] AdeleRing (𝓞 K) K) ≃ₗ[AdeleRing (𝓞 K) K] (ι → AdeleRing (𝓞 K) K) := b.equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let eh : (L ⊗[K] AdeleRing (𝓞 K) K) ≃ₜ (ι → AdeleRing (𝓞 K) K) :=
    { toEquiv := e.toEquiv, continuous_toFun := h1, continuous_invFun := h2 }
  exact eh.isInducing.secondCountableTopology

end InvInvariant

section Euler

variable (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)
  (μ : Measure (Gt K L)) [IsHaarMeasure μ] (ν : Measure (Ht K L)) (cG : ℝ)
  (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (F : Gt K L → ℂ) (Fa : Ht K L → ℂ)
      (FS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ),
      AEStronglyMeasurable Fa ν → (∀ v ∈ S, AEStronglyMeasurable (FS v) (semiLocalHaar K L v)) →
      (∀ x : Gt K L, (∀ v ∉ S, tensorPlace K L v x ∈ semiLocalIntegralSet K L v) →
          F x = Fa (tensorArch K L x) * ∏ v ∈ S, FS v (tensorPlace K L v x)) →
      (∀ x : Gt K L, (∃ v ∉ S, tensorPlace K L v x ∉ semiLocalIntegralSet K L v) → F x = 0) →
        ∫ x, F x ∂μ = cG * (∫ y, Fa y ∂ν) * ∏ v ∈ S, ∫ y, FS v y ∂(semiLocalHaar K L v))
  (δ : Gt K L) (hδ : IsRegularSemisimple (normString K L (AdeleRing (𝓞 K) K) σ δ))

abbrev Ttw : Subgroup (Gt K L) := twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ
abbrev Ta' : Subgroup (Ht K L) := twistedCentralizer K L (InfiniteAdeleRing K) σ (tensorArch K L δ)
abbrev Tv' (v : HeightOneSpectrum (𝓞 K)) : Subgroup (Gsl K L v) :=
  twistedCentralizer K L (v.adicCompletion K) σ (tensorPlace K L v δ)

variable (τ : Measure (Ttw σ δ)) [IsHaarMeasure τ] (τa : Measure (Ta' σ δ)) [IsHaarMeasure τa]
  (τf : ∀ v : HeightOneSpectrum (𝓞 K), Measure (Tv' σ δ v)) (hτf : ∀ v, IsHaarMeasure (τf v))
  (hτf1 : ∀ v, τf v (Subtype.val ⁻¹' semiLocalIntegralSet K L v) = 1)
  (cT : ℝ) (hcT : 0 < cT)
  (hT : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (W : Gt K L → ℂ) (Wa : Ht K L → ℂ)
      (WS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ),
      AEStronglyMeasurable (fun t : Ta' σ δ => Wa t) τa →
      (∀ v ∈ S, AEStronglyMeasurable (fun t : Tv' σ δ v => WS v t) (τf v)) →
      (∀ t : Ttw σ δ, (∀ v ∉ S, tensorPlace K L v (t : Gt K L) ∈ semiLocalIntegralSet K L v) →
          W t = Wa (tensorArch K L (t : Gt K L)) * ∏ v ∈ S, WS v (tensorPlace K L v (t : Gt K L))) →
      (∀ t : Ttw σ δ, (∃ v ∉ S, tensorPlace K L v (t : Gt K L) ∉ semiLocalIntegralSet K L v) → W t = 0) →
        ∫ t, W t ∂τ = cT * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v))
  (S : Finset (HeightOneSpectrum (𝓞 K))) (φ : Gad L → ℂ) (φa : Garch L → ℂ) (φf : Gfin L → ℂ)
  (φS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ) (hφ : IsSemiLocalFactorization K L S φ φa φf φS)

include hσ hδ in

theorem exists_local_sectionFn (v : HeightOneSpectrum (𝓞 K)) [IsHaarMeasure (τf v)]
    (g : Gsl K L v → ℂ) (C : Set (Gsl K L v)) (hC : IsCompact C)
    (hE : {y : Gsl K L v | g (y⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ y) ≠ 0} ⊆ (Tv' σ δ v : Set (Gsl K L v)) * C) :
    ∃ w : Gsl K L v → ℝ, IsTwistedSectionFnOn K L (v.adicCompletion K) σ (tensorPlace K L v δ) (τf v) g w := by
  have hδv : IsRegularSemisimple (normString K L (v.adicCompletion K) σ (tensorPlace K L v δ)) := by
    rw [← map_normString K L _ σ (tensorPlace K L v) (tensorPlace_sigmaGL K L σ v) δ]
    exact isRegularSemisimple_map _ hδ
  haveI : (τf v).IsMulRightInvariant := isMulRightInvariant_of_comm _ (twistedCentralizer_comm K L _ σ hσ hδv) (τf v)
  obtain ⟨w, hw0, hwm, hws, hw1⟩ :=
    MeasureTheory.exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul
      (Tv' σ δ v) (isClosed_twistedCentralizer K L _ σ _) (τf v) hC hE
  exact ⟨w, hw0, hwm, hws, fun x hx => hw1 x hx⟩

include hσ hδ in
theorem exists_arch_sectionFn (g : Ht K L → ℂ) (C : Set (Ht K L)) (hC : IsCompact C)
    (hE : {y : Ht K L | g (y⁻¹ * tensorArch K L δ * sigmaGL K L _ σ y) ≠ 0} ⊆ (Ta' σ δ : Set (Ht K L)) * C) :
    ∃ w : Ht K L → ℝ, IsTwistedSectionFnOn K L (InfiniteAdeleRing K) σ (tensorArch K L δ) τa g w := by
  have hδa : IsRegularSemisimple (normString K L (InfiniteAdeleRing K) σ (tensorArch K L δ)) := by
    rw [← map_normString K L _ σ (tensorArch K L) (tensorArch_sigmaGL K L σ) δ]
    exact isRegularSemisimple_map _ hδ
  haveI : τa.IsMulRightInvariant := isMulRightInvariant_of_comm _ (twistedCentralizer_comm K L _ σ hσ hδa) τa
  obtain ⟨w, hw0, hwm, hws, hw1⟩ :=
    MeasureTheory.exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul
      (Ta' σ δ) (isClosed_twistedCentralizer K L _ σ _) τa hC hE
  exact ⟨w, hw0, hwm, hws, fun x hx => hw1 x hx⟩

theorem unit_orbitalIntegral (v : HeightOneSpectrum (𝓞 K)) (hδv : tensorPlace K L v δ ∈ semiLocalIntegralSet K L v)
    (hunit : IsTwistedSectionFnOn K L (v.adicCompletion K) σ (tensorPlace K L v δ) (τf v)
      ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℝ))) :
    IsTwistedOrbitalIntegral K L v σ (tensorPlace K L v δ) (τf v) ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) 1 := by
  refine ⟨(semiLocalIntegralSet K L v).indicator fun _ => (1 : ℝ), hunit, ?_⟩
  have h : (fun x : Gsl K L v => (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
      (x⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ x) *
      (((semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ)) =
      (semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ) := by
    funext x
    by_cases hx : x ∈ semiLocalIntegralSet K L v
    · have hc : x⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ x ∈ semiLocalIntegralSet K L v :=
        mul_mem_semiLocalIntegralSet v (mul_mem_semiLocalIntegralSet v (inv_mem_semiLocalIntegralSet v hx) hδv)
          (sigmaGL_mem_semiLocalIntegralSet v σ hx)
      simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hc, Complex.ofReal_one, mul_one]
    · simp only [Set.indicator_of_notMem hx, Complex.ofReal_zero, mul_zero]
  show (1 : ℂ) = ∫ x, (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
      (x⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ x) *
      (((semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) ∂(semiLocalHaar K L v)
  rw [h, integral_indicator_const _ (isOpen_semiLocalIntegralSet K L v).measurableSet, Measure.real,
    semiLocalHaar_semiLocalIntegralSet]
  simp

def gW (Wa : Ht K L → ℝ) (x : Gt K L) : ℝ :=
  Wa (tensorArch K L x) + ∑ᶠ v : HeightOneSpectrum (𝓞 K), semiLocalWeight K L v (tensorPlace K L v x)

theorem gW_eq_of_integral (Wa : Ht K L → ℝ) (S₁ : Finset (HeightOneSpectrum (𝓞 K))) (x : Gt K L)
    (hx : ∀ v ∉ S₁, tensorPlace K L v x ∈ semiLocalIntegralSet K L v) :
    gW Wa x = Wa (tensorArch K L x) + ∑ v ∈ S₁, semiLocalWeight K L v (tensorPlace K L v x) := by
  unfold gW
  congr 1
  refine finsum_eq_sum_of_support_subset _ fun v hv => ?_
  by_contra hvS
  exact hv (semiLocalWeight_eq_zero_of_mem v (hx v (by simpa using hvS)))

theorem unit_weightedOrbitalIntegral (v : HeightOneSpectrum (𝓞 K))
    (hunit : IsTwistedSectionFnOn K L (v.adicCompletion K) σ (tensorPlace K L v δ) (τf v)
      ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℝ))) :
    IsTwistedWeightedOrbitalIntegral K L v σ (tensorPlace K L v δ) (τf v)
      ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) 0 := by
  refine ⟨(semiLocalIntegralSet K L v).indicator fun _ => (1 : ℝ), hunit, ?_⟩
  have h : (fun x : Gsl K L v => (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
      (x⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ x) * (semiLocalWeight K L v x : ℂ) *
      (((semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ)) = fun _ => 0 := by
    funext x
    by_cases hx : x ∈ semiLocalIntegralSet K L v
    · rw [semiLocalWeight_eq_zero_of_mem v hx, Complex.ofReal_zero, mul_zero, zero_mul]
    · simp only [Set.indicator_of_notMem hx, Complex.ofReal_zero, mul_zero]
  show (0 : ℂ) = ∫ x, (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
      (x⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ x) * (semiLocalWeight K L v x : ℂ) *
      (((semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) ∂(semiLocalHaar K L v)
  rw [h, integral_zero]

omit [IsHaarMeasure μ] [IsHaarMeasure τa] in
include hG hφ in

theorem weuler_core (S₁ : Finset (HeightOneSpectrum (𝓞 K))) (hSS₁ : S ⊆ S₁)
    (hδint₁ : ∀ v ∉ S₁, tensorPlace K L v δ ∈ semiLocalIntegralSet K L v)
    (wa : Ht K L → ℝ) (hwa : IsTwistedSectionFnOn K L (InfiniteAdeleRing K) σ (tensorArch K L δ) τa (φat φa) wa)
    (wf : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℝ)
    (hwf : ∀ v ∈ S₁, IsTwistedSectionFnOn K L (v.adicCompletion K) σ (tensorPlace K L v δ) (τf v) (φSp S φS v) (wf v))
    (hunit : ∀ v ∉ S₁, IsTwistedSectionFnOn K L (v.adicCompletion K) σ (tensorPlace K L v δ) (τf v)
      ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℝ)))
    (wt : Gt K L → ℝ)
    (hwt : wt = {x : Gt K L | ∀ v ∉ S₁, tensorPlace K L v x ∈ semiLocalIntegralSet K L v}.indicator
      fun x => cT⁻¹ * (wa (tensorArch K L x) * ∏ v ∈ S₁, wf v (tensorPlace K L v x)))
    (Wa : Ht K L → ℝ) (hWam : Measurable Wa)
    (hIntA : Integrable (fun x => φt φ (x⁻¹ * δ * sigmaGL K L _ σ x) * (Wa (tensorArch K L x) : ℂ) * (wt x : ℂ)) μ)
    (hIntV : ∀ v ∈ S₁, Integrable (fun x => φt φ (x⁻¹ * δ * sigmaGL K L _ σ x) *
      (semiLocalWeight K L v (tensorPlace K L v x) : ℂ) * (wt x : ℂ)) μ)
    (J : ℂ) (hJt : J = ∫ x, φt φ (x⁻¹ * δ * sigmaGL K L _ σ x) * (gW Wa x : ℂ) * (wt x : ℂ) ∂μ) :
    ∃ (Ia : ℂ) (Iv : HeightOneSpectrum (𝓞 K) → ℂ) (Ja : ℂ) (Jv : HeightOneSpectrum (𝓞 K) → ℂ),
      IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ ν (tensorArch K L δ) τa (φat φa) Ia ∧
      (∀ v, IsTwistedOrbitalIntegral K L v σ (tensorPlace K L v δ) (τf v) (φSp S φS v) (Iv v)) ∧
      IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ ν Wa (tensorArch K L δ) τa (φat φa) Ja ∧
      (∀ v, IsTwistedWeightedOrbitalIntegral K L v σ (tensorPlace K L v δ) (τf v) (φSp S φS v) (Jv v)) ∧
      (∀ v ∉ S₁, Jv v = 0) ∧
      ∀ T : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ T →
        J = cG * cT⁻¹ * (Ja * ∏ v ∈ T, Iv v + Ia * ∑ v ∈ T, Jv v * ∏ u ∈ T.erase v, Iv u) := by

  obtain ⟨Fa, hFa⟩ : ∃ Fa : Ht K L → ℂ,
      Fa = fun x => ((cT⁻¹ : ℝ) : ℂ) * (φat φa (x⁻¹ * tensorArch K L δ * sigmaGL K L _ σ x) * (wa x : ℂ)) := ⟨_, rfl⟩
  obtain ⟨Ga, hGa⟩ : ∃ Ga : Ht K L → ℂ,
      Ga = fun x => ((cT⁻¹ : ℝ) : ℂ) * (φat φa (x⁻¹ * tensorArch K L δ * sigmaGL K L _ σ x) * (Wa x : ℂ) * (wa x : ℂ)) :=
    ⟨_, rfl⟩
  obtain ⟨Fv, hFv⟩ : ∃ Fv : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ,
      Fv = fun v x => φSp S φS v (x⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ x) * (wf v x : ℂ) := ⟨_, rfl⟩
  obtain ⟨Gv, hGv⟩ : ∃ Gv : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ,
      Gv = fun v x => φSp S φS v (x⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ x) *
        (semiLocalWeight K L v x : ℂ) * (wf v x : ℂ) := ⟨_, rfl⟩

  obtain ⟨FA, hFA⟩ : ∃ FA : Gt K L → ℂ,
      FA = fun x => φt φ (x⁻¹ * δ * sigmaGL K L _ σ x) * (Wa (tensorArch K L x) : ℂ) * (wt x : ℂ) := ⟨_, rfl⟩
  obtain ⟨FV, hFV⟩ : ∃ FV : HeightOneSpectrum (𝓞 K) → Gt K L → ℂ,
      FV = fun v x => φt φ (x⁻¹ * δ * sigmaGL K L _ σ x) * (semiLocalWeight K L v (tensorPlace K L v x) : ℂ) * (wt x : ℂ) :=
    ⟨_, rfl⟩
  have hint : ∀ x : Gt K L, (∀ v ∉ S₁, tensorPlace K L v x ∈ semiLocalIntegralSet K L v) →
      ∀ v ∉ S₁, tensorPlace K L v (x⁻¹ * δ * sigmaGL K L _ σ x) ∈ semiLocalIntegralSet K L v := by
    intro x hx v hv
    rw [tensorPlace_tconj]
    exact mul_mem_semiLocalIntegralSet v (mul_mem_semiLocalIntegralSet v (inv_mem_semiLocalIntegralSet v (hx v hv))
      (hδint₁ v hv)) (sigmaGL_mem_semiLocalIntegralSet v σ (hx v hv))
  have hwt_of_mem : ∀ x : Gt K L, (∀ v ∉ S₁, tensorPlace K L v x ∈ semiLocalIntegralSet K L v) →
      wt x = cT⁻¹ * (wa (tensorArch K L x) * ∏ v ∈ S₁, wf v (tensorPlace K L v x)) := by
    intro x hx
    rw [hwt, Set.indicator_of_mem (show x ∈ {x : Gt K L | ∀ v ∉ S₁, tensorPlace K L v x ∈ semiLocalIntegralSet K L v}
      from hx)]
  have hwt_of_not_mem : ∀ x : Gt K L, (∃ v ∉ S₁, tensorPlace K L v x ∉ semiLocalIntegralSet K L v) → wt x = 0 := by
    intro x hx
    rw [hwt, Set.indicator_of_notMem]
    obtain ⟨v, hv, hxv⟩ := hx
    exact fun h => hxv (h v hv)

  have hFAshape : ∀ x : Gt K L, (∀ v ∉ S₁, tensorPlace K L v x ∈ semiLocalIntegralSet K L v) →
      FA x = Ga (tensorArch K L x) * ∏ v ∈ S₁, Fv v (tensorPlace K L v x) := by
    intro x hx
    rw [hFA, hGa, hFv]
    dsimp only
    rw [shape_of_subset hφ hSS₁ _ (hint x hx), hwt_of_mem x hx, tensorArch_tconj]
    simp only [tensorPlace_tconj]
    push_cast
    rw [Finset.prod_mul_distrib]
    ring
  have hFAvanish : ∀ x : Gt K L, (∃ v ∉ S₁, tensorPlace K L v x ∉ semiLocalIntegralSet K L v) → FA x = 0 := by
    intro x hx
    rw [hFA]
    dsimp only
    rw [hwt_of_not_mem x hx, Complex.ofReal_zero, mul_zero]
  have hFVshape : ∀ v₀ ∈ S₁, ∀ x : Gt K L, (∀ v ∉ S₁, tensorPlace K L v x ∈ semiLocalIntegralSet K L v) →
      FV v₀ x = Fa (tensorArch K L x) *
        ∏ v ∈ S₁, (fun v => if v = v₀ then Gv v else Fv v) v (tensorPlace K L v x) := by
    intro v₀ hv₀ x hx
    have hsplit : ∏ v ∈ S₁, (fun v => if v = v₀ then Gv v else Fv v) v (tensorPlace K L v x) =
        (semiLocalWeight K L v₀ (tensorPlace K L v₀ x) : ℂ) * ∏ v ∈ S₁, Fv v (tensorPlace K L v x) := by
      rw [← Finset.mul_prod_erase S₁ _ hv₀, ← Finset.mul_prod_erase S₁ (fun v => Fv v (tensorPlace K L v x)) hv₀]
      dsimp only
      rw [if_pos rfl]
      have hrest : ∏ v ∈ S₁.erase v₀, (if v = v₀ then Gv v else Fv v) (tensorPlace K L v x) =
          ∏ v ∈ S₁.erase v₀, Fv v (tensorPlace K L v x) :=
        Finset.prod_congr rfl fun v hv => by rw [if_neg (Finset.ne_of_mem_erase hv)]
      rw [hrest, hGv, hFv]
      dsimp only
      ring
    rw [hsplit, hFV, hFa, hFv]
    dsimp only
    rw [shape_of_subset hφ hSS₁ _ (hint x hx), hwt_of_mem x hx, tensorArch_tconj]
    simp only [tensorPlace_tconj]
    push_cast
    rw [Finset.prod_mul_distrib]
    ring
  have hFVvanish : ∀ v₀, ∀ x : Gt K L, (∃ v ∉ S₁, tensorPlace K L v x ∉ semiLocalIntegralSet K L v) → FV v₀ x = 0 := by
    intro v₀ x hx
    rw [hFV]
    dsimp only
    rw [hwt_of_not_mem x hx, Complex.ofReal_zero, mul_zero]

  have hmeas_tca : Measurable fun x : Ht K L => x⁻¹ * tensorArch K L δ * sigmaGL K L _ σ x :=
    (continuous_twistedConj _ _ (continuous_sigmaGL K L _ σ)).measurable
  have hFa_meas : AEStronglyMeasurable Fa ν := by
    rw [hFa]
    refine Measurable.aestronglyMeasurable ?_
    exact measurable_const.mul ((((continuous_φat hφ).measurable.comp hmeas_tca)).mul
      (Complex.measurable_ofReal.comp hwa.2.1))
  have hGa_meas : AEStronglyMeasurable Ga ν := by
    rw [hGa]
    refine Measurable.aestronglyMeasurable ?_
    exact measurable_const.mul (((((continuous_φat hφ).measurable.comp hmeas_tca)).mul
      (Complex.measurable_ofReal.comp hWam)).mul (Complex.measurable_ofReal.comp hwa.2.1))
  have hFv_meas : ∀ v ∈ S₁, AEStronglyMeasurable (Fv v) (semiLocalHaar K L v) := by
    intro v hv
    rw [hFv]
    refine Measurable.aestronglyMeasurable ?_
    exact ((measurable_φSp hφ v).comp (continuous_twistedConj _ _ (continuous_sigmaGL K L _ σ)).measurable).mul
      (Complex.measurable_ofReal.comp (hwf v hv).2.1)
  have hGv_meas : ∀ v ∈ S₁, AEStronglyMeasurable (Gv v) (semiLocalHaar K L v) := by
    intro v hv
    rw [hGv]
    refine Measurable.aestronglyMeasurable ?_
    exact (((measurable_φSp hφ v).comp (continuous_twistedConj _ _ (continuous_sigmaGL K L _ σ)).measurable).mul
      (Complex.measurable_ofReal.comp (continuous_semiLocalWeight v).measurable)).mul
      (Complex.measurable_ofReal.comp (hwf v hv).2.1)
  have hmix_meas : ∀ v₀ ∈ S₁, ∀ v ∈ S₁,
      AEStronglyMeasurable ((fun v => if v = v₀ then Gv v else Fv v) v) (semiLocalHaar K L v) := by
    intro v₀ hv₀ v hv
    dsimp only
    split_ifs
    · exact hGv_meas v hv
    · exact hFv_meas v hv

  have hEA := hG S₁ FA Ga Fv hGa_meas hFv_meas hFAshape hFAvanish
  have hEV : ∀ v₀ ∈ S₁, ∫ x, FV v₀ x ∂μ = cG * (∫ y, Fa y ∂ν) *
      ∏ v ∈ S₁, ∫ y, (fun v => if v = v₀ then Gv v else Fv v) v y ∂(semiLocalHaar K L v) :=
    fun v₀ hv₀ => hG S₁ (FV v₀) Fa (fun v => if v = v₀ then Gv v else Fv v) hFa_meas (hmix_meas v₀ hv₀)
      (hFVshape v₀ hv₀) (hFVvanish v₀)

  obtain ⟨Ia, hIa⟩ : ∃ Ia : ℂ, Ia = ∫ x, φat φa (x⁻¹ * tensorArch K L δ * sigmaGL K L _ σ x) * (wa x : ℂ) ∂ν := ⟨_, rfl⟩
  obtain ⟨Ja, hJa⟩ : ∃ Ja : ℂ, Ja = ∫ x, φat φa (x⁻¹ * tensorArch K L δ * sigmaGL K L _ σ x) * (Wa x : ℂ) * (wa x : ℂ) ∂ν :=
    ⟨_, rfl⟩
  obtain ⟨Iv, hIv⟩ : ∃ Iv : HeightOneSpectrum (𝓞 K) → ℂ,
      Iv = fun v => if v ∈ S₁ then ∫ y, Fv v y ∂(semiLocalHaar K L v) else 1 := ⟨_, rfl⟩
  obtain ⟨Jv, hJv⟩ : ∃ Jv : HeightOneSpectrum (𝓞 K) → ℂ,
      Jv = fun v => if v ∈ S₁ then ∫ y, Gv v y ∂(semiLocalHaar K L v) else 0 := ⟨_, rfl⟩
  have hIa' : ∫ x, Fa x ∂ν = ((cT⁻¹ : ℝ) : ℂ) * Ia := by
    rw [hFa, hIa]; exact integral_const_mul _ _
  have hJa' : ∫ x, Ga x ∂ν = ((cT⁻¹ : ℝ) : ℂ) * Ja := by
    rw [hGa, hJa]; exact integral_const_mul _ _
  have hIv_of_mem : ∀ v ∈ S₁, Iv v = ∫ y, Fv v y ∂(semiLocalHaar K L v) := fun v hv => by
    rw [hIv]; dsimp only; rw [if_pos hv]
  have hIv_of_not_mem : ∀ v ∉ S₁, Iv v = 1 := fun v hv => by rw [hIv]; dsimp only; rw [if_neg hv]
  have hJv_of_mem : ∀ v ∈ S₁, Jv v = ∫ y, Gv v y ∂(semiLocalHaar K L v) := fun v hv => by
    rw [hJv]; dsimp only; rw [if_pos hv]
  have hJv_of_not_mem : ∀ v ∉ S₁, Jv v = 0 := fun v hv => by rw [hJv]; dsimp only; rw [if_neg hv]
  refine ⟨Ia, Iv, Ja, Jv, ⟨wa, hwa, hIa⟩, fun v => ?_, ⟨wa, hwa, hJa⟩, fun v => ?_, hJv_of_not_mem, fun T hT₁ => ?_⟩
  · by_cases hv : v ∈ S₁
    · exact ⟨wf v, hwf v hv, by rw [hIv_of_mem v hv, hFv]⟩
    · rw [hIv_of_not_mem v hv, φSp_of_not_mem S φS (fun h => hv (hSS₁ h))]
      exact unit_orbitalIntegral σ δ τf v (hδint₁ v hv) (hunit v hv)
  · by_cases hv : v ∈ S₁
    · exact ⟨wf v, hwf v hv, by rw [hJv_of_mem v hv, hGv]⟩
    · rw [hJv_of_not_mem v hv, φSp_of_not_mem S φS (fun h => hv (hSS₁ h))]
      exact unit_weightedOrbitalIntegral σ δ τf v (hunit v hv)
  ·
    have hprodT : ∏ v ∈ T, Iv v = ∏ v ∈ S₁, Iv v :=
      (Finset.prod_subset hT₁ (fun v _ hv => hIv_of_not_mem v hv)).symm
    have hprodTe : ∀ v ∈ S₁, ∏ u ∈ T.erase v, Iv u = ∏ u ∈ S₁.erase v, Iv u := fun v hv =>
      (Finset.prod_subset (Finset.erase_subset_erase v hT₁) (fun u huT hu => hIv_of_not_mem u
        (fun h => hu (Finset.mem_erase.2 ⟨(Finset.mem_erase.1 huT).1, h⟩)))).symm
    have hsumT : ∑ v ∈ T, Jv v * ∏ u ∈ T.erase v, Iv u = ∑ v ∈ S₁, Jv v * ∏ u ∈ S₁.erase v, Iv u := by
      rw [← Finset.sum_subset hT₁ (fun v _ hv => by rw [hJv_of_not_mem v hv, zero_mul])]
      exact Finset.sum_congr rfl fun v hv => by rw [hprodTe v hv]
    rw [hprodT, hsumT]

    have hsplit : (fun x => φt φ (x⁻¹ * δ * sigmaGL K L _ σ x) * (gW Wa x : ℂ) * (wt x : ℂ)) =
        fun x => FA x + ∑ v ∈ S₁, FV v x := by
      funext x
      by_cases hx : ∀ v ∉ S₁, tensorPlace K L v x ∈ semiLocalIntegralSet K L v
      · rw [gW_eq_of_integral Wa S₁ x hx, hFA, hFV]
        dsimp only
        push_cast
        rw [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
      · push Not at hx
        rw [hwt_of_not_mem x hx, hFAvanish x hx]
        simp only [Complex.ofReal_zero, mul_zero, zero_add]
        exact (Finset.sum_eq_zero fun v _ => hFVvanish v x hx).symm
    have hIA : Integrable FA μ := by rw [hFA]; exact hIntA
    have hIV : ∀ v ∈ S₁, Integrable (FV v) μ := fun v hv => by rw [hFV]; exact hIntV v hv
    rw [hJt, hsplit, integral_add hIA (integrable_finset_sum S₁ hIV), integral_finset_sum S₁ hIV, hEA, hJa']
    have hterm : ∀ v₀ ∈ S₁, ∫ x, FV v₀ x ∂μ = cG * (((cT⁻¹ : ℝ) : ℂ) * Ia) * (Jv v₀ * ∏ u ∈ S₁.erase v₀, Iv u) := by
      intro v₀ hv₀
      rw [hEV v₀ hv₀, hIa', ← Finset.mul_prod_erase S₁ _ hv₀]
      dsimp only
      rw [if_pos rfl, hJv_of_mem v₀ hv₀]
      congr 2
      refine Finset.prod_congr rfl fun u hu => ?_
      rw [if_neg (Finset.ne_of_mem_erase hu), hIv_of_mem u (Finset.mem_of_mem_erase hu)]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hprodS : ∏ v ∈ S₁, ∫ y, Fv v y ∂(semiLocalHaar K L v) = ∏ v ∈ S₁, Iv v :=
      Finset.prod_congr rfl fun v hv => (hIv_of_mem v hv).symm
    rw [hprodS]
    push_cast
    ring

include hσ hG hδ hτf hτf1 hcT hT hφ in

theorem weuler (Wa : Ht K L → ℝ) (hWac : Continuous Wa)
    (hWa : ∀ t : Ta' σ δ, ∀ x : Ht K L, Wa ((t : Ht K L) * x) = Wa x)
    (hWv : ∀ v : HeightOneSpectrum (𝓞 K), ∀ t : Tv' σ δ v, ∀ x : Gsl K L v,
      semiLocalWeight K L v ((t : Gsl K L v) * x) = semiLocalWeight K L v x)
    (J : ℂ) (hJ : IsTwistedWeightedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μ (gW Wa) δ τ (φt φ) J)
    (hne : ∃ x : Gt K L, φt φ (x⁻¹ * δ * sigmaGL K L _ σ x) ≠ 0) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S₁ ∧
      ∃ (Ia Ja : ℂ) (Iv Jv : HeightOneSpectrum (𝓞 K) → ℂ),
        IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ ν (tensorArch K L δ) τa (φat φa) Ia ∧
        IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ ν Wa (tensorArch K L δ) τa (φat φa) Ja ∧
        (∀ v, IsTwistedOrbitalIntegral K L v σ (tensorPlace K L v δ) (τf v) (φSp S φS v) (Iv v)) ∧
        (∀ v, IsTwistedWeightedOrbitalIntegral K L v σ (tensorPlace K L v δ) (τf v) (φSp S φS v) (Jv v)) ∧
        (∀ v ∉ S₁, Jv v = 0) ∧
        ∀ T : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ T →
          J = cG * cT⁻¹ * (Ja * ∏ v ∈ T, Iv v + Ia * ∑ v ∈ T, Jv v * ∏ u ∈ T.erase v, Iv u) := by
  haveI := hτf
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  haveI : SecondCountableTopology (L ⊗[K] AdeleRing (𝓞 K) K) := secondCountableTopology_TA
  haveI : SecondCountableTopology (Gt K L) := secondCountable_gl _
  haveI : LocallyCompactSpace (Gt K L) := locallyCompactSpace_tensorGL K L _

  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)), S₀ = S ∪ (finite_setOf_tensorPlace_not_mem δ).toFinset :=
    ⟨_, rfl⟩
  have hSS₀ : S ⊆ S₀ := by rw [hS₀]; exact Finset.subset_union_left
  have hδint : ∀ v ∉ S₀, tensorPlace K L v δ ∈ semiLocalIntegralSet K L v := by
    intro v hv
    by_contra h
    exact hv (by rw [hS₀]; exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h))
  obtain ⟨w, hw, hJw⟩ := hJ
  obtain ⟨⟨S₁, hS₀S₁, hunit⟩, hcpS, hcpnS, hcpa⟩ :=
    AutomorphicForm.exists_finset_forall_isTwistedSectionFnOn_indicator_semiLocalIntegralSet_of_isTwistedSectionFnOn_baseChange
      K L σ hσ δ hδ τ τf (fun v => inferInstance) hτf1 S₀ (φt φ) (φat φa) (φSp S φS)
      (fun x hx => shape_of_subset hφ hSS₀ x hx) (fun x hx => vanish_of_subset hφ hSS₀ x hx) ⟨w, hw⟩ hne
  have hSS₁ : S ⊆ S₁ := hSS₀.trans hS₀S₁
  have hδint₁ : ∀ v ∉ S₁, tensorPlace K L v δ ∈ semiLocalIntegralSet K L v := fun v hv => hδint v fun h => hv (hS₀S₁ h)
  have hloc : ∀ v : HeightOneSpectrum (𝓞 K), ∃ wv : Gsl K L v → ℝ,
      v ∈ S₁ → IsTwistedSectionFnOn K L (v.adicCompletion K) σ (tensorPlace K L v δ) (τf v) (φSp S φS v) wv := by
    intro v
    by_cases hv : v ∈ S₁
    · by_cases hv₀ : v ∈ S₀
      · obtain ⟨C, hC, hE⟩ := hcpS v hv₀
        obtain ⟨wv, hwv⟩ := exists_local_sectionFn σ hσ δ hδ τf v (φSp S φS v) C hC hE
        exact ⟨wv, fun _ => hwv⟩
      · obtain ⟨C, hC, hE⟩ := hcpnS v hv₀
        have hE' : {y : Gsl K L v | φSp S φS v (y⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ y) ≠ 0} ⊆
            (Tv' σ δ v : Set (Gsl K L v)) * C := by
          intro y hy
          apply hE
          rw [Set.mem_setOf_eq, φSp_of_not_mem S φS (fun h => hv₀ (hSS₀ h))] at hy
          simpa [Set.indicator_apply_ne_zero] using hy
        obtain ⟨wv, hwv⟩ := exists_local_sectionFn σ hσ δ hδ τf v (φSp S φS v) C hC hE'
        exact ⟨wv, fun _ => hwv⟩
    · exact ⟨fun _ => 0, fun h => absurd h hv⟩
  choose wf hwf using hloc
  obtain ⟨Ca, hCa, hEa⟩ := hcpa
  obtain ⟨wa, hwa⟩ := exists_arch_sectionFn σ hσ δ hδ τa (φat φa) Ca hCa hEa
  have hsec := AutomorphicForm.isTwistedSectionFnOn_baseChange_indicator_prod_of_forall_isTwistedSectionFnOn K L σ δ τ τa τf
    cT hcT hT S₁ (φt φ) (φat φa) (φSp S φS) (fun x hx => shape_of_subset hφ hSS₁ x hx)
    (fun x hx => vanish_of_subset hφ hSS₁ x hx) wa hwa wf (fun v hv => hwf v hv) (fun v hv => hunit v hv)
  obtain ⟨wt, hwt⟩ : ∃ wt : Gt K L → ℝ, wt = {x : Gt K L | ∀ v ∉ S₁, tensorPlace K L v x ∈ semiLocalIntegralSet K L v}.indicator
    fun x => cT⁻¹ * (wa (tensorArch K L x) * ∏ v ∈ S₁, wf v (tensorPlace K L v x)) := ⟨_, rfl⟩
  rw [← hwt] at hsec

  have hTc : IsClosed ((Ttw σ δ : Subgroup (Gt K L)) : Set (Gt K L)) := isClosed_twistedCentralizer K L _ σ δ
  haveI : τ.IsInvInvariant := isInvInvariant_of_comm (Ttw σ δ) hTc (twistedCentralizer_comm K L _ σ hσ hδ) τ

  set F : Gt K L → ℂ := fun x => φt φ (x⁻¹ * δ * sigmaGL K L _ σ x) with hF
  have hFm : Measurable F :=
    (continuous_φt hφ).measurable.comp (continuous_twistedConj _ _ (continuous_sigmaGL K L _ σ)).measurable
  have hFb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C := by
    obtain ⟨C, hC⟩ := bounded_φt hφ
    exact ⟨C, fun x => hC _⟩
  have hFT : ∀ (t : Ttw σ δ) (x : Gt K L), F ((t : Gt K L) * x) = F x := by
    intro t x
    have key : (t : Gt K L)⁻¹ * δ * sigmaGL K L (AdeleRing (𝓞 K) K) σ (t : Gt K L) = δ :=
      (mem_sigmaCentralizer_iff_inv).1 t.2
    have h' : ((t : Gt K L) * x)⁻¹ * δ * sigmaGL K L (AdeleRing (𝓞 K) K) σ ((t : Gt K L) * x) =
        x⁻¹ * δ * sigmaGL K L (AdeleRing (𝓞 K) K) σ x := by
      calc ((t : Gt K L) * x)⁻¹ * δ * sigmaGL K L (AdeleRing (𝓞 K) K) σ ((t : Gt K L) * x)
          = x⁻¹ * ((t : Gt K L)⁻¹ * δ * sigmaGL K L (AdeleRing (𝓞 K) K) σ (t : Gt K L)) *
              sigmaGL K L (AdeleRing (𝓞 K) K) σ x := by
            simp only [mul_inv_rev, map_mul, mul_assoc]
        _ = x⁻¹ * δ * sigmaGL K L (AdeleRing (𝓞 K) K) σ x := by rw [key]
    show φt φ (((t : Gt K L) * x)⁻¹ * δ * sigmaGL K L (AdeleRing (𝓞 K) K) σ ((t : Gt K L) * x)) =
      φt φ (x⁻¹ * δ * sigmaGL K L (AdeleRing (𝓞 K) K) σ x)
    rw [h']
  have hWaAc : Continuous fun x : Gt K L => Wa (tensorArch K L x) := hWac.comp (continuous_tensorArch K L)
  have hWaAT : ∀ (t : Ttw σ δ) (x : Gt K L), Wa (tensorArch K L ((t : Gt K L) * x)) = Wa (tensorArch K L x) := by
    intro t x
    rw [map_mul]
    exact hWa ⟨_, tensorArch_mem_twistedCentralizer σ t.2⟩ _
  have hWvc : ∀ v, Continuous fun x : Gt K L => semiLocalWeight K L v (tensorPlace K L v x) := fun v =>
    (continuous_semiLocalWeight v).comp (continuous_tensorPlace K L v)
  have hWvT : ∀ v (t : Ttw σ δ) (x : Gt K L),
      semiLocalWeight K L v (tensorPlace K L v ((t : Gt K L) * x)) = semiLocalWeight K L v (tensorPlace K L v x) := by
    intro v t x
    rw [map_mul]
    exact hWv v ⟨_, tensorPlace_mem_twistedCentralizer σ v t.2⟩ _
  have hgW : gW Wa = fun x => Wa (tensorArch K L x) + finWeight x := rfl
  have hWc : Continuous (gW Wa : Gt K L → ℝ) := by rw [hgW]; exact hWaAc.add continuous_finWeight
  have hWT : ∀ (t : Ttw σ δ) (x : Gt K L), gW Wa ((t : Gt K L) * x) = gW Wa x := by
    intro t x
    rw [hgW]
    dsimp only
    rw [hWaAT]
    congr 1
    exact finsum_congr fun v => hWvT v t x

  have hJt : J = ∫ x, φt φ (x⁻¹ * δ * sigmaGL K L _ σ x) * (gW Wa x : ℂ) * (wt x : ℂ) ∂μ := by
    rw [hJw]
    exact integral_mul_mul_eq_of_continuous_weight (Ttw σ δ) hTc μ τ F hFm hFb hFT (gW Wa) hWc hWT w wt hw hsec
  have hIntA : Integrable (fun x => φt φ (x⁻¹ * δ * sigmaGL K L _ σ x) * (Wa (tensorArch K L x) : ℂ) * (wt x : ℂ)) μ :=
    integrable_mul_mul_of_continuous_weight (Ttw σ δ) hTc μ τ F hFm hFb hFT
      (fun x => Wa (tensorArch K L x)) hWaAc hWaAT wt hsec
  have hIntV : ∀ v ∈ S₁, Integrable (fun x => φt φ (x⁻¹ * δ * sigmaGL K L _ σ x) *
      (semiLocalWeight K L v (tensorPlace K L v x) : ℂ) * (wt x : ℂ)) μ := fun v _ =>
    integrable_mul_mul_of_continuous_weight (Ttw σ δ) hTc μ τ F hFm hFb hFT
      (fun x => semiLocalWeight K L v (tensorPlace K L v x)) (hWvc v) (hWvT v) wt hsec
  obtain ⟨Ia, Iv, Ja, Jv, h1, h2, h3, h4, h5, h6⟩ := weuler_core σ μ ν cG hG δ τa τf cT S φ φa φf φS hφ S₁ hSS₁ hδint₁
    wa hwa wf hwf hunit wt hwt Wa hWac.measurable hIntA hIntV J hJt
  exact ⟨S₁, hSS₁, Ia, Ja, Iv, Jv, h1, h3, h2, h4, h5, h6⟩

end Euler

end AutomorphicForm.TwistedWeightedEuler
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isTwistedWeightedOrbitalIntegralOn_baseChange_eq_mul_sum_prod_of_isSemiLocalFactorization.AutomorphicForm P2MW.S_AutomorphicForm_exists_isTwistedWeightedOrbitalIntegralOn_baseChange_eq_mul_sum_prod_of_isSemiLocalFactorization.AutomorphicForm.TwistedWeightedEuler"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isTwistedWeightedOrbitalIntegralOn_baseChange_eq_mul_sum_prod_of_isSemiLocalFactorization.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isTwistedWeightedOrbitalIntegralOn_baseChange_eq_mul_sum_prod_of_isSemiLocalFactorization.AutomorphicForm P2MW.S_AutomorphicForm_exists_isTwistedWeightedOrbitalIntegralOn_baseChange_eq_mul_sum_prod_of_isSemiLocalFactorization.AutomorphicForm.TwistedWeightedEuler"

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_isTwistedWeightedOrbitalIntegralOn_baseChange_eq_mul_sum_prod_of_isSemiLocalFactorization.AutomorphicForm AutomorphicForm.TwistedWeightedEuler in
open Classical in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)
    (μ : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) μ)
    (ν : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
      (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (cG : ℝ)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (F : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ) (Fa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (FS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] Fa ν →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] (FS v)
          (AutomorphicForm.semiLocalHaar K L v)) →
        (∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v x ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            F x = Fa (AutomorphicForm.tensorArch K L x) *
              ∏ v ∈ S, FS v (AutomorphicForm.tensorPlace K L v x)) →
        (∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v x ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            F x = 0) →
          ∫ x, F x ∂μ = cG * (∫ y, Fa y ∂ν) * ∏ v ∈ S, ∫ y, FS v y ∂(AutomorphicForm.semiLocalHaar K L v))
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ))
    (τ : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ))
    (hτ : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ) τ)
    (τa : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
        (AutomorphicForm.tensorArch K L δ))
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
        (AutomorphicForm.tensorArch K L δ)))
    (hτa : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
        (AutomorphicForm.tensorArch K L δ)) τa)
    (τf : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ))
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)))
    (hτf : ∀ v : HeightOneSpectrum (𝓞 K), @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
        (AutomorphicForm.tensorPlace K L v δ)) (τf v))
    (hτf1 : ∀ v : HeightOneSpectrum (𝓞 K),
      τf v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (cT : ℝ) (hcT : 0 < cT)
    (hT : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ)
        (Wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L δ)] (fun t => Wa t) τa →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)] (fun t => WS v t) (τf v)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v t ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = Wa (AutomorphicForm.tensorArch K L t) *
              ∏ v ∈ S, WS v (AutomorphicForm.tensorPlace K L v t)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v t ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = 0) →
          ∫ t, W t ∂τ = cT * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v))

    (Wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ)
    (hWa : ∀ t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ),
      ∀ x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
        Wa ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) * x) = Wa x)
    (hWac : Continuous Wa)
    (hWam : AEStronglyMeasurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] (fun x => (Wa x : ℂ)) ν)
    (hWv : ∀ v : HeightOneSpectrum (𝓞 K),
      ∀ t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (AutomorphicForm.tensorPlace K L v δ),
      ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        AutomorphicForm.semiLocalWeight K L v ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * x) =
          AutomorphicForm.semiLocalWeight K L v x)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ : AutomorphicForm.IsSemiLocalFactorization K L S φ φa φf φS)
    (J : ℂ)
    (hJ : AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μ
      (fun x => Wa (AutomorphicForm.tensorArch K L x) +
        ∑ᶠ v : HeightOneSpectrum (𝓞 K), AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.tensorPlace K L v x))
      δ τ (φ ∘ AutomorphicForm.baseChangeGL K L) J) :
    (J = 0 ∧
      ((∀ x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
          φa (AutomorphicForm.archIdentGL K L (x⁻¹ * AutomorphicForm.tensorArch K L δ *
            AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ x)) = 0) ∨
        (∃ v ∈ S, ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
          φS v (x⁻¹ * AutomorphicForm.tensorPlace K L v δ *
            AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x) = 0) ∨
        (∃ v ∉ S, ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
          x⁻¹ * AutomorphicForm.tensorPlace K L v δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x ∉
            AutomorphicForm.semiLocalIntegralSet K L v))) ∨
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S₁ ∧
      ∃ (Ia Ja : ℂ) (Iv Jv : HeightOneSpectrum (𝓞 K) → ℂ),
        AutomorphicForm.IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ ν
          (AutomorphicForm.tensorArch K L δ) τa (φa ∘ AutomorphicForm.archIdentGL K L) Ia ∧
        AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ ν Wa
          (AutomorphicForm.tensorArch K L δ) τa (φa ∘ AutomorphicForm.archIdentGL K L) Ja ∧
        (∀ v ∈ S, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ
          (AutomorphicForm.tensorPlace K L v δ) (τf v) (φS v) (Iv v)) ∧
        (∀ v ∈ S, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ
          (AutomorphicForm.tensorPlace K L v δ) (τf v) (φS v) (Jv v)) ∧
        (∀ v ∉ S, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ
          (AutomorphicForm.tensorPlace K L v δ) (τf v)
          ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) (Iv v)) ∧
        (∀ v ∉ S, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ
          (AutomorphicForm.tensorPlace K L v δ) (τf v)
          ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) (Jv v)) ∧
        (∀ v ∉ S₁, Jv v = 0) ∧
        ∀ T : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ T →
          J = cG * cT⁻¹ * (Ja * ∏ v ∈ T, Iv v + Ia * ∑ v ∈ T, Jv v * ∏ u ∈ T.erase v, Iv u) := by
  haveI := hμ; haveI := hτ; haveI := hτa
  by_cases hne : ∃ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      φt φ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x) ≠ 0
  · right
    obtain ⟨S₁, hSS₁, Ia, Ja, Iv, Jv, hIa, hJa, hIv, hJv, hJ0, hJeq⟩ :=
      weuler σ hσ μ ν cG hG δ hδ τ τa τf hτf hτf1 cT hcT hT S φ φa φf φS hφ Wa hWac hWa hWv J hJ hne
    refine ⟨S₁, hSS₁, Ia, Ja, Iv, Jv, hIa, hJa, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_,
      hJ0, hJeq⟩
    · have h := hIv v
      rwa [φSp_of_mem S φS hv] at h
    · have h := hJv v
      rwa [φSp_of_mem S φS hv] at h
    · have h := hIv v
      rwa [φSp_of_not_mem S φS hv] at h
    · have h := hJv v
      rwa [φSp_of_not_mem S φS hv] at h
  · left
    refine ⟨?_, ?_⟩
    · obtain ⟨w, -, rfl⟩ := hJ
      push Not at hne
      have h0 : ∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          φ (AutomorphicForm.baseChangeGL K L (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x)) = 0 := hne
      simp only [Function.comp_apply, h0, zero_mul, integral_zero]
    · by_contra hcon
      push Not at hcon
      obtain ⟨ha, hS, hnS⟩ := hcon
      exact hne (exists_ne_zero_of_local σ hφ δ ha hS hnS)

end S_AutomorphicForm_exists_isTwistedWeightedOrbitalIntegralOn_baseChange_eq_mul_sum_prod_of_isSemiLocalFactorization
end P2MW
export P2MW.S_AutomorphicForm_exists_isTwistedWeightedOrbitalIntegralOn_baseChange_eq_mul_sum_prod_of_isSemiLocalFactorization (solution)
