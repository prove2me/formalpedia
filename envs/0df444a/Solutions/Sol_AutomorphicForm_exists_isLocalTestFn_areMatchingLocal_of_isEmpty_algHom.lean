-- Prove2me | solution 1 for AutomorphicForm.exists_isLocalTestFn_areMatchingLocal_of_isEmpty_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/d39b7d0c-3cb9-5e60-98e2-eb7f806a3613

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_MeasureTheory_exists_isLocallyConstant_integral_subgroup_mul_eq_one
import Theorems.Thm_AutomorphicForm_exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul
import Theorems.Thm_AutomorphicForm_exists_isSectionFn_and_isLocallyConstant_of_isRegularSemisimple_of_isLocalTestFn
import Theorems.Thm_AutomorphicForm_IsOrbitalIntegralOn_unique_of_isRegularSemisimple
import Theorems.Thm_AutomorphicForm_IsTwistedOrbitalIntegralOn_unique_of_isRegularSemisimple_normString
import Theorems.Thm_AutomorphicForm_exists_nhds_forall_exists_isLocalTestFn_areMatchingLocal_of_isRegularSemisimple_normString
import Theorems.Thm_AutomorphicForm_exists_nhds_forall_exists_isLocalTestFn_areMatchingLocal_of_not_isRegularSemisimple_normString
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatchingLocal_of_isEmpty_algHom
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace
open scoped TensorProduct TensorProduct.RightActions

section ModelBlock
p2m_open "AutomorphicForm Module TensorProduct.RightActions.Module"
p2m_open_scoped "TensorProduct TensorProduct.RightActions.Module.TensorProduct TensorProduct.RightActions"

namespace SplitModel

section Bridge

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (F : Type) [CommRing F] [Algebra K F] (ι : L →ₐ[K] F) (σ : L ≃ₐ[K] L) (n : ℕ)

private theorem sigmaTensor_tmul (x : L) (a : F) : sigmaTensor K L F σ (x ⊗ₜ a) = σ x ⊗ₜ a := by
  simp [sigmaTensor]

variable {σ n}

end Bridge

end SplitModel

end ModelBlock

section

open AutomorphicForm

namespace RegularCentralizer

section Ring

variable {A : Type*} [CommRing A]

private theorem exists_eq_smul_one_add_smul_of_mul_eq_mul {G X : Matrix (Fin 2) (Fin 2) A}
    (hd : IsUnit (Matrix.trace G ^ 2 - 4 * Matrix.det G)) (hX : X * G = G * X) :
    ∃ l m : A, X = l • (1 : Matrix (Fin 2) (Fin 2) A) + m • G := by
  rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hd
  obtain ⟨u, hu⟩ := hd
  have hu1 : (↑u⁻¹ : A) * ↑u = 1 := u.inv_mul
  have h00 : (X * G) 0 0 = (G * X) 0 0 := by rw [hX]
  have h01 : (X * G) 0 1 = (G * X) 0 1 := by rw [hX]
  have h10 : (X * G) 1 0 = (G * X) 1 0 := by rw [hX]
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  obtain ⟨Z, hZ⟩ : ∃ Z : A,
      Z = (G 0 0 - G 1 1) * (X 0 0 - X 1 1) + 2 * (G 1 0 * X 0 1 + G 0 1 * X 1 0) := ⟨_, rfl⟩
  refine ⟨X 0 0 - (↑u⁻¹ : A) * Z * G 0 0, (↑u⁻¹ : A) * Z, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simp
    linear_combination (-(X 0 1)) * hu1 + (X 0 1 * (↑u⁻¹ : A)) * hu -
      ((↑u⁻¹ : A) * (G 0 0 - G 1 1)) * h01 + (2 * (↑u⁻¹ : A) * G 0 1) * h00 -
      ((↑u⁻¹ : A) * G 0 1) * hZ
  · simp
    linear_combination (-(X 1 0)) * hu1 + (X 1 0 * (↑u⁻¹ : A)) * hu +
      ((↑u⁻¹ : A) * (G 0 0 - G 1 1)) * h10 - (2 * (↑u⁻¹ : A) * G 1 0) * h00 -
      ((↑u⁻¹ : A) * G 1 0) * hZ
  · simp
    linear_combination (X 0 0 - X 1 1) * hu1 - ((X 0 0 - X 1 1) * (↑u⁻¹ : A)) * hu -
      (2 * (↑u⁻¹ : A) * G 1 0) * h01 + (2 * (↑u⁻¹ : A) * G 0 1) * h10 +
      ((↑u⁻¹ : A) * (G 0 0 - G 1 1)) * hZ

private theorem commute_of_mul_eq_mul_of_mul_eq_mul {G X Y : Matrix (Fin 2) (Fin 2) A}
    (hd : IsUnit (Matrix.trace G ^ 2 - 4 * Matrix.det G)) (hX : X * G = G * X)
    (hY : Y * G = G * Y) :
    Commute X Y := by
  obtain ⟨l, m, rfl⟩ := exists_eq_smul_one_add_smul_of_mul_eq_mul hd hX
  obtain ⟨l', m', rfl⟩ := exists_eq_smul_one_add_smul_of_mul_eq_mul hd hY
  have c1 : Commute (1 : Matrix (Fin 2) (Fin 2) A) (l' • (1 : Matrix (Fin 2) (Fin 2) A) + m' • G) :=
    ((Commute.one_left _).smul_right l').add_right ((Commute.one_left G).smul_right m')
  have c2 : Commute G (l' • (1 : Matrix (Fin 2) (Fin 2) A) + m' • G) :=
    ((Commute.one_right G).smul_right l').add_right ((Commute.refl G).smul_right m')
  exact (c1.smul_left l).add_left (c2.smul_left m)

private theorem commute_of_mem_centralizer_of_isRegularSemisimple {g : GL (Fin 2) A}
    (hg : IsRegularSemisimple g) {x y : GL (Fin 2) A}
    (hx : x ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) A)))
    (hy : y ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) A))) : Commute x y := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx hy
  have hx' : (x : Matrix (Fin 2) (Fin 2) A) * g = g * x := congrArg Units.val hx
  have hy' : (y : Matrix (Fin 2) (Fin 2) A) * g = g * y := congrArg Units.val hy
  exact Units.ext (commute_of_mul_eq_mul_of_mul_eq_mul hg hx' hy').eq

private theorem isMulCommutative_centralizer_of_isRegularSemisimple {g : GL (Fin 2) A}
    (hg : IsRegularSemisimple g) :
    IsMulCommutative (Subgroup.centralizer ({g} : Set (GL (Fin 2) A))) :=
  ⟨⟨fun x y => Subtype.ext (commute_of_mem_centralizer_of_isRegularSemisimple hg x.2 y.2).eq⟩⟩

end Ring

end RegularCentralizer

end

section

open AutomorphicForm

namespace RegularCentralizer

section Generic

variable {G : Type*} [Group G]

private theorem mul_prod_range_iterate (f : G →* G) {t δ : G} (h : t * δ = δ * f t) (n : ℕ) :
    t * ((List.range n).map fun i => (⇑f)^[i] δ).prod =
      ((List.range n).map fun i => (⇑f)^[i] δ).prod * (⇑f)^[n] t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one, ← mul_assoc, ih, mul_assoc, mul_assoc, Function.iterate_succ_apply]
    congr 1
    have h' := congrArg ((⇑f)^[n]) h
    rwa [iterate_map_mul, iterate_map_mul] at h'

end Generic

section Twisted

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

private theorem twistedCentralizer_le_centralizer_normString_of_iterate (σ : L ≃ₐ[K] L)
    (hσ : ∀ t : GL (Fin 2) (L ⊗[K] A), (⇑(sigmaGL K L A σ))^[Module.finrank K L] t = t)
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    twistedCentralizer K L A σ δ ≤
      Subgroup.centralizer ({normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  intro t ht
  rw [Subgroup.mem_centralizer_singleton_iff]
  have ht' : t * δ * (sigmaGL K L A σ t)⁻¹ = δ := ht
  have key := mul_prod_range_iterate (sigmaGL K L A σ) (mul_inv_eq_iff_eq_mul.mp ht')
    (Module.finrank K L)
  rw [hσ t] at key
  exact key

private theorem sigmaTensor_mul_apply (σ σ' : L ≃ₐ[K] L) (z : L ⊗[K] A) :
    sigmaTensor K L A (σ * σ') z = sigmaTensor K L A σ (sigmaTensor K L A σ' z) := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro l a
    simp [sigmaTensor, Algebra.TensorProduct.map_tmul, AlgEquiv.mul_apply]
  · intro x y hx hy
    simp only [map_add, hx, hy]

private theorem sigmaTensor_one_apply (z : L ⊗[K] A) : sigmaTensor K L A 1 z = z := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro l a
    simp [sigmaTensor, Algebra.TensorProduct.map_tmul, AlgEquiv.one_apply]
  · intro x y hx hy
    simp only [map_add, hx, hy]

private theorem sigmaGL_mul_apply (σ σ' : L ≃ₐ[K] L) (g : GL (Fin 2) (L ⊗[K] A)) :
    sigmaGL K L A (σ * σ') g = sigmaGL K L A σ (sigmaGL K L A σ' g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show Matrix.GeneralLinearGroup.map (sigmaTensor K L A (σ * σ')) g i j =
    Matrix.GeneralLinearGroup.map (sigmaTensor K L A σ)
      (Matrix.GeneralLinearGroup.map (sigmaTensor K L A σ') g) i j
  simp only [Matrix.GeneralLinearGroup.map_apply, sigmaTensor_mul_apply]

private theorem sigmaGL_one_apply (g : GL (Fin 2) (L ⊗[K] A)) : sigmaGL K L A 1 g = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show Matrix.GeneralLinearGroup.map (sigmaTensor K L A 1) g i j = g i j
  simp only [Matrix.GeneralLinearGroup.map_apply, sigmaTensor_one_apply]

private theorem sigmaGL_iterate (σ : L ≃ₐ[K] L) (n : ℕ) (g : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(sigmaGL K L A σ))^[n] g = sigmaGL K L A (σ ^ n) g := by
  induction n with
  | zero => simp [sigmaGL_one_apply]
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', sigmaGL_mul_apply]

private theorem pow_finrank_eq_one [FiniteDimensional K L] (σ : L ≃ₐ[K] L) : σ ^ Module.finrank K L = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← Nat.card_zpowers, ← IntermediateField.finrank_fixedField_eq_card]
  exact Dvd.intro_left _
    (Module.finrank_mul_finrank K (IntermediateField.fixedField (Subgroup.zpowers σ)) L)

private theorem sigmaGL_iterate_finrank [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    (g : GL (Fin 2) (L ⊗[K] A)) : (⇑(sigmaGL K L A σ))^[Module.finrank K L] g = g := by
  rw [sigmaGL_iterate, pow_finrank_eq_one, sigmaGL_one_apply]

private theorem twistedCentralizer_le_centralizer_normString [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    twistedCentralizer K L A σ δ ≤
      Subgroup.centralizer ({normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) :=
  twistedCentralizer_le_centralizer_normString_of_iterate K L A σ
    (sigmaGL_iterate_finrank K L A σ) δ

end Twisted

end RegularCentralizer

end

section

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace TensorProduct Topology
open scoped TensorProduct.RightActions
open AutomorphicForm

namespace OrbitalCarriers

section TwistedClosed

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  (σ : L ≃ₐ[K] L)

private theorem isClosed_twistedCentralizer (hσc : Continuous (sigmaGL K L A σ))
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := isTopologicalRing_tensor K L A
  haveI := t2Space_tensorGL K L A
  have h : ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) = {t | t * δ * (sigmaGL K L A σ t)⁻¹ = δ} := by
    ext t
    exact mem_sigmaCentralizer_iff
  rw [h]
  exact isClosed_eq ((continuous_id.mul continuous_const).mul hσc.inv) continuous_const

end TwistedClosed

end OrbitalCarriers

end

section Tail
open AutomorphicForm
open MeasureTheory

private theorem isMulCommutative_of_le {G : Type} [Group G] {H₁ H₂ : Subgroup G} (hle : H₁ ≤ H₂)
    (hc : IsMulCommutative H₂) : IsMulCommutative H₁ :=
  ⟨⟨fun a b => Subtype.ext (congrArg (Subtype.val : H₂ → G)
    (hc.is_comm.comm (⟨a.1, hle a.2⟩ : H₂) ⟨b.1, hle b.2⟩))⟩⟩

section SigmaContinuous

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)

omit [IsTopologicalRing A] in
private theorem continuous_sigmaTensor : Continuous (sigmaTensor K L A σ) := by
  have hs : ∀ (a : A) (x : L) (b : A), a • (x ⊗ₜ[K] b : L ⊗[K] A) = x ⊗ₜ (a * b) := by
    intro a x b
    simp only [TensorProduct.RightActions.smul_def, TensorProduct.comm_tmul]
    rw [TensorProduct.smul_tmul']
    simp only [smul_eq_mul, TensorProduct.comm_symm_tmul]
  let f : L ⊗[K] A →ₗ[A] L ⊗[K] A :=
    { toFun := sigmaTensor K L A σ
      map_add' := fun x y => map_add (sigmaTensor K L A σ) x y
      map_smul' := fun a z => by
        rw [RingHom.id_apply]
        induction z with
        | zero => rw [smul_zero, map_zero, smul_zero]
        | tmul x b => rw [hs, SplitModel.sigmaTensor_tmul K L A σ, SplitModel.sigmaTensor_tmul K L A σ, hs]
        | add y w hy hw => rw [smul_add, map_add, map_add, smul_add, hy, hw] }
  exact IsModuleTopology.continuous_of_linearMap f

omit [IsTopologicalRing A] in
private theorem continuous_sigmaGL : Continuous (sigmaGL K L A σ) := by
  rw [Units.continuous_iff]
  exact ⟨Units.continuous_val.matrix_map (continuous_sigmaTensor K L A σ),
    Units.continuous_coe_inv.matrix_map (continuous_sigmaTensor K L A σ)⟩

end SigmaContinuous

end Tail

section OwnF5

open AutomorphicForm

variable (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K))

private theorem add_mem_semiLocalIntegers {a b : L ⊗[K] v.adicCompletion K} (ha : a ∈ semiLocalIntegers K L v)
    (hb : b ∈ semiLocalIntegers K L v) : a + b ∈ semiLocalIntegers K L v := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x + y, map_add _ _ _⟩

private theorem mul_mem_semiLocalIntegers {a b : L ⊗[K] v.adicCompletion K} (ha : a ∈ semiLocalIntegers K L v)
    (hb : b ∈ semiLocalIntegers K L v) : a * b ∈ semiLocalIntegers K L v := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x * y, map_mul _ _ _⟩

private theorem matrix_mul_mem {g h : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hg : ∀ i j, g i j ∈ semiLocalIntegers K L v) (hh : ∀ i j, h i j ∈ semiLocalIntegers K L v) :
    ∀ i j, (g * h) i j ∈ semiLocalIntegers K L v := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact add_mem_semiLocalIntegers K L v (mul_mem_semiLocalIntegers K L v (hg i 0) (hh 0 j))
    (mul_mem_semiLocalIntegers K L v (hg i 1) (hh 1 j))

private def semiLocalIntegralSubgroup : Subgroup (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) where
  carrier := semiLocalIntegralSet K L v
  one_mem' := one_mem_semiLocalIntegralSet K L v
  mul_mem' := by
    intro g h hg hh
    obtain ⟨hg1, hg2⟩ := mem_integralUnitsSet.mp hg
    obtain ⟨hh1, hh2⟩ := mem_integralUnitsSet.mp hh
    refine mem_integralUnitsSet.mpr ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact matrix_mul_mem K L v hg1 hh1
    · rw [mul_inv_rev, Units.val_mul]
      exact matrix_mul_mem K L v hh2 hg2
  inv_mem' := by
    intro g hg
    obtain ⟨hg1, hg2⟩ := mem_integralUnitsSet.mp hg
    refine mem_integralUnitsSet.mpr ⟨hg2, ?_⟩
    rw [inv_inv]
    exact hg1

end OwnF5

section OwnAdapter

open AutomorphicForm

private theorem twistedCentralizer_forall_mul_comm (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) {δ : GL (Fin 2) (L ⊗[K] A)}
    (hδ : IsRegularSemisimple (normString K L A σ δ)) :
    ∀ s ∈ twistedCentralizer K L A σ δ, ∀ t ∈ twistedCentralizer K L A σ δ, s * t = t * s := by
  have hc : IsMulCommutative (twistedCentralizer K L A σ δ) :=
    isMulCommutative_of_le (RegularCentralizer.twistedCentralizer_le_centralizer_normString K L A σ δ)
      (RegularCentralizer.isMulCommutative_centralizer_of_isRegularSemisimple hδ)
  intro s hs t ht
  exact congrArg Subtype.val (hc.is_comm.comm (⟨s, hs⟩ : twistedCentralizer K L A σ δ) ⟨t, ht⟩)

end OwnAdapter

section OwnGlue

open AutomorphicForm

private theorem exists_isTwistedSectionFnOn_and_isLocallyConstant_glue
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    [@Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ']
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : IsSemiLocalTestFn K L v φv) :
    ∃ w : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ,
      IsTwistedSectionFnOn K L (v.adicCompletion K) σ δ τ' φv w ∧ IsLocallyConstant w := by
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  letI := twistedCentralizerBorel K L (v.adicCompletion K) σ δ
  haveI : BorelSpace (twistedCentralizer K L (v.adicCompletion K) σ δ) := ⟨rfl⟩
  obtain ⟨Ω, hΩ, hcover⟩ := exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul K L v σ δ hδ
    (tsupport φv) hφv.2
  obtain ⟨w, hw0, hwlc, hwcs, hw1⟩ := MeasureTheory.exists_isLocallyConstant_integral_subgroup_mul_eq_one
    (semiLocalIntegralSubgroup K L v) (isCompact_semiLocalIntegralSet K L v) (isOpen_semiLocalIntegralSet K L v)
    (twistedCentralizer K L (v.adicCompletion K) σ δ)
    (OrbitalCarriers.isClosed_twistedCentralizer K L (v.adicCompletion K) σ
      (continuous_sigmaGL K L (v.adicCompletion K) σ) δ)
    (twistedCentralizer_forall_mul_comm K L (v.adicCompletion K) σ hδ) τ' Ω hΩ
  refine ⟨w, ⟨hw0, ?_, hwcs, fun x hx => hw1 x (hcover x (subset_tsupport φv hx))⟩, hwlc⟩
  letI := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  exact hwlc.continuous.measurable

end OwnGlue

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace TensorProduct
open scoped TensorProduct.RightActions
open AutomorphicForm

namespace TestFn

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

private theorem measurable_and_bounded_of_isLocalTestFn {fv : GL (Fin 2) (v.adicCompletion K) → ℂ}
    (h : IsLocalTestFn K v fv) :
    @Measurable _ _ (glBorelOf (v.adicCompletion K)) _ fv ∧ ∃ C : ℝ, ∀ g, ‖fv g‖ ≤ C := by
  letI := glBorelOf (v.adicCompletion K)
  haveI := borelSpace_glBorelOf (v.adicCompletion K)
  exact ⟨h.1.continuous.measurable, h.1.continuous.bounded_above_of_compact_support h.2⟩

private theorem measurable_and_bounded_of_isSemiLocalTestFn {φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (h : IsSemiLocalTestFn K L v φv) :
    @Measurable _ _ (glBorelOf (L ⊗[K] v.adicCompletion K)) _ φv ∧ ∃ C : ℝ, ∀ g, ‖φv g‖ ≤ C := by
  letI := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  exact ⟨h.1.continuous.measurable, h.1.continuous.bounded_above_of_compact_support h.2⟩

private theorem isLocalTestFn_norm {fv : GL (Fin 2) (v.adicCompletion K) → ℂ} (h : IsLocalTestFn K v fv) :
    IsLocalTestFn K v fun g => ((‖fv g‖ : ℝ) : ℂ) := by
  have h1 : IsLocallyConstant ((fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) ∘ fv) := h.1.comp _
  have h2 : HasCompactSupport ((fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) ∘ fv) := h.2.comp_left (by simp)
  exact ⟨h1, h2⟩

private theorem isSemiLocalTestFn_norm {φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (h : IsSemiLocalTestFn K L v φv) : IsSemiLocalTestFn K L v fun g => ((‖φv g‖ : ℝ) : ℂ) := by
  have h1 : IsLocallyConstant ((fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) ∘ φv) := h.1.comp _
  have h2 : HasCompactSupport ((fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) ∘ φv) := h.2.comp_left (by simp)
  exact ⟨h1, h2⟩

end TestFn

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace TensorProduct Topology Filter
open scoped TensorProduct.RightActions

noncomputable section

namespace LocalTransferCore

open AutomorphicForm

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)

section TestFn

omit σ in
private theorem isSemiLocalTestFn_add {φ ψ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (hφ : IsSemiLocalTestFn K L v φ) (hψ : IsSemiLocalTestFn K L v ψ) :
    IsSemiLocalTestFn K L v (φ + ψ) :=
  ⟨hφ.1.add hψ.1, hφ.2.add hψ.2⟩

private theorem isLocalTestFn_add {f g : GL (Fin 2) (v.adicCompletion K) → ℂ}
    (hf : IsLocalTestFn K v f) (hg : IsLocalTestFn K v g) : IsLocalTestFn K v (f + g) :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

private theorem isSemiLocalTestFn_indicator_mul {W : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))}
    (hW : IsClopen W) {φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (hφ : IsSemiLocalTestFn K L v φ) :
    IsSemiLocalTestFn K L v (fun x => W.indicator (fun _ => (1 : ℂ)) x * φ x) :=
  ⟨(isLocallyConstant_indicator_one hW.isOpen hW.isClosed).mul hφ.1, hφ.2.mul_left⟩

private theorem isSemiLocalTestFn_norm_add_norm {φ ψ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (hφ : IsSemiLocalTestFn K L v φ) (hψ : IsSemiLocalTestFn K L v ψ) :
    IsSemiLocalTestFn K L v (fun x => ((‖φ x‖ : ℝ) : ℂ) + ((‖ψ x‖ : ℝ) : ℂ)) :=
  ⟨((hφ.1.comp fun z => ((‖z‖ : ℝ) : ℂ)).add (hψ.1.comp fun z => ((‖z‖ : ℝ) : ℂ))),
    (hφ.2.norm.comp_left Complex.ofReal_zero).add (hψ.2.norm.comp_left Complex.ofReal_zero)⟩

private theorem isLocalTestFn_norm_add_norm {f g : GL (Fin 2) (v.adicCompletion K) → ℂ}
    (hf : IsLocalTestFn K v f) (hg : IsLocalTestFn K v g) :
    IsLocalTestFn K v (fun x => ((‖f x‖ : ℝ) : ℂ) + ((‖g x‖ : ℝ) : ℂ)) :=
  ⟨((hf.1.comp fun z => ((‖z‖ : ℝ) : ℂ)).add (hg.1.comp fun z => ((‖z‖ : ℝ) : ℂ))),
    (hf.2.norm.comp_left Complex.ofReal_zero).add (hg.2.norm.comp_left Complex.ofReal_zero)⟩

private theorem norm_add_norm_ne_zero_left {X : Type} {φ ψ : X → ℂ} {z : X} (h : φ z ≠ 0) :
    ((‖φ z‖ : ℝ) : ℂ) + ((‖ψ z‖ : ℝ) : ℂ) ≠ 0 := by
  rw [← Complex.ofReal_add, Complex.ofReal_ne_zero]
  exact (add_pos_of_pos_of_nonneg (norm_pos_iff.2 h) (norm_nonneg _)).ne'

private theorem norm_add_norm_ne_zero_right {X : Type} {φ ψ : X → ℂ} {z : X} (h : ψ z ≠ 0) :
    ((‖φ z‖ : ℝ) : ℂ) + ((‖ψ z‖ : ℝ) : ℂ) ≠ 0 := by
  rw [add_comm]
  exact norm_add_norm_ne_zero_left h

private theorem norm_add_norm_ne_zero_add {X : Type} {φ ψ : X → ℂ} {z : X} (h : (φ + ψ) z ≠ 0) :
    ((‖φ z‖ : ℝ) : ℂ) + ((‖ψ z‖ : ℝ) : ℂ) ≠ 0 := by
  by_cases hφ : φ z = 0
  · have hψ : ψ z ≠ 0 := by
      intro hψ; apply h; simp [hφ, hψ]
    exact norm_add_norm_ne_zero_right hψ
  · exact norm_add_norm_ne_zero_left hφ

end TestFn

section Hyps

private def UUniq : Prop :=
  ∀ γ : GL (Fin 2) (v.adicCompletion K), IsRegularSemisimple γ →
  ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ),
    @Measure.IsHaarMeasure _ _ _ (centralizerBorel (v.adicCompletion K) γ) τ →
  ∀ f : GL (Fin 2) (v.adicCompletion K) → ℂ, IsLocalTestFn K v f →
  ∀ I₁ I₂ : ℂ, IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ f I₁ →
    IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ f I₂ → I₁ = I₂

private def TUniq : Prop :=
  ∀ δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
    IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ) →
  ∀ τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ),
    @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ' →
  ∀ φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ, IsSemiLocalTestFn K L v φ →
  ∀ I₁ I₂ : ℂ,
    IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' φ I₁ →
    IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' φ I₂ → I₁ = I₂

private def ULC : Prop :=
  ∀ γ : GL (Fin 2) (v.adicCompletion K), IsRegularSemisimple γ →
  ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ),
    @Measure.IsHaarMeasure _ _ _ (centralizerBorel (v.adicCompletion K) γ) τ →
  ∀ f : GL (Fin 2) (v.adicCompletion K) → ℂ, IsLocalTestFn K v f →
  ∃ w : GL (Fin 2) (v.adicCompletion K) → ℝ,
    IsSectionFnOn (v.adicCompletion K) γ τ f w ∧ IsLocallyConstant w

private def TLC : Prop :=
  ∀ δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
    IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ) →
  ∀ τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ),
    @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ' →
  ∀ φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ, IsSemiLocalTestFn K L v φ →
  ∃ w : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ,
    IsTwistedSectionFnOn K L (v.adicCompletion K) σ δ τ' φ w ∧ IsLocallyConstant w

private def Loc : Prop :=
  ∀ δ₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
    ∃ U ∈ 𝓝 δ₀, ∀ φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ,
      IsSemiLocalTestFn K L v φ → tsupport φ ⊆ U →
        ∃ f : GL (Fin 2) (v.adicCompletion K) → ℂ, IsLocalTestFn K v f ∧ AreMatchingLocal K L v σ φ f

end Hyps

section Patch

private theorem twisted_split (hσc : Continuous (sigmaGL K L (v.adicCompletion K) σ))
    (hTLC : TLC K L v σ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    {φ ψ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (hφ : IsSemiLocalTestFn K L v φ) (hψ : IsSemiLocalTestFn K L v ψ) :
    ∃ I₁ I₂ : ℂ,
      IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' φ I₁ ∧
      IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' ψ I₂ ∧
      IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' (φ + ψ)
        (I₁ + I₂) := by
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := isHaarMeasure_semiLocalHaar K L v
  obtain ⟨w, hw, hwlc⟩ := hTLC δ hδ τ' hτ' _ (isSemiLocalTestFn_norm_add_norm K L v hφ hψ)
  obtain ⟨hw0, hwm, hwc, hw1⟩ := hw
  have hsec : ∀ θ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ,
      (∀ z, θ z ≠ 0 → ((‖φ z‖ : ℝ) : ℂ) + ((‖ψ z‖ : ℝ) : ℂ) ≠ 0) →
      IsTwistedSectionFnOn K L (v.adicCompletion K) σ δ τ' θ w :=
    fun θ hθ => ⟨hw0, hwm, hwc, fun x hx => hw1 x (hθ _ hx)⟩
  have horb : Continuous fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
      x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x :=
    (continuous_id.inv.mul continuous_const).mul hσc
  have hint : ∀ θ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ, IsSemiLocalTestFn K L v θ →
      Integrable (fun x => θ (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) * (w x : ℂ))
        (semiLocalHaar K L v) := fun θ hθ =>
    Continuous.integrable_of_hasCompactSupport
      ((hθ.1.continuous.comp horb).mul (Complex.continuous_ofReal.comp hwlc.continuous))
      (hwc.comp_left Complex.ofReal_zero).mul_left
  refine ⟨_, _, ⟨w, hsec φ fun z hz => norm_add_norm_ne_zero_left hz, rfl⟩,
    ⟨w, hsec ψ fun z hz => norm_add_norm_ne_zero_right hz, rfl⟩,
    ⟨w, hsec (φ + ψ) fun z hz => norm_add_norm_ne_zero_add hz, ?_⟩⟩
  simp only [Pi.add_apply, add_mul]
  exact (integral_add (hint φ hφ) (hint ψ hψ)).symm

private theorem untwisted_split (hLC : ULC K v)
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel (v.adicCompletion K) γ) τ)
    {f g : GL (Fin 2) (v.adicCompletion K) → ℂ}
    (hf : IsLocalTestFn K v f) (hg : IsLocalTestFn K v g) :
    ∃ I₁ I₂ : ℂ,
      IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ f I₁ ∧
      IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ g I₂ ∧
      IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ (f + g) (I₁ + I₂) := by
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := glBorelOf (v.adicCompletion K)
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion K)) := borelSpace_glBorelOf (v.adicCompletion K)
  haveI := isHaarMeasure_localHaar K v
  obtain ⟨w, hw, hwlc⟩ := hLC γ hγ τ hτ _ (isLocalTestFn_norm_add_norm K v hf hg)
  obtain ⟨hw0, hwm, hwc, hw1⟩ := hw
  have hsec : ∀ θ : GL (Fin 2) (v.adicCompletion K) → ℂ,
      (∀ z, θ z ≠ 0 → ((‖f z‖ : ℝ) : ℂ) + ((‖g z‖ : ℝ) : ℂ) ≠ 0) →
      IsSectionFnOn (v.adicCompletion K) γ τ θ w :=
    fun θ hθ => ⟨hw0, hwm, hwc, fun x hx => hw1 x (hθ _ hx)⟩
  have horb : Continuous fun x : GL (Fin 2) (v.adicCompletion K) => x⁻¹ * γ * x :=
    (continuous_id.inv.mul continuous_const).mul continuous_id
  have hint : ∀ θ : GL (Fin 2) (v.adicCompletion K) → ℂ, IsLocalTestFn K v θ →
      Integrable (fun x => θ (x⁻¹ * γ * x) * (w x : ℂ)) (localHaar K v) := fun θ hθ =>
    Continuous.integrable_of_hasCompactSupport
      ((hθ.1.continuous.comp horb).mul (Complex.continuous_ofReal.comp hwlc.continuous))
      (hwc.comp_left Complex.ofReal_zero).mul_left
  refine ⟨_, _, ⟨w, hsec f fun z hz => norm_add_norm_ne_zero_left hz, rfl⟩,
    ⟨w, hsec g fun z hz => norm_add_norm_ne_zero_right hz, rfl⟩,
    ⟨w, hsec (f + g) fun z hz => norm_add_norm_ne_zero_add hz, ?_⟩⟩
  simp only [Pi.add_apply, add_mul]
  exact (integral_add (hint f hf) (hint g hg)).symm

private theorem areMatchingLocal_add (hσc : Continuous (sigmaGL K L (v.adicCompletion K) σ))
    (hU : UUniq K v) (hT : TUniq K L v σ) (hLC : ULC K v) (hTLC : TLC K L v σ)
    {φ ψ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ} {f g : GL (Fin 2) (v.adicCompletion K) → ℂ}
    (hφ : IsSemiLocalTestFn K L v φ) (hψ : IsSemiLocalTestFn K L v ψ)
    (hf : IsLocalTestFn K v f) (hg : IsLocalTestFn K v g)
    (h₁ : AreMatchingLocal K L v σ φ f) (h₂ : AreMatchingLocal K L v σ ψ g) :
    AreMatchingLocal K L v σ (φ + ψ) (f + g) := by
  obtain ⟨h₁a, h₁b⟩ := h₁
  obtain ⟨h₂a, h₂b⟩ := h₂
  refine ⟨fun δ hδ γ hγ y hy τ τ' hτ hτ' hc I I' hI' hI => ?_, fun γ hγ hnn τ hτ I hI => ?_⟩
  · obtain ⟨J₁, J₂, hJ₁, hJ₂, hJ⟩ := twisted_split K L v σ hσc hTLC δ hδ τ' hτ' hφ hψ
    obtain ⟨I₁, I₂, hI₁, hI₂, hI12⟩ := untwisted_split K v hLC γ hγ τ hτ hf hg
    have e1 : I' = J₁ + J₂ :=
      hT δ hδ τ' hτ' (φ + ψ) (isSemiLocalTestFn_add K L v hφ hψ) I' (J₁ + J₂) hI' hJ
    have e2 : I = I₁ + I₂ := hU γ hγ τ hτ (f + g) (isLocalTestFn_add K v hf hg) I (I₁ + I₂) hI hI12
    rw [e1, e2, h₁a δ hδ γ hγ y hy τ τ' hτ hτ' hc I₁ J₁ hJ₁ hI₁,
      h₂a δ hδ γ hγ y hy τ τ' hτ hτ' hc I₂ J₂ hJ₂ hI₂]
  · obtain ⟨I₁, I₂, hI₁, hI₂, hI12⟩ := untwisted_split K v hLC γ hγ τ hτ hf hg
    rw [hU γ hγ τ hτ (f + g) (isLocalTestFn_add K v hf hg) I (I₁ + I₂) hI hI12,
      h₁b γ hγ hnn τ hτ I₁ hI₁, h₂b γ hγ hnn τ hτ I₂ hI₂, add_zero]

end Patch

section Clopen

omit σ in
private theorem totallyDisconnectedSpace_tensor :
    TotallyDisconnectedSpace (L ⊗[K] v.adicCompletion K) := by
  let b := Module.finBasis (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)
  let e : (L ⊗[K] v.adicCompletion K) ≃ₗ[v.adicCompletion K]
      (Fin (Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)) → v.adicCompletion K) :=
    b.equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hes : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : (L ⊗[K] v.adicCompletion K) ≃ₜ
      (Fin (Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)) → v.adicCompletion K) :=
    { e with continuous_toFun := he, continuous_invFun := hes }
  exact ⟨h.isEmbedding.isTotallyDisconnected (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

omit σ in
private theorem totallyDisconnectedSpace_tensorGL :
    TotallyDisconnectedSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := by
  haveI := totallyDisconnectedSpace_tensor K L v
  haveI : TotallyDisconnectedSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin 2 → Fin 2 → L ⊗[K] v.adicCompletion K))
  haveI : TotallyDisconnectedSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))ᵐᵒᵖ :=
    ⟨MulOpposite.opHomeomorph.symm.isEmbedding.isTotallyDisconnected
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  exact ⟨Units.isEmbedding_embedProduct.isTotallyDisconnected
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

omit σ in
private theorem exists_isClopen_mem_subset (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (U : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) (hU : U ∈ 𝓝 x) :
    ∃ V : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)), IsClopen V ∧ x ∈ V ∧ V ⊆ U := by
  haveI := t2Space_tensorGL K L (v.adicCompletion K)
  haveI := locallyCompactSpace_tensorGL K L (v.adicCompletion K)
  haveI := totallyDisconnectedSpace_tensorGL K L v
  obtain ⟨V, hV, hxV, hVU⟩ := (loc_compact_Haus_tot_disc_of_zero_dim
    (H := GL (Fin 2) (L ⊗[K] v.adicCompletion K))).mem_nhds_iff.1 hU
  exact ⟨V, hV, hxV, hVU⟩

end Clopen

section Assembly

private theorem exists_transfer_of_loc (hσc : Continuous (sigmaGL K L (v.adicCompletion K) σ))
    (hU : UUniq K v) (hT : TUniq K L v σ) (hLC : ULC K v) (hTLC : TLC K L v σ)
    (hLoc : Loc K L v σ)
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφ : IsSemiLocalTestFn K L v φ) :
    ∃ f : GL (Fin 2) (v.adicCompletion K) → ℂ, IsLocalTestFn K v f ∧ AreMatchingLocal K L v σ φ f := by
  classical
  choose U hUn hP using hLoc
  choose V hVc hxV hVU using fun x => exists_isClopen_mem_subset K L v x (U x) (hUn x)
  have claim : ∀ t : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      ∀ θ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ, IsSemiLocalTestFn K L v θ →
        tsupport θ ⊆ ⋃ x ∈ t, V x →
          ∃ f : GL (Fin 2) (v.adicCompletion K) → ℂ,
            IsLocalTestFn K v f ∧ AreMatchingLocal K L v σ θ f := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · intro θ hθ hsub
      have hθ0 : θ = fun _ => 0 := by
        funext x
        by_contra hx
        have hx' : x ∈ tsupport θ := subset_tsupport θ hx
        simpa using hsub hx'
      subst hθ0
      exact ⟨fun _ => 0, isLocalTestFn_zero K v, areMatchingLocal_zero K L v σ⟩
    · intro a s ha ih θ hθ hsub
      set θ₁ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ :=
        fun x => (V a).indicator (fun _ => (1 : ℂ)) x * θ x with hθ₁def
      set θ₂ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ :=
        fun x => (V a)ᶜ.indicator (fun _ => (1 : ℂ)) x * θ x with hθ₂def
      have hθ₁ : IsSemiLocalTestFn K L v θ₁ := isSemiLocalTestFn_indicator_mul K L v (hVc a) hθ
      have hθ₂ : IsSemiLocalTestFn K L v θ₂ :=
        isSemiLocalTestFn_indicator_mul K L v (hVc a).compl hθ
      have h1 : tsupport θ₁ ⊆ U a :=
        (tsupport_mul_subset_left.trans
          (closure_minimal (Set.support_indicator_subset) (hVc a).isClosed)).trans (hVU a)
      have h2 : tsupport θ₂ ⊆ ⋃ x ∈ s, V x := by
        intro z hz
        have hz1 : z ∈ tsupport θ := tsupport_mul_subset_right hz
        have hz2 : z ∈ (V a)ᶜ :=
          closure_minimal (Set.support_indicator_subset) (hVc a).compl.isClosed
            (tsupport_mul_subset_left hz)
        have hz3 := hsub hz1
        rw [Finset.set_biUnion_insert] at hz3
        exact hz3.resolve_left hz2
      obtain ⟨f₁, hf₁, hm₁⟩ := hP a θ₁ hθ₁ h1
      obtain ⟨f₂, hf₂, hm₂⟩ := ih θ₂ hθ₂ h2
      have hθ12 : θ₁ + θ₂ = θ := by
        funext x
        simp only [hθ₁def, hθ₂def, Pi.add_apply]
        by_cases hx : x ∈ V a <;> simp [hx]
      exact ⟨f₁ + f₂, isLocalTestFn_add K v hf₁ hf₂,
        hθ12 ▸ areMatchingLocal_add K L v σ hσc hU hT hLC hTLC hθ₁ hθ₂ hf₁ hf₂ hm₁ hm₂⟩
  obtain ⟨t, ht⟩ := hφ.2.elim_finite_subcover (fun x => V x) (fun x => (hVc x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  exact claim t φ hφ ht

end Assembly

section Discharge

private theorem uuniq_holds : UUniq K v := by
  intro γ hγ τ hτ f hf I₁ I₂ h₁ h₂
  obtain ⟨hfm, hfb⟩ := TestFn.measurable_and_bounded_of_isLocalTestFn K v hf
  exact IsOrbitalIntegralOn.unique_of_isRegularSemisimple (v.adicCompletion K) (localHaar K v)
    (isHaarMeasure_localHaar K v) γ hγ τ hτ f hfm hfb h₁ h₂

private theorem tuniq_holds : TUniq K L v σ := by
  intro δ hδ τ' hτ' φ hφ I₁ I₂ h₁ h₂
  obtain ⟨hφm, hφb⟩ := TestFn.measurable_and_bounded_of_isSemiLocalTestFn K L v hφ
  exact IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString K L (v.adicCompletion K) σ
    (RegularCentralizer.pow_finrank_eq_one K L σ) (semiLocalHaar K L v) (isHaarMeasure_semiLocalHaar K L v)
    δ hδ τ' hτ' φ hφm hφb h₁ h₂

private theorem ulc_holds : ULC K v := by
  intro γ hγ τ hτ f hf
  obtain ⟨w, hw, hlc⟩ :=
    @exists_isSectionFn_and_isLocallyConstant_of_isRegularSemisimple_of_isLocalTestFn K _ _ v γ hγ τ hτ f hf
  exact ⟨w, hw, hlc⟩

private theorem tlc_holds : TLC K L v σ := by
  intro δ hδ τ' hτ' φ hφ
  exact @exists_isTwistedSectionFnOn_and_isLocallyConstant_glue K L _ _ _ _ _ v σ δ hδ τ' hτ' φ hφ

private theorem pre_solution (hLoc : Loc K L v σ)
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : IsSemiLocalTestFn K L v φv) :
    ∃ fv : GL (Fin 2) (v.adicCompletion K) → ℂ, IsLocalTestFn K v fv ∧ AreMatchingLocal K L v σ φv fv :=
  exists_transfer_of_loc K L v σ (continuous_sigmaGL K L (v.adicCompletion K) σ) (uuniq_holds K v)
    (tuniq_holds K L v σ) (ulc_holds K v) (tlc_holds K L v σ) hLoc φv hφv

end Discharge

end LocalTransferCore

open AutomorphicForm in
private theorem solution_of_children
    (hreg : ∀
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : Module.finrank K L = 2 ∨ Module.finrank K L = 3) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) (hι : IsEmpty (L →ₐ[K] v.adicCompletion K))
    (δ₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ₀ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δ₀)),
    ∃ U ∈ nhds δ₀, ∀ φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ,
      AutomorphicForm.IsSemiLocalTestFn K L v φv → tsupport φv ⊆ U →
        ∃ fv : GL (Fin 2) (v.adicCompletion K) → ℂ,
          AutomorphicForm.IsLocalTestFn K v fv ∧ AutomorphicForm.AreMatchingLocal K L v σ φv fv)
    (hsing : ∀
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : Module.finrank K L = 2 ∨ Module.finrank K L = 3) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) (hι : IsEmpty (L →ₐ[K] v.adicCompletion K))
    (δ₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ₀ : ¬ AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δ₀)),
    ∃ U ∈ nhds δ₀, ∀ φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ,
      AutomorphicForm.IsSemiLocalTestFn K L v φv → tsupport φv ⊆ U →
        ∃ fv : GL (Fin 2) (v.adicCompletion K) → ℂ,
          AutomorphicForm.IsLocalTestFn K v fv ∧ AutomorphicForm.AreMatchingLocal K L v σ φv fv)
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : Module.finrank K L = 2 ∨ Module.finrank K L = 3) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) (hι : IsEmpty (L →ₐ[K] v.adicCompletion K))
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : IsSemiLocalTestFn K L v φv) :
    ∃ fv : GL (Fin 2) (v.adicCompletion K) → ℂ, IsLocalTestFn K v fv ∧ AreMatchingLocal K L v σ φv fv := by
  refine LocalTransferCore.pre_solution K L v σ ?_ φv hφv
  intro δ₀
  by_cases h : IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ₀)
  · exact hreg K L hdeg σ hσ v hι δ₀ h
  · exact hsing K L hdeg σ hσ v hι δ₀ h

end

open AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : Module.finrank K L = 2 ∨ Module.finrank K L = 3) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) (hι : IsEmpty (L →ₐ[K] v.adicCompletion K))
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : IsSemiLocalTestFn K L v φv) :
    ∃ fv : GL (Fin 2) (v.adicCompletion K) → ℂ, IsLocalTestFn K v fv ∧ AreMatchingLocal K L v σ φv fv :=
  solution_of_children
    AutomorphicForm.exists_nhds_forall_exists_isLocalTestFn_areMatchingLocal_of_isRegularSemisimple_normString
    AutomorphicForm.exists_nhds_forall_exists_isLocalTestFn_areMatchingLocal_of_not_isRegularSemisimple_normString
    K L hdeg σ hσ v hι φv hφv

#print axioms solution

end S_AutomorphicForm_exists_isLocalTestFn_areMatchingLocal_of_isEmpty_algHom
end P2MW
export P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatchingLocal_of_isEmpty_algHom (solution)
