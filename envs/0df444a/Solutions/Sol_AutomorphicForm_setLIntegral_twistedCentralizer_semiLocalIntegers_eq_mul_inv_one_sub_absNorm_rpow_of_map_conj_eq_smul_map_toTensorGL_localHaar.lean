-- Prove2me | solution 1 for AutomorphicForm.setLIntegral_twistedCentralizer_semiLocalIntegers_eq_mul_inv_one_sub_absNorm_rpow_of_map_conj_eq_smul_map_toTensorGL_localHaar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/9a2cc95d-49f3-5f9c-a411-46e2ae1ed8fd

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LatticeTreeOrbital
import Theorems.Thm_AutomorphicForm_setLIntegral_nnnorm_det_rpow_setOf_integral_eq_measure_localIntegralSet_mul
import Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setLIntegral_twistedCentralizer_semiLocalIntegers_eq_mul_inv_one_sub_absNorm_rpow_of_map_conj_eq_smul_map_toTensorGL_localHaar

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory NumberField IsDedekindDomain TopologicalSpace Topology
open scoped TensorProduct TensorProduct.RightActions ENNReal NNReal Matrix

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL glBorelOf borelSpace_glBorelOf toTensorGL semiLocalIntegers isCompact_semiLocalIntegers semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet isOpen_semiLocalIntegralSet sigmaTensor sigmaGL twistedCentralizer twistedCentralizerBorel IsTwistedOrbitalIntegralOn integralMatrixSet isCompact_integralMatrixSet integralUnitsSet mem_integralUnitsSet localIntegralSet mem_localIntegralSet one_mem_localIntegralSet isOpen_localIntegralSet localGLBorel borelSpace_localGLBorel locallyCompactSpace_localGL localHaar isHaarMeasure_localHaar localHaar_localIntegralSet mem_sigmaCentralizer_iff setLIntegral_nnnorm_det_rpow_setOf_integral_eq_measure_localIntegralSet_mul"
namespace GoodPlaceLocalZeta
p2m_open "AutomorphicForm"

section Lattice

open LT.LatticeTree

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

theorem exists_gl_latticeMap_stdLattice_eq {Λ : Submodule R (Fin 2 → F)} (hΛ : IsFullLattice Λ) :
    ∃ g : GL (Fin 2) F, latticeMap g (stdLattice R F) = Λ := by
  haveI : Submodule.IsLattice F Λ := ⟨hΛ.1, hΛ.2⟩
  have hrank : Module.finrank R Λ = 2 := by
    rw [Submodule.IsLattice.finrank_of_pi F Λ, Fintype.card_fin]
  let b : Module.Basis (Fin 2) R Λ := Module.finBasisOfFinrankEq R Λ hrank
  let bK : Module.Basis (Fin 2) F (Fin 2 → F) := b.extendOfIsLattice F
  let e : Module.Basis (Fin 2) F (Fin 2 → F) := Pi.basisFun F (Fin 2)
  let g : GL (Fin 2) F :=
    ⟨e.toMatrix bK, bK.toMatrix e, e.toMatrix_mul_toMatrix_flip bK, bK.toMatrix_mul_toMatrix_flip e⟩
  refine ⟨g, ?_⟩
  have hcol : ∀ j, mulVecLinR (R := R) g (Pi.single j 1) = ((b j : Λ) : Fin 2 → F) := by
    intro j
    rw [mulVecLinR_apply, mulVec_single_one]
    funext i
    change e.toMatrix bK i j = _
    rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr, Module.Basis.extendOfIsLattice_apply]
  rw [latticeMap, stdLattice_eq_span, Submodule.map_span, ← Set.range_comp]
  have hfun : (mulVecLinR (R := R) g) ∘ (fun j => (Pi.single j 1 : Fin 2 → F)) =
      fun j => ((b j : Λ) : Fin 2 → F) := funext hcol
  rw [hfun]
  have h2 := congrArg (Submodule.map Λ.subtype) b.span_eq
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h2
  exact h2

omit [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R F] in

theorem isInteger_conj_of_mulVec_mem {Λ : Submodule R (Fin 2 → F)} {g : GL (Fin 2) F}
    (hg : latticeMap g (stdLattice R F) = Λ) {m : Matrix (Fin 2) (Fin 2) F}
    (hm : ∀ x ∈ Λ, m *ᵥ x ∈ Λ) (i j : Fin 2) :
    IsLocalization.IsInteger R
      ((((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * m * (g : Matrix (Fin 2) (Fin 2) F)) i j) := by

  have hgej : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ (Pi.single j 1 : Fin 2 → F) ∈ Λ := by
    rw [← hg]
    exact mulVec_mem_latticeMap (single_one_mem_stdLattice R F j)
  have hm' := hm _ hgej
  rw [← hg, mem_latticeMap] at hm'
  obtain ⟨w, hw, hw'⟩ := hm'
  have hcol : (((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * m * (g : Matrix (Fin 2) (Fin 2) F)) *ᵥ
      (Pi.single j 1 : Fin 2 → F) = w := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hw', Matrix.mulVec_mulVec,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have h := congrFun hcol i
  rw [mulVec_single_one] at h
  dsimp only at h
  rw [h]
  exact hw i

end Lattice

section LocalField

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => HeightOneSpectrum.adicCompletion K v
local notation "𝓸" => HeightOneSpectrum.adicCompletionIntegers K v

theorem mem_integers_iff_norm (y : F) : y ∈ 𝓸 ↔ ‖y‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valued.toNormedField.norm_le_one_iff]

theorem isInteger_iff (x : F) : IsLocalization.IsInteger (𝓸) x ↔ x ∈ 𝓸 := by
  constructor
  · rintro ⟨r, rfl⟩
    exact r.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem exists_norm_lt_one : ∃ π : F, π ≠ 0 ∧ ‖π‖ < 1 := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  refine ⟨NumberField.FinitePlace.embedding v (algebraMap _ K x), ?_, ?_⟩
  · rw [map_ne_zero]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).2 hx0
  · exact (NumberField.FinitePlace.norm_lt_one_iff_mem K v x).2 hx

theorem exists_mul_mem_integers (C : ℝ) :
    ∃ d : F, d ≠ 0 ∧ d ∈ 𝓸 ∧ ∀ x : F, ‖x‖ ≤ C → d * x ∈ 𝓸 := by
  obtain ⟨π, hπ0, hπ1⟩ := exists_norm_lt_one K v
  have hπpos : 0 < ‖π‖ := norm_pos_iff.2 hπ0
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (max C 1) by positivity) hπ1
  refine ⟨π ^ (n + 1), pow_ne_zero _ hπ0, ?_, fun x hx => ?_⟩
  · rw [mem_integers_iff_norm, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hπ1.le
  · rw [mem_integers_iff_norm, norm_mul, norm_pow, pow_succ]
    have hC : ‖x‖ ≤ max C 1 := hx.trans (le_max_left _ _)
    have hM : (0 : ℝ) < max C 1 := by positivity
    have h1 : ‖π‖ ^ n * max C 1 ≤ 1 := by
      have := (mul_lt_mul_of_pos_right hn hM)
      rw [one_div, inv_mul_cancel₀ hM.ne'] at this
      exact this.le
    calc ‖π‖ ^ n * ‖π‖ * ‖x‖ ≤ ‖π‖ ^ n * 1 * max C 1 := by gcongr
      _ = ‖π‖ ^ n * max C 1 := by ring
      _ ≤ 1 := h1

end LocalField

section Order

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => HeightOneSpectrum.adicCompletion K v
local notation "𝓸" => HeightOneSpectrum.adicCompletionIntegers K v

attribute [local instance] AutomorphicForm.localGLBorel

scoped instance : BorelSpace (GL (Fin 2) F) := AutomorphicForm.borelSpace_localGLBorel K v

theorem secondCountableTopology_GL (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [SecondCountableTopology A] : SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

scoped instance : SecondCountableTopology (GL (Fin 2) F) := secondCountableTopology_GL _
scoped instance : LocallyCompactSpace (GL (Fin 2) F) := AutomorphicForm.locallyCompactSpace_localGL K v
scoped instance : (AutomorphicForm.localHaar K v).IsHaarMeasure := AutomorphicForm.isHaarMeasure_localHaar K v
scoped instance : (AutomorphicForm.localHaar K v).IsMulRightInvariant :=
  (Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two _).1

def uT : GL (Fin 2) F := ⟨!![1, 1; 0, 1], !![1, -1; 0, 1], by ext i j; fin_cases i <;> fin_cases j <;> simp,
  by ext i j; fin_cases i <;> fin_cases j <;> simp⟩
def uT' : GL (Fin 2) F := ⟨!![1, 0; 1, 1], !![1, 0; -1, 1], by ext i j; fin_cases i <;> fin_cases j <;> simp,
  by ext i j; fin_cases i <;> fin_cases j <;> simp⟩
def uW : GL (Fin 2) F := ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp,
  by ext i j; fin_cases i <;> fin_cases j <;> simp⟩
def uQ : GL (Fin 2) F := ⟨!![0, 1; 1, 1], !![-1, 1; 1, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp,
  by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

@[scoped simp] theorem uT_val : ((uT K v : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] := rfl
@[scoped simp] theorem uT'_val : ((uT' K v : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1] := rfl
@[scoped simp] theorem uW_val : ((uW K v : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := rfl
@[scoped simp] theorem uQ_val : ((uQ K v : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 1] := rfl
@[scoped simp] theorem uT_inv_val : (((uT K v)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, -1; 0, 1] := rfl
@[scoped simp] theorem uT'_inv_val : (((uT' K v)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; -1, 1] := rfl
@[scoped simp] theorem uW_inv_val : (((uW K v)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := rfl
@[scoped simp] theorem uQ_inv_val : (((uQ K v)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![-1, 1; 1, 0] := rfl

theorem mem_localIntegralSet_of_entries {g : GL (Fin 2) F}
    (h1 : ∀ i j, (g : Matrix (Fin 2) (Fin 2) F) i j = 0 ∨ (g : Matrix (Fin 2) (Fin 2) F) i j = 1 ∨
      (g : Matrix (Fin 2) (Fin 2) F) i j = -1)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j = 0 ∨
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j = 1 ∨
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j = -1) :
    g ∈ AutomorphicForm.localIntegralSet K v := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rcases h1 i j with h | h | h <;> rw [h]
    · exact zero_mem _
    · exact one_mem _
    · exact neg_mem (one_mem _)
  · rcases h2 i j with h | h | h <;> rw [h]
    · exact zero_mem _
    · exact one_mem _
    · exact neg_mem (one_mem _)

theorem uT_mem : uT K v ∈ AutomorphicForm.localIntegralSet K v :=
  mem_localIntegralSet_of_entries K v (fun i j => by rw [uT_val]; fin_cases i <;> fin_cases j <;> simp)
    (fun i j => by rw [uT_inv_val]; fin_cases i <;> fin_cases j <;> simp)
theorem uT'_mem : uT' K v ∈ AutomorphicForm.localIntegralSet K v :=
  mem_localIntegralSet_of_entries K v (fun i j => by rw [uT'_val]; fin_cases i <;> fin_cases j <;> simp)
    (fun i j => by rw [uT'_inv_val]; fin_cases i <;> fin_cases j <;> simp)
theorem uW_mem : uW K v ∈ AutomorphicForm.localIntegralSet K v :=
  mem_localIntegralSet_of_entries K v (fun i j => by rw [uW_val]; fin_cases i <;> fin_cases j <;> simp)
    (fun i j => by rw [uW_inv_val]; fin_cases i <;> fin_cases j <;> simp)
theorem uQ_mem : uQ K v ∈ AutomorphicForm.localIntegralSet K v :=
  mem_localIntegralSet_of_entries K v (fun i j => by rw [uQ_val]; fin_cases i <;> fin_cases j <;> simp)
    (fun i j => by rw [uQ_inv_val]; fin_cases i <;> fin_cases j <;> simp)

theorem matrix_eq_combination (a : Matrix (Fin 2) (Fin 2) F) :
    a = a 0 0 • ((1 : Matrix (Fin 2) (Fin 2) F) - (uQ K v : Matrix (Fin 2) (Fin 2) F) + (uW K v : Matrix (Fin 2) (Fin 2) F)) +
        a 0 1 • ((uT K v : Matrix (Fin 2) (Fin 2) F) - 1) +
        a 1 0 • ((uT' K v : Matrix (Fin 2) (Fin 2) F) - 1) +
        a 1 1 • ((uQ K v : Matrix (Fin 2) (Fin 2) F) - (uW K v : Matrix (Fin 2) (Fin 2) F)) := by
  rw [uT_val, uT'_val, uW_val, uQ_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

def sandwich (P Q : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F →ₗ[F] Matrix (Fin 2) (Fin 2) F where
  toFun X := P * X * Q
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

@[scoped simp] theorem sandwich_apply (P Q X : Matrix (Fin 2) (Fin 2) F) : sandwich K v P Q X = P * X * Q := rfl

theorem conj_integral_mem (O : Set (Matrix (Fin 2) (Fin 2) F))
    (hadd : ∀ m ∈ O, ∀ n ∈ O, m + n ∈ O)
    (hneg : ∀ m ∈ O, -m ∈ O)
    (hsmul : ∀ a : F, a ∈ 𝓸 → ∀ m ∈ O, a • m ∈ O)
    (k : GL (Fin 2) F)
    (hk : ∀ u : GL (Fin 2) F, u ∈ AutomorphicForm.localIntegralSet K v →
      ((k : Matrix (Fin 2) (Fin 2) F) * u * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) ∈ O)
    (a : Matrix (Fin 2) (Fin 2) F) (ha : ∀ i j, a i j ∈ 𝓸) :
    (k : Matrix (Fin 2) (Fin 2) F) * a * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ∈ O := by
  have hsub_mem : ∀ x ∈ O, ∀ y ∈ O, x - y ∈ O := fun x hx y hy => by
    rw [sub_eq_add_neg]; exact hadd _ hx _ (hneg _ hy)
  have hkI : (k : Matrix (Fin 2) (Fin 2) F) * 1 * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ∈ O := by
    have := hk 1 (AutomorphicForm.one_mem_localIntegralSet K v)
    rwa [Units.val_one] at this
  have h := congrArg (sandwich K v (k : Matrix (Fin 2) (Fin 2) F) ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
    (matrix_eq_combination K v a)
  simp only [map_add, map_sub, LinearMap.map_smul, sandwich_apply] at h
  rw [h]
  refine hadd _ (hadd _ (hadd _ (hsmul _ (ha 0 0) _ ?_) _ (hsmul _ (ha 0 1) _ ?_)) _
    (hsmul _ (ha 1 0) _ ?_)) _ (hsmul _ (ha 1 1) _ ?_)
  · exact hadd _ (hsub_mem _ hkI _ (hk _ (uQ_mem K v))) _ (hk _ (uW_mem K v))
  · exact hsub_mem _ (hk _ (uT_mem K v)) _ hkI
  · exact hsub_mem _ (hk _ (uT'_mem K v)) _ hkI
  · exact hsub_mem _ (hk _ (uQ_mem K v)) _ (hk _ (uW_mem K v))

theorem eq_of_subset_of_measure_eq_one {U V : Set (GL (Fin 2) F)}
    (hUV : U ⊆ V) (hUmeas : MeasurableSet U)
    (hUmul : ∀ g ∈ U, ∀ h ∈ U, g * h ∈ U) (hUinv : ∀ g ∈ U, g⁻¹ ∈ U)
    (hVmul : ∀ g ∈ V, ∀ h ∈ V, g * h ∈ V)
    (hU : AutomorphicForm.localHaar K v U = 1) (hV : AutomorphicForm.localHaar K v V = 1) : U = V := by
  set μ := AutomorphicForm.localHaar K v with hμ
  refine Set.Subset.antisymm hUV fun g₀ hg₀ => ?_
  by_contra hg₀U
  have hcos_sub : (fun u => g₀ * u) '' U ⊆ V := by
    rintro _ ⟨u, hu, rfl⟩
    exact hVmul _ hg₀ _ (hUV hu)
  have hdisj : Disjoint U ((fun u => g₀ * u) '' U) := by
    rw [Set.disjoint_left]
    rintro g hg ⟨u, hu, rfl⟩
    apply hg₀U
    have : g₀ = g₀ * u * u⁻¹ := by group
    rw [this]
    exact hUmul _ hg _ (hUinv _ hu)
  have hcos_meas : MeasurableSet ((fun u => g₀ * u) '' U) := by
    rw [Set.image_mul_left]
    exact hUmeas.preimage (measurable_const_mul _)
  have hcos_vol : μ ((fun u => g₀ * u) '' U) = 1 := by
    rw [Set.image_mul_left, measure_preimage_mul]
    exact hU
  have hle : μ U + μ ((fun u => g₀ * u) '' U) ≤ μ V := by
    rw [← measure_union hdisj hcos_meas]
    exact measure_mono (Set.union_subset hUV hcos_sub)
  rw [hU, hcos_vol, hV] at hle
  norm_num at hle

theorem map_conj_localHaar (k : GL (Fin 2) F) :
    Measure.map (fun g : GL (Fin 2) F => k⁻¹ * g * k) (AutomorphicForm.localHaar K v) =
      AutomorphicForm.localHaar K v := by
  have h1 : (fun g : GL (Fin 2) F => k⁻¹ * g * k) = (fun g => g * k) ∘ fun g => k⁻¹ * g := rfl
  rw [h1, ← Measure.map_map (measurable_mul_const k) (measurable_const_mul k⁻¹),
    map_mul_left_eq_self, map_mul_right_eq_self]

variable {K v}

theorem exists_conj_eq_integral (O : Set (Matrix (Fin 2) (Fin 2) F))
    (h1 : (1 : Matrix (Fin 2) (Fin 2) F) ∈ O)
    (hmul : ∀ m ∈ O, ∀ n ∈ O, m * n ∈ O)
    (hadd : ∀ m ∈ O, ∀ n ∈ O, m + n ∈ O)
    (hneg : ∀ m ∈ O, -m ∈ O)
    (hsmul : ∀ a : F, a ∈ 𝓸 → ∀ m ∈ O, a • m ∈ O)
    (hbdd : ∃ C : ℝ, ∀ m ∈ O, ∀ i j, ‖m i j‖ ≤ C)
    (hmeas : MeasurableSet {g : GL (Fin 2) F | (g : Matrix (Fin 2) (Fin 2) F) ∈ O ∧
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ∈ O})
    (hvol : AutomorphicForm.localHaar K v {g : GL (Fin 2) F | (g : Matrix (Fin 2) (Fin 2) F) ∈ O ∧
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ∈ O} = 1) :
    ∃ k : GL (Fin 2) F, ∀ m : Matrix (Fin 2) (Fin 2) F,
      m ∈ O ↔ ∀ i j, ((((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * m *
        (k : Matrix (Fin 2) (Fin 2) F)) i j) ∈ 𝓸 := by
  classical

  set gens : Set (Fin 2 → F) := {x | ∃ m ∈ O, ∃ j : Fin 2, x = m *ᵥ Pi.single j 1} with hgens
  set Λ : Submodule (𝓸) (Fin 2 → F) := Submodule.span (𝓸) gens with hΛdef
  have hstd_le : LT.LatticeTree.stdLattice (𝓸) F ≤ Λ := by
    rw [LT.LatticeTree.stdLattice_eq_span, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨1, h1, j, by rw [Matrix.one_mulVec]⟩
  have hstab : ∀ m ∈ O, ∀ x ∈ Λ, m *ᵥ x ∈ Λ := by
    intro m hm x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨n, hn, j, rfl⟩ := hx
        exact Submodule.subset_span ⟨m * n, hmul m hm n hn, j, by rw [Matrix.mulVec_mulVec]⟩
    | zero => rw [Matrix.mulVec_zero]; exact Λ.zero_mem
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Λ.add_mem hx hy
    | smul r x _ hx =>
        rw [Matrix.mulVec_smul]
        exact Λ.smul_mem r hx

  obtain ⟨C, hC⟩ := hbdd
  obtain ⟨d, hd0, hdO, hd⟩ := exists_mul_mem_integers K v C
  set dU : Fˣ := Units.mk0 d hd0 with hdU
  set N : Submodule (𝓸) (Fin 2 → F) :=
    LT.LatticeTree.latticeMap (LT.LatticeTree.scalarGL dU⁻¹) (LT.LatticeTree.stdLattice (𝓸) F) with hN
  have hNfg : N.FG := (LT.LatticeTree.stdLattice_fg (𝓸) F).map _
  have hΛN : Λ ≤ N := by
    rw [hΛdef, Submodule.span_le]
    rintro _ ⟨m, hm, j, rfl⟩
    rw [SetLike.mem_coe, hN, LT.LatticeTree.mem_latticeMap_scalarGL]
    refine ⟨d • (m *ᵥ Pi.single j 1), fun i => ?_, ?_⟩
    · rw [LT.LatticeTree.mulVec_single_one, Pi.smul_apply, smul_eq_mul, isInteger_iff]
      exact hd _ (hC m hm i j)
    · rw [smul_smul, Units.val_inv_eq_inv_val, hdU, Units.val_mk0, inv_mul_cancel₀ hd0, one_smul]
  have hΛfg : Λ.FG := by
    haveI : IsNoetherian (𝓸) N := isNoetherian_of_fg_of_noetherian N hNfg
    exact (isNoetherian_submodule.mp inferInstance) Λ hΛN
  have hΛfull : LT.LatticeTree.IsFullLattice Λ := by
    refine ⟨hΛfg, ?_⟩
    rw [eq_top_iff, ← LT.LatticeTree.stdLattice_span_top (𝓸) F]
    exact Submodule.span_mono hstd_le

  obtain ⟨k, hk⟩ := exists_gl_latticeMap_stdLattice_eq hΛfull
  have hsub : ∀ m ∈ O, ∀ i j, ((((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * m *
      (k : Matrix (Fin 2) (Fin 2) F)) i j) ∈ 𝓸 := fun m hm i j =>
    (isInteger_iff K v _).1 (isInteger_conj_of_mulVec_mem hk (hstab m hm) i j)
  refine ⟨k, fun m => ⟨hsub m, fun hm => ?_⟩⟩

  set U : Set (GL (Fin 2) F) := {g | (g : Matrix (Fin 2) (Fin 2) F) ∈ O ∧
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ∈ O} with hUdef
  set V : Set (GL (Fin 2) F) := (fun g => k⁻¹ * g * k) ⁻¹' AutomorphicForm.localIntegralSet K v with hVdef
  have hconj_val : ∀ g : GL (Fin 2) F, ((k⁻¹ * g * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * g * (k : Matrix (Fin 2) (Fin 2) F) := fun g => by
    simp only [Units.val_mul]
  have hUV : U ⊆ V := by
    intro g hg
    rw [hVdef, Set.mem_preimage, AutomorphicForm.mem_localIntegralSet]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [hconj_val]; exact hsub _ hg.1 i j
    · have : (k⁻¹ * g * k)⁻¹ = k⁻¹ * g⁻¹ * k := by group
      rw [this, hconj_val]; exact hsub _ hg.2 i j
  have hcont_conj : Continuous fun g : GL (Fin 2) F => k⁻¹ * g * k :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hmap_conj := map_conj_localHaar K v k
  have hVvol : AutomorphicForm.localHaar K v V = 1 := by
    rw [hVdef, ← Measure.map_apply hcont_conj.measurable
      (AutomorphicForm.isOpen_localIntegralSet K v).measurableSet, hmap_conj,
      AutomorphicForm.localHaar_localIntegralSet]
  have hUmul : ∀ g ∈ U, ∀ h ∈ U, g * h ∈ U := fun g hg h hh =>
    ⟨by rw [Units.val_mul]; exact hmul _ hg.1 _ hh.1,
     by rw [mul_inv_rev, Units.val_mul]; exact hmul _ hh.2 _ hg.2⟩
  have hUinv : ∀ g ∈ U, g⁻¹ ∈ U := fun g hg => ⟨hg.2, by rw [inv_inv]; exact hg.1⟩
  have hVmul : ∀ g ∈ V, ∀ h ∈ V, g * h ∈ V := by
    intro g hg h hh
    rw [hVdef, Set.mem_preimage] at hg hh ⊢
    have : k⁻¹ * (g * h) * k = (k⁻¹ * g * k) * (k⁻¹ * h * k) := by group
    rw [this]
    obtain ⟨hg1, hg2⟩ := hg
    obtain ⟨hh1, hh2⟩ := hh
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [Units.val_mul, Matrix.mul_apply]
      exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hg1 i l) (hh1 l j)
    · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
      exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hh2 i l) (hg2 l j)
  have hUeqV : U = V := eq_of_subset_of_measure_eq_one K v hUV hmeas hUmul hUinv hVmul hvol hVvol

  have hkuk : ∀ u : GL (Fin 2) F, u ∈ AutomorphicForm.localIntegralSet K v →
      ((k : Matrix (Fin 2) (Fin 2) F) * u * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) ∈ O := by
    intro u hu
    have hmemV : k * u * k⁻¹ ∈ V := by
      rw [hVdef, Set.mem_preimage]
      have : k⁻¹ * (k * u * k⁻¹) * k = u := by group
      rwa [this]
    rw [← hUeqV] at hmemV
    have := hmemV.1
    simpa only [Units.val_mul] using this
  obtain ⟨a, ha⟩ : ∃ a : Matrix (Fin 2) (Fin 2) F,
      ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * m * (k : Matrix (Fin 2) (Fin 2) F) = a := ⟨_, rfl⟩
  have hm' : ∀ i j, a i j ∈ 𝓸 := fun i j => ha ▸ hm i j
  have hma : m = (k : Matrix (Fin 2) (Fin 2) F) * a * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [← ha, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  rw [hma]
  exact conj_integral_mem K v O hadd hneg hsmul k hkuk a hm'

end Order

section Main

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

local notation "F" => HeightOneSpectrum.adicCompletion K v
local notation "𝓸" => HeightOneSpectrum.adicCompletionIntegers K v
local notation "E" => L ⊗[K] HeightOneSpectrum.adicCompletion K v
local notation "G" => GL (Fin 2) (L ⊗[K] HeightOneSpectrum.adicCompletion K v)

attribute [local instance] AutomorphicForm.localGLBorel AutomorphicForm.glBorelOf
  AutomorphicForm.twistedCentralizerBorel

set_option synthInstance.maxHeartbeats 1600000

scoped instance instIsTopologicalRingE : IsTopologicalRing E := isTopologicalRing_tensor K L _
scoped instance instT2E : T2Space E := t2Space_tensor K L _
scoped instance instLocallyCompactE : LocallyCompactSpace E := locallyCompactSpace_tensor K L _
scoped instance instIsTopologicalGroupG : IsTopologicalGroup G := isTopologicalGroup_tensorGL K L _
scoped instance instT2G : T2Space G := t2Space_tensorGL K L _
scoped instance instBorelG : BorelSpace G := borelSpace_glBorelOf _
scoped instance instBorelGF : BorelSpace (GL (Fin 2) F) := AutomorphicForm.borelSpace_localGLBorel K v
scoped instance instHaarF : (AutomorphicForm.localHaar K v).IsHaarMeasure := AutomorphicForm.isHaarMeasure_localHaar K v

abbrev incl : F →ₐ[K] E := Algebra.TensorProduct.includeRight

theorem incl_injective : Function.Injective (incl K L v) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective

theorem continuous_incl : Continuous (incl K L v) := by
  have h : Continuous fun a : F => a • (1 : E) := continuous_id.fun_smul continuous_const
  refine h.congr fun a => ?_
  rw [← Algebra.algebraMap_eq_smul_one]
  rfl

theorem continuous_toTensorGL : Continuous (toTensorGL K L F) := by
  refine Continuous.units_map _ ?_
  change Continuous fun M : Matrix (Fin 2) (Fin 2) F => M.map ((incl K L v).toRingHom)
  exact continuous_id.matrix_map (continuous_incl K L v)

theorem exists_retraction : ∃ r : E →ₗ[F] F, ∀ a : F, r ((1 : L) ⊗ₜ[K] a) = a := by
  obtain ⟨lam, hlam⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.2 (algebraMap K L).injective)
  have hlam1 : lam 1 = 1 := by
    have := LinearMap.congr_fun hlam 1
    simpa using this
  refine ⟨(TensorProduct.AlgebraTensorModule.rid K F F).toLinearMap ∘ₗ
      (TensorProduct.RightActions.Module.TensorProduct.comm K F K).symm.toLinearMap ∘ₗ
      TensorProduct.RightActions.LinearMap.baseChange K L K F lam, fun a => ?_⟩
  simp [hlam1]

def retr : E →ₗ[F] F := (exists_retraction K L v).choose

theorem retr_incl (a : F) : retr K L v (incl K L v a) = a := (exists_retraction K L v).choose_spec a

theorem continuous_retr : Continuous (retr K L v) := IsModuleTopology.continuous_of_linearMap _

theorem range_incl_eq : Set.range (incl K L v) = {e : E | incl K L v (retr K L v e) = e} := by
  ext e
  constructor
  · rintro ⟨a, rfl⟩
    show incl K L v (retr K L v (incl K L v a)) = incl K L v a
    rw [retr_incl]
  · intro he
    exact ⟨_, he⟩

theorem isClosed_range_incl : IsClosed (Set.range (incl K L v)) := by
  rw [range_incl_eq]
  exact isClosed_eq ((continuous_incl K L v).comp (continuous_retr K L v)) continuous_id

theorem val_toTensorGL (g : GL (Fin 2) F) :
    ((toTensorGL K L F g : G) : Matrix (Fin 2) (Fin 2) E) = (g : Matrix (Fin 2) (Fin 2) F).map (incl K L v) := rfl

theorem mem_range_toTensorGL_iff (x : G) :
    x ∈ Set.range (toTensorGL K L F) ↔
      (∀ i j, (x : Matrix (Fin 2) (Fin 2) E) i j ∈ Set.range (incl K L v)) ∧
      (∀ i j, ((x⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j ∈ Set.range (incl K L v)) := by
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨fun i j => ⟨(g : Matrix (Fin 2) (Fin 2) F) i j, rfl⟩, fun i j => ⟨((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j, ?_⟩⟩
    rw [← map_inv]; rfl
  · rintro ⟨h1, h2⟩
    choose a ha using h1
    choose b hb using h2
    set φ : Matrix (Fin 2) (Fin 2) F →+* Matrix (Fin 2) (Fin 2) E := (incl K L v).toRingHom.mapMatrix with hφ
    have hφinj : Function.Injective φ := fun M N h =>
      Matrix.map_injective (f := fun a : F => incl K L v a) (incl_injective K L v) h
    have hA : φ (Matrix.of a) = (x : Matrix (Fin 2) (Fin 2) E) := by
      ext i j; exact ha i j
    have hB : φ (Matrix.of b) = ((x⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) := by
      ext i j; exact hb i j
    have e1 : Matrix.of a * Matrix.of b = 1 := hφinj (by
      rw [map_mul, map_one, hA, hB, ← Units.val_mul, mul_inv_cancel, Units.val_one])
    have e2 : Matrix.of b * Matrix.of a = 1 := hφinj (by
      rw [map_mul, map_one, hA, hB, ← Units.val_mul, inv_mul_cancel, Units.val_one])
    exact ⟨⟨Matrix.of a, Matrix.of b, e1, e2⟩, Units.ext hA⟩

theorem isClosed_range_toTensorGL : IsClosed (Set.range (toTensorGL K L F)) := by
  have hcont : ∀ i j, Continuous fun x : G => (x : Matrix (Fin 2) (Fin 2) E) i j := fun i j =>
    Units.continuous_val.matrix_elem i j
  have hcont' : ∀ i j, Continuous fun x : G => ((x⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j := fun i j =>
    Units.continuous_coe_inv.matrix_elem i j
  have hset : Set.range (toTensorGL K L F) =
      (⋂ i, ⋂ j, (fun x : G => (x : Matrix (Fin 2) (Fin 2) E) i j) ⁻¹' Set.range (incl K L v)) ∩
      (⋂ i, ⋂ j, (fun x : G => ((x⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j) ⁻¹' Set.range (incl K L v)) := by
    ext x
    rw [mem_range_toTensorGL_iff]
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
  rw [hset]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => (isClosed_range_incl K L v).preimage (hcont i j)).inter
    (isClosed_iInter fun i => isClosed_iInter fun j => (isClosed_range_incl K L v).preimage (hcont' i j))

theorem det_toTensorGL_val (g : GL (Fin 2) F) :
    ((Matrix.GeneralLinearGroup.det (toTensorGL K L F g) : Eˣ) : E) =
      incl K L v ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, val_toTensorGL]
  exact (AlgHom.map_det (incl K L v) _).symm

def SLI : Subring E := (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).toRingHom.range

theorem mem_SLI {e : E} : e ∈ SLI K L v ↔ e ∈ semiLocalIntegers K L v := by
  simp only [SLI, RingHom.mem_range, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, semiLocalIntegers, Set.mem_range]

theorem incl_mem_semiLocalIntegers {a : F} (ha : a ∈ 𝓸) : incl K L v a ∈ semiLocalIntegers K L v := by
  refine ⟨(1 : 𝓞 L) ⊗ₜ ⟨a, ha⟩, ?_⟩
  rw [HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul, map_one]
  rfl

theorem conj_smul_apply {R : Type*} [CommRing R] (P X Q : Matrix (Fin 2) (Fin 2) R) (e : R) (i j : Fin 2) :
    (P * (e • X) * Q) i j = e * (P * X * Q) i j := by
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two]
  ring

variable (σ : L ≃ₐ[K] L)

theorem continuous_sigmaGL : Continuous (sigmaGL K L F σ) := by
  refine Continuous.units_map _ ?_
  have h : Continuous (sigmaTensor K L F σ) := IsModuleTopology.continuous_of_linearMap
    (TensorProduct.RightActions.AlgebraMap.baseChange K L L F σ.toAlgHom).toLinearMap
  exact continuous_id.matrix_map h

theorem isClosed_twistedCentralizer (δ : G) :
    IsClosed ((twistedCentralizer K L F σ δ : Subgroup G) : Set G) := by
  have hc : Continuous fun t : G => t * δ * (sigmaGL K L F σ t)⁻¹ :=
    (continuous_id.mul continuous_const).mul (continuous_sigmaGL K L v σ).inv
  have : ((twistedCentralizer K L F σ δ : Subgroup G) : Set G) =
      (fun t : G => t * δ * (sigmaGL K L F σ t)⁻¹) ⁻¹' {δ} := by
    ext t
    exact mem_sigmaCentralizer_iff
  rw [this]
  exact isClosed_singleton.preimage hc

set_option maxHeartbeats 12000000 in

theorem main (δ : G)
    (τ : Measure (twistedCentralizer K L F σ δ)) (hτ : τ.IsHaarMeasure)
    (y : G) (c : ℝ≥0∞)
    (hy : Measure.map (fun t : ↥(twistedCentralizer K L F σ δ) => y⁻¹ * (t : G) * y) τ =
      c • Measure.map (toTensorGL K L F) (localHaar K v))
    (hU : τ (Subtype.val ⁻¹' semiLocalIntegralSet K L v) = c)
    (a : ℝ) (N : ↥(twistedCentralizer K L F σ δ) → ℝ≥0∞)
    (hN : ∀ (t : ↥(twistedCentralizer K L F σ δ)) (s : Fˣ),
      Matrix.GeneralLinearGroup.det (t : G) = Units.map (incl K L v).toRingHom.toMonoidHom s →
        N t = ((‖(s : F)‖₊ : ℝ≥0∞) ^ a)) :
    ∫⁻ t in {t : ↥(twistedCentralizer K L F σ δ) | ∀ i j, ((t : G) : Matrix (Fin 2) (Fin 2) E) i j ∈ semiLocalIntegers K L v},
        N t ∂τ =
      c * ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-a))⁻¹ *
        (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - a))⁻¹) := by
  haveI := hτ
  haveI : IsTopologicalRing E := instIsTopologicalRingE K L v
  haveI : T2Space E := instT2E K L v
  haveI : IsTopologicalGroup G := instIsTopologicalGroupG K L v
  haveI : T2Space G := instT2G K L v
  haveI : T1Space G := T2Space.t1Space
  haveI : BorelSpace G := instBorelG K L v
  haveI : BorelSpace ↥(twistedCentralizer K L F σ δ) := ⟨rfl⟩

  obtain ⟨φ, hφ⟩ : ∃ φ : ↥(twistedCentralizer K L F σ δ) → G, ∀ t, φ t = y⁻¹ * (t : G) * y := ⟨_, fun _ => rfl⟩
  have hφfun : (fun t : ↥(twistedCentralizer K L F σ δ) => y⁻¹ * (t : G) * y) = φ := funext fun t => (hφ t).symm
  rw [hφfun] at hy
  have hφc : Continuous φ := by
    rw [← hφfun]; exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  have hφm : Measurable φ := hφc.measurable
  have hιc : Continuous (toTensorGL K L F) := continuous_toTensorGL K L v
  have hιm : Measurable (toTensorGL K L F) := hιc.measurable
  have hTclosed : IsClosed ((twistedCentralizer K L F σ δ : Subgroup G) : Set G) := isClosed_twistedCentralizer K L v σ δ

  have hUopen : IsOpen (Subtype.val ⁻¹' semiLocalIntegralSet K L v : Set ↥(twistedCentralizer K L F σ δ)) :=
    (isOpen_semiLocalIntegralSet K L v).preimage continuous_subtype_val
  have hUcpt : IsCompact (Subtype.val ⁻¹' semiLocalIntegralSet K L v : Set ↥(twistedCentralizer K L F σ δ)) :=
    hTclosed.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_semiLocalIntegralSet K L v)
  have hc0 : c ≠ 0 := by
    rw [← hU]
    exact hUopen.measure_ne_zero τ ⟨1, by
      show ((1 : ↥(twistedCentralizer K L F σ δ)) : G) ∈ semiLocalIntegralSet K L v
      exact one_mem_semiLocalIntegralSet K L v⟩
  have hctop : c ≠ ⊤ := by
    rw [← hU]
    exact hUcpt.measure_lt_top.ne

  have htrans : ∀ A : Set G, MeasurableSet A → τ (φ ⁻¹' A) = c * localHaar K v (toTensorGL K L F ⁻¹' A) := by
    intro A hA
    rw [← Measure.map_apply hφm hA, hy, Measure.smul_apply, Measure.map_apply hιm hA, smul_eq_mul]
  have hconjc : Continuous fun x : G => y * x * y⁻¹ := (continuous_const.mul continuous_id).mul continuous_const

  have hAmeas : MeasurableSet ((fun x : G => y * x * y⁻¹) ⁻¹' semiLocalIntegralSet K L v) :=
    ((isOpen_semiLocalIntegralSet K L v).preimage hconjc).measurableSet
  have hU''vol : localHaar K v ((fun g : GL (Fin 2) F => y * toTensorGL K L F g * y⁻¹) ⁻¹' semiLocalIntegralSet K L v) = 1 := by
    have h := htrans _ hAmeas
    have h1 : φ ⁻¹' ((fun x : G => y * x * y⁻¹) ⁻¹' semiLocalIntegralSet K L v) =
        (Subtype.val ⁻¹' semiLocalIntegralSet K L v : Set ↥(twistedCentralizer K L F σ δ)) := by
      ext t
      simp only [Set.mem_preimage, hφ t]
      have : y * (y⁻¹ * (t : G) * y) * y⁻¹ = t := by group
      rw [this]
    rw [h1, hU] at h
    exact ((ENNReal.mul_eq_left hc0 hctop).1 h.symm)

  have hrange : ∀ t : ↥(twistedCentralizer K L F σ δ), φ t ∈ Set.range (toTensorGL K L F) := by
    have hS : τ (φ ⁻¹' (Set.range (toTensorGL K L F))ᶜ) = 0 := by
      rw [htrans _ (isClosed_range_toTensorGL K L v).measurableSet.compl]
      have : toTensorGL K L F ⁻¹' (Set.range (toTensorGL K L F))ᶜ = ∅ := by
        ext g; simp
      rw [this, measure_empty, mul_zero]
    have hopen : IsOpen (φ ⁻¹' (Set.range (toTensorGL K L F))ᶜ) :=
      (isClosed_range_toTensorGL K L v).isOpen_compl.preimage hφc
    have hempty := (hopen.measure_eq_zero_iff τ).1 hS
    intro t
    by_contra ht
    have : t ∈ φ ⁻¹' (Set.range (toTensorGL K L F))ᶜ := ht
    rw [hempty] at this
    exact this
  choose gT hgT using hrange

  have hdet : ∀ t : ↥(twistedCentralizer K L F σ δ), Matrix.GeneralLinearGroup.det (t : G) =
      Units.map (incl K L v).toRingHom.toMonoidHom (Matrix.GeneralLinearGroup.det (gT t)) := by
    intro t
    have h1 : Matrix.GeneralLinearGroup.det (φ t) = Matrix.GeneralLinearGroup.det (t : G) := by
      rw [hφ t, map_mul, map_mul, map_inv]
      exact inv_mul_cancel_comm _ _
    rw [← h1, ← hgT t]
    apply Units.ext
    rw [det_toTensorGL_val, Units.coe_map]
    rfl
  have hNt : ∀ t : ↥(twistedCentralizer K L F σ δ), N t = ((‖((Matrix.GeneralLinearGroup.det (gT t) : Fˣ) : F)‖₊ : ℝ≥0∞) ^ a) :=
    fun t => hN t _ (hdet t)
  have hdet_val : ∀ t : ↥(twistedCentralizer K L F σ δ), retr K L v ((φ t : G) : Matrix (Fin 2) (Fin 2) E).det =
      ((Matrix.GeneralLinearGroup.det (gT t) : Fˣ) : F) := by
    intro t
    rw [← hgT t, ← Matrix.GeneralLinearGroup.val_det_apply, det_toTensorGL_val, retr_incl]

  obtain ⟨Iy, hIydef⟩ : ∃ S : Set G,
      S = {x | ∀ i j, ((y * x * y⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j ∈ semiLocalIntegers K L v} := ⟨_, rfl⟩
  have hIymem : ∀ x : G, x ∈ Iy ↔ ∀ i j, ((y * x * y⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j ∈ semiLocalIntegers K L v :=
    fun x => by rw [hIydef]; exact Iff.rfl
  obtain ⟨fG, hfG⟩ : ∃ f : G → ℝ≥0∞, ∀ x, f x = ((‖retr K L v ((x : Matrix (Fin 2) (Fin 2) E).det)‖₊ : ℝ≥0∞) ^ a) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Fn, hFn⟩ : ∃ f : G → ℝ≥0∞, ∀ x, f x = Iy.indicator fG x := ⟨_, fun _ => rfl⟩
  have hentry : ∀ i j, Continuous fun x : G => ((y * x * y⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j := fun i j =>
    (Units.continuous_val.comp hconjc).matrix_elem i j
  have hIyclosed : IsClosed Iy := by
    have : Iy = ⋂ i, ⋂ j, (fun x : G => ((y * x * y⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j) ⁻¹' semiLocalIntegers K L v := by
      ext x; simp [hIymem]
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      (isCompact_semiLocalIntegers K L v).isClosed.preimage (hentry i j)
  have hfGm : Measurable fG := by
    have hc : Continuous fun x : G => retr K L v ((x : Matrix (Fin 2) (Fin 2) E).det) :=
      (continuous_retr K L v).comp ((continuous_id.matrix_det).comp Units.continuous_val)
    have : fG = fun x : G => ((‖retr K L v ((x : Matrix (Fin 2) (Fin 2) E).det)‖₊ : ℝ≥0∞) ^ a) := funext hfG
    rw [this]
    exact (ENNReal.continuous_rpow_const.comp (ENNReal.continuous_coe.comp (continuous_nnnorm.comp hc))).measurable
  have hFnm : Measurable Fn := by
    have : Fn = Iy.indicator fG := funext hFn
    rw [this]
    exact hfGm.indicator hIyclosed.measurableSet

  obtain ⟨I, hIdef⟩ : ∃ S : Set ↥(twistedCentralizer K L F σ δ),
      S = {t : ↥(twistedCentralizer K L F σ δ) | ∀ i j, ((t : G) : Matrix (Fin 2) (Fin 2) E) i j ∈ semiLocalIntegers K L v} :=
    ⟨_, rfl⟩
  rw [← hIdef]
  have hImem : ∀ t : ↥(twistedCentralizer K L F σ δ), t ∈ I ↔ ∀ i j, ((t : G) : Matrix (Fin 2) (Fin 2) E) i j ∈ semiLocalIntegers K L v :=
    fun t => by rw [hIdef]; exact Iff.rfl
  have hIclosed : IsClosed I := by
    have : I = ⋂ i, ⋂ j, (fun t : ↥(twistedCentralizer K L F σ δ) => ((t : G) : Matrix (Fin 2) (Fin 2) E) i j) ⁻¹' semiLocalIntegers K L v := by
      ext t; simp [hImem]
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      (isCompact_semiLocalIntegers K L v).isClosed.preimage
        ((Units.continuous_val.comp continuous_subtype_val).matrix_elem i j)
  have hpoint : ∀ t : ↥(twistedCentralizer K L F σ δ), I.indicator N t = Fn (φ t) := by
    intro t
    have hconj : y * φ t * y⁻¹ = (t : G) := by rw [hφ t]; group
    rw [hFn]
    by_cases ht : t ∈ I
    · have ht' : φ t ∈ Iy := by
        rw [hIymem, hconj]; exact (hImem t).1 ht
      rw [Set.indicator_of_mem ht, hNt t, Set.indicator_of_mem ht', hfG, hdet_val t]
    · have ht' : φ t ∉ Iy := by
        rw [hIymem, hconj]; exact fun h => ht ((hImem t).2 h)
      rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht']

  obtain ⟨O'', hO''def⟩ : ∃ S : Set (GL (Fin 2) F),
      S = {g | ∀ i j, ((y * toTensorGL K L F g * y⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j ∈ semiLocalIntegers K L v} :=
    ⟨_, rfl⟩
  have hO''mem : ∀ g : GL (Fin 2) F, g ∈ O'' ↔
      ∀ i j, ((y * toTensorGL K L F g * y⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j ∈ semiLocalIntegers K L v :=
    fun g => by rw [hO''def]; exact Iff.rfl
  have hO''closed : IsClosed O'' := by
    have : O'' = toTensorGL K L F ⁻¹' Iy := by
      ext g; rw [hO''mem, Set.mem_preimage, hIymem]
    rw [this]
    exact hIyclosed.preimage hιc
  have hpoint' : ∀ g : GL (Fin 2) F, Fn (toTensorGL K L F g) =
      O''.indicator (fun g => ((‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖₊ : ℝ≥0∞) ^ a)) g := by
    intro g
    rw [hFn]
    by_cases hg : g ∈ O''
    · have hg' : toTensorGL K L F g ∈ Iy := by rw [hIymem]; exact (hO''mem g).1 hg
      rw [Set.indicator_of_mem hg', Set.indicator_of_mem hg, hfG, ← Matrix.GeneralLinearGroup.val_det_apply,
        det_toTensorGL_val, retr_incl]
    · have hg' : toTensorGL K L F g ∉ Iy := by rw [hIymem]; exact fun h => hg ((hO''mem g).2 h)
      rw [Set.indicator_of_notMem hg', Set.indicator_of_notMem hg]

  have hstep : ∫⁻ t in I, N t ∂τ =
      c * ∫⁻ g in O'', ((‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖₊ : ℝ≥0∞) ^ a) ∂(localHaar K v) := by
    rw [← lintegral_indicator hIclosed.measurableSet]
    rw [lintegral_congr hpoint, ← lintegral_map hFnm hφm, hy, lintegral_smul_measure,
      lintegral_map hFnm hιm, lintegral_congr hpoint', lintegral_indicator hO''closed.measurableSet, smul_eq_mul]
  rw [hstep]
  congr 1

  obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin 2) (Fin 2) E, Y = (y : Matrix (Fin 2) (Fin 2) E) := ⟨_, rfl⟩
  obtain ⟨Y', hY'⟩ : ∃ Y' : Matrix (Fin 2) (Fin 2) E, Y' = ((y⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) := ⟨_, rfl⟩
  have hYY' : Y * Y' = 1 := by rw [hY, hY', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hY'Y : Y' * Y = 1 := by rw [hY, hY', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hval_conj : ∀ g : GL (Fin 2) F, ((y * toTensorGL K L F g * y⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) =
      Y * (g : Matrix (Fin 2) (Fin 2) F).map (incl K L v) * Y' := by
    intro g
    rw [Units.val_mul, Units.val_mul, val_toTensorGL, hY, hY']
  obtain ⟨Omat, hOmatdef⟩ : ∃ S : Set (Matrix (Fin 2) (Fin 2) F),
      S = {m | ∀ i j, (Y * m.map (incl K L v) * Y') i j ∈ semiLocalIntegers K L v} := ⟨_, rfl⟩
  have hOmat0 : ∀ m : Matrix (Fin 2) (Fin 2) F, m ∈ Omat ↔ ∀ i j, (Y * m.map (incl K L v) * Y') i j ∈ semiLocalIntegers K L v :=
    fun m => by rw [hOmatdef]; exact Iff.rfl
  have hOmat : ∀ m : Matrix (Fin 2) (Fin 2) F, m ∈ Omat ↔ ∀ i j, (Y * m.map (incl K L v) * Y') i j ∈ SLI K L v := by
    intro m
    simp only [mem_SLI]
    exact hOmat0 m
  have hmapmul : ∀ m n : Matrix (Fin 2) (Fin 2) F, (m * n).map (incl K L v) = m.map (incl K L v) * n.map (incl K L v) :=
    fun m n => Matrix.map_mul
  have hconj_mul : ∀ m n : Matrix (Fin 2) (Fin 2) F,
      Y * (m * n).map (incl K L v) * Y' = (Y * m.map (incl K L v) * Y') * (Y * n.map (incl K L v) * Y') := by
    intro m n
    rw [hmapmul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Y' Y, hY'Y, Matrix.one_mul]

  have h1 : (1 : Matrix (Fin 2) (Fin 2) F) ∈ Omat := by
    rw [hOmat, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, hYY']
    intro i j
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq]; exact Subring.one_mem _
    · rw [Matrix.one_apply_ne hij]; exact Subring.zero_mem _
  have hmul : ∀ m ∈ Omat, ∀ n ∈ Omat, m * n ∈ Omat := by
    intro m hm n hn
    rw [hOmat] at hm hn ⊢
    rw [hconj_mul]
    intro i j
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hm i l) (hn l j)
  have hadd : ∀ m ∈ Omat, ∀ n ∈ Omat, m + n ∈ Omat := by
    intro m hm n hn
    rw [hOmat] at hm hn ⊢
    rw [Matrix.map_add _ (map_add (incl K L v)), Matrix.mul_add, Matrix.add_mul]
    intro i j
    rw [Matrix.add_apply]
    exact Subring.add_mem _ (hm i j) (hn i j)
  have hneg : ∀ m ∈ Omat, -m ∈ Omat := by
    intro m hm
    rw [hOmat] at hm ⊢
    rw [Matrix.map_neg _ (map_neg _), Matrix.mul_neg, Matrix.neg_mul]
    intro i j
    rw [Matrix.neg_apply]
    exact Subring.neg_mem _ (hm i j)
  have hsmul : ∀ b : F, b ∈ 𝓸 → ∀ m ∈ Omat, b • m ∈ Omat := by
    intro b hb m hm
    rw [hOmat] at hm ⊢
    have hsm : (b • m).map (incl K L v) = incl K L v b • m.map (incl K L v) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    rw [hsm]
    intro i j
    rw [conj_smul_apply]
    exact Subring.mul_mem _ ((mem_SLI K L v).2 (incl_mem_semiLocalIntegers K L v hb)) (hm i j)
  have hbdd : ∃ C : ℝ, ∀ m ∈ Omat, ∀ i j, ‖m i j‖ ≤ C := by
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Matrix (Fin 2) (Fin 2) E → (Fin 2 → Fin 2 → F),
        ∀ X i j, ψ X i j = retr K L v ((Y' * X * Y) i j) := ⟨fun X i j => retr K L v ((Y' * X * Y) i j), fun _ _ _ => rfl⟩
    have hψc : Continuous ψ := by
      have : ψ = fun X i j => retr K L v ((Y' * X * Y) i j) := by
        funext X i j; exact hψ X i j
      rw [this]
      refine continuous_pi fun i => continuous_pi fun j => (continuous_retr K L v).comp ?_
      exact ((continuous_const.mul continuous_id).mul continuous_const).matrix_elem i j
    have hcpt : IsCompact (ψ '' integralMatrixSet (semiLocalIntegers K L v)) :=
      (isCompact_integralMatrixSet (isCompact_semiLocalIntegers K L v)).image hψc
    obtain ⟨C, hC⟩ := hcpt.isBounded.exists_norm_le
    refine ⟨C, fun m hm i j => ?_⟩
    have hX : Y * m.map (incl K L v) * Y' ∈ integralMatrixSet (semiLocalIntegers K L v) := (hOmat0 m).1 hm
    have hψX : ψ (Y * m.map (incl K L v) * Y') = fun i j => m i j := by
      funext i j
      rw [hψ]
      have : Y' * (Y * m.map (incl K L v) * Y') * Y = m.map (incl K L v) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hY'Y, Matrix.one_mul, Matrix.mul_assoc, hY'Y, Matrix.mul_one]
      rw [this, Matrix.map_apply, retr_incl]
    have h := hC _ ⟨_, hX, hψX⟩
    exact le_trans (le_trans (norm_le_pi_norm (fun j => m i j) j) (norm_le_pi_norm (fun i j => m i j) i)) h
  have hUset_eq : {g : GL (Fin 2) F | (g : Matrix (Fin 2) (Fin 2) F) ∈ Omat ∧
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ∈ Omat} =
      (fun g : GL (Fin 2) F => y * toTensorGL K L F g * y⁻¹) ⁻¹' semiLocalIntegralSet K L v := by
    ext g
    have e2 : (((y * toTensorGL K L F g * y⁻¹)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) =
        Y * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).map (incl K L v) * Y' := by
      have : (y * toTensorGL K L F g * y⁻¹)⁻¹ = y * toTensorGL K L F g⁻¹ * y⁻¹ := by rw [map_inv]; group
      rw [this, hval_conj]
    rw [Set.mem_preimage, show semiLocalIntegralSet K L v = integralUnitsSet (semiLocalIntegers K L v) from rfl,
      mem_integralUnitsSet, hval_conj, e2, Set.mem_setOf_eq, hOmat0, hOmat0]
  have hmeasU : MeasurableSet {g : GL (Fin 2) F | (g : Matrix (Fin 2) (Fin 2) F) ∈ Omat ∧
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ∈ Omat} := by
    rw [hUset_eq]
    exact ((isOpen_semiLocalIntegralSet K L v).preimage
      ((continuous_const.mul hιc).mul continuous_const)).measurableSet
  have hvolU : localHaar K v {g : GL (Fin 2) F | (g : Matrix (Fin 2) (Fin 2) F) ∈ Omat ∧
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ∈ Omat} = 1 := by
    rw [hUset_eq]; exact hU''vol
  obtain ⟨k, hk⟩ := exists_conj_eq_integral Omat h1 hmul hadd hneg hsmul hbdd hmeasU hvolU

  have hckc : Continuous fun g : GL (Fin 2) F => k⁻¹ * g * k := (continuous_const.mul continuous_id).mul continuous_const
  have hO''eq : O'' = (fun g : GL (Fin 2) F => k⁻¹ * g * k) ⁻¹'
      {g : GL (Fin 2) F | ∀ i j, (g : Matrix (Fin 2) (Fin 2) F) i j ∈ v.adicCompletionIntegers K} := by
    ext g
    have hg : g ∈ O'' ↔ (g : Matrix (Fin 2) (Fin 2) F) ∈ Omat := by
      rw [hO''mem, hval_conj, hOmat0]
    rw [hg, hk, Set.mem_preimage, Set.mem_setOf_eq, Units.val_mul, Units.val_mul]
  have hintclosed : IsClosed {g : GL (Fin 2) F | ∀ i j, (g : Matrix (Fin 2) (Fin 2) F) i j ∈ v.adicCompletionIntegers K} := by
    have hO : IsClosed ((v.adicCompletionIntegers K : ValuationSubring F) : Set F) :=
      (isCompact_iff_compactSpace.2 (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v)).isClosed
    have : {g : GL (Fin 2) F | ∀ i j, (g : Matrix (Fin 2) (Fin 2) F) i j ∈ v.adicCompletionIntegers K} =
        ⋂ i, ⋂ j, (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) i j) ⁻¹'
          ((v.adicCompletionIntegers K : ValuationSubring F) : Set F) := by
      ext g; simp
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      hO.preimage (Units.continuous_val.matrix_elem i j)
  have hdetm : Measurable fun g : GL (Fin 2) F => ((‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖₊ : ℝ≥0∞) ^ a) := by
    have hc : Continuous fun g : GL (Fin 2) F => ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) := by
      simp_rw [Matrix.GeneralLinearGroup.val_det_apply]
      exact Units.continuous_val.matrix_det
    exact (ENNReal.continuous_rpow_const.comp (ENNReal.continuous_coe.comp (continuous_nnnorm.comp hc))).measurable
  have hdet_ck : ∀ g : GL (Fin 2) F, Matrix.GeneralLinearGroup.det (k⁻¹ * g * k) = Matrix.GeneralLinearGroup.det g := by
    intro g
    rw [map_mul, map_mul, map_inv]
    exact inv_mul_cancel_comm _ _
  rw [hO''eq]
  rw [setLIntegral_congr_fun (hintclosed.measurableSet.preimage hckc.measurable)
    (fun g _ => show _ = ((‖((Matrix.GeneralLinearGroup.det (k⁻¹ * g * k) : Fˣ) : F)‖₊ : ℝ≥0∞) ^ a) by
      rw [hdet_ck])]
  rw [← setLIntegral_map hintclosed.measurableSet hdetm hckc.measurable, map_conj_localHaar K v k]
  have hT := AutomorphicForm.setLIntegral_nnnorm_det_rpow_setOf_integral_eq_measure_localIntegralSet_mul K v
    (localHaar K v) inferInstance a
  rw [hT, localHaar_localIntegralSet, one_mul]

end Main

end AutomorphicForm.GoodPlaceLocalZeta
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_twistedCentralizer_semiLocalIntegers_eq_mul_inv_one_sub_absNorm_rpow_of_map_conj_eq_smul_map_toTensorGL_localHaar.AutomorphicForm P2MW.S_AutomorphicForm_setLIntegral_twistedCentralizer_semiLocalIntegers_eq_mul_inv_one_sub_absNorm_rpow_of_map_conj_eq_smul_map_toTensorGL_localHaar.AutomorphicForm.GoodPlaceLocalZeta"
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_twistedCentralizer_semiLocalIntegers_eq_mul_inv_one_sub_absNorm_rpow_of_map_conj_eq_smul_map_toTensorGL_localHaar.AutomorphicForm"

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open AutomorphicForm.GoodPlaceLocalZeta in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ : Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ))
    (hτ : τ.IsHaarMeasure)
    (y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (c : ℝ≥0∞)
    (hy : letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
      letI := AutomorphicForm.localGLBorel K v
      Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) =>
          y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) τ =
        c • Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v))
    (hU : τ (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = c)
    (a : ℝ) (N : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) → ℝ≥0∞)
    (hN : ∀ (t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)) (s : (v.adicCompletion K)ˣ),
      Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
        Units.map (Algebra.TensorProduct.includeRight :
          v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s →
      N t = ((‖(s : v.adicCompletion K)‖₊ : ℝ≥0∞) ^ a)) :
    ∫⁻ t in {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) |
        ∀ i j, ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j ∈ AutomorphicForm.semiLocalIntegers K L v},
        N t ∂τ =
      c * ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-a))⁻¹ *
        (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - a))⁻¹) :=
  main K L v σ δ τ hτ y c hy hU a N hN

end
end S_AutomorphicForm_setLIntegral_twistedCentralizer_semiLocalIntegers_eq_mul_inv_one_sub_absNorm_rpow_of_map_conj_eq_smul_map_toTensorGL_localHaar
end P2MW
export P2MW.S_AutomorphicForm_setLIntegral_twistedCentralizer_semiLocalIntegers_eq_mul_inv_one_sub_absNorm_rpow_of_map_conj_eq_smul_map_toTensorGL_localHaar (solution)
