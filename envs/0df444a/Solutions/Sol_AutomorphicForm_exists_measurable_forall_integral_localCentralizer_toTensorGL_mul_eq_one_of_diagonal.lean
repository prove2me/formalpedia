-- Prove2me | solution 1 for AutomorphicForm.exists_measurable_forall_integral_localCentralizer_toTensorGL_mul_eq_one_of_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ce2ceae6-95c9-5198-b53a-f4955b7ea740

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_measurable_forall_integral_localCentralizer_toTensorGL_mul_eq_one_of_diagonal

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain MeasureTheory Set Function
open scoped ENNReal NNReal TensorProduct TensorProduct.RightActions

noncomputable section

namespace KcTorusSectionFn

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => v.adicCompletion K
local notation "E" => L ⊗[K] v.adicCompletion K
local notation "G" => GL (Fin 2) (L ⊗[K] v.adicCompletion K)
local notation "GF" => GL (Fin 2) (v.adicCompletion K)

attribute [local instance 9999] Algebra.toModule

theorem isTopologicalRing_E : IsTopologicalRing E := AutomorphicForm.isTopologicalRing_tensor K L F
theorem t2Space_E : T2Space E := AutomorphicForm.t2Space_tensor K L F
theorem continuousSMul_E : ContinuousSMul F E := IsModuleTopology.toContinuousSMul F E
theorem isScalarTower_FEE : IsScalarTower F E E :=
  @IsScalarTower.right F E _ _ (TensorProduct.RightActions.instAlgebra_definitions K (v.adicCompletion K) L)
theorem smulCommClass_FEE : SMulCommClass F E E :=
  @Algebra.to_smulCommClass F E _ _ (TensorProduct.RightActions.instAlgebra_definitions K (v.adicCompletion K) L)
theorem finite_KL : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L

attribute [local instance] isTopologicalRing_E t2Space_E continuousSMul_E
  isScalarTower_FEE smulCommClass_FEE finite_KL

local notation "n" => Module.finrank K L

theorem finrank_E : Module.finrank F E = n := TensorProduct.finrank_rightAlgebra L

private theorem _root_.KcTorusSectionFn.finrank_pos : 0 < n := Module.finrank_pos

p2m_export "KcTorusSectionFn" "finrank_pos"

theorem continuous_algebraNorm : Continuous (Algebra.norm F : E → F) := by
  classical
  let b := Module.finBasis F E
  have h1 : Continuous fun x : E => Algebra.leftMulMatrix b x :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have h2 : (Algebra.norm F : E → F) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x; exact Algebra.norm_eq_matrix_det b x
  rw [h2]
  exact h1.matrix_det

theorem norm_ne_zero_of_isUnit {x : E} (hx : IsUnit x) : Algebra.norm F x ≠ 0 := by
  intro h0
  obtain ⟨u, rfl⟩ := hx
  have h1 : Algebra.norm F ((u : E)) * Algebra.norm F ((u⁻¹ : Eˣ) : E) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

theorem norm_algebraMap_mul (c : F) (x : E) :
    Algebra.norm F (algebraMap F E c * x) = c ^ n * Algebra.norm F x := by
  rw [map_mul, Algebra.norm_algebraMap, finrank_E]

def InW (N : ℕ) (z : F) : Prop := ∃ k : ℕ, k < N ∧ Valued.v z = WithZero.exp (k : ℤ)

theorem isOpen_sphere {g : WithZero (Multiplicative ℤ)} (hg : g ≠ 0) :
    IsOpen {z : F | Valued.v z = g} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx' : Valued.v x = g := hx
  have h := Valued.locally_const (R := F) (x := x) (by rw [hx']; exact hg)
  have hset : {y : F | Valued.v y = Valued.v x} = {z : F | Valued.v z = g} := by
    ext y; simp [hx']
  rw [hset] at h
  exact h

theorem isOpen_setOf_inW (N : ℕ) : IsOpen {z : F | InW (K := K) (v := v) N z} := by
  have : {z : F | InW (K := K) (v := v) N z} = ⋃ k ∈ Finset.range N, {z : F | Valued.v z = WithZero.exp (k : ℤ)} := by
    ext z
    simp only [mem_setOf_eq, InW, mem_iUnion, Finset.mem_range, exists_prop]
  rw [this]
  exact isOpen_biUnion fun k _ => isOpen_sphere WithZero.exp_ne_zero

theorem inW_pow_mul_iff {N : ℕ} (hN : 0 < N) {c y : F} {k m : ℤ} (hc : Valued.v c = WithZero.exp k)
    (hy : Valued.v y = WithZero.exp m) :
    InW (K := K) (v := v) N (c ^ N * y) ↔ k = -(m / N) := by
  have hn : (0 : ℤ) < N := by exact_mod_cast hN
  have hv : Valued.v (c ^ N * y) = WithZero.exp ((N : ℤ) * k + m) := by
    rw [map_mul, map_pow, hc, hy, WithZero.exp_add]
    congr 1
  constructor
  · rintro ⟨j, hj, hjv⟩
    rw [hv, WithZero.exp_inj] at hjv
    have h := (Int.ediv_emod_unique hn (a := m) (r := (j : ℤ)) (q := -k)).2
      ⟨by rw [← hjv]; ring, by positivity, by exact_mod_cast hj⟩
    rw [h.1]; ring
  · intro hk
    refine ⟨(m % N).toNat, ?_, ?_⟩
    · have h1 : m % N < N := Int.emod_lt_of_pos m hn
      have h2 : 0 ≤ m % N := Int.emod_nonneg m hn.ne'
      omega
    · rw [hv, WithZero.exp_inj, Int.toNat_of_nonneg (Int.emod_nonneg m hn.ne'), hk, Int.emod_def]
      ring

def e₀ (g : G) : E := (g : Matrix (Fin 2) (Fin 2) E) 0 0
def e₁ (g : G) : E := (g : Matrix (Fin 2) (Fin 2) E) 1 1

theorem continuous_e₀ : Continuous (e₀ : G → E) := Units.continuous_val.matrix_elem 0 0
theorem continuous_e₁ : Continuous (e₁ : G → E) := Units.continuous_val.matrix_elem 1 1

def Pset : Set G :=
  {g | InW (K := K) (v := v) n (Algebra.norm F (e₀ g)) ∧ InW (K := K) (v := v) n (Algebra.norm F (e₁ g))}

theorem isOpen_Pset : IsOpen (Pset : Set G) :=
  ((isOpen_setOf_inW n).preimage (continuous_algebraNorm.comp continuous_e₀)).inter
    ((isOpen_setOf_inW n).preimage (continuous_algebraNorm.comp continuous_e₁))

@[reducible] def measurableSpace_GL : MeasurableSpace G := AutomorphicForm.glBorelOf E

attribute [local instance] measurableSpace_GL

theorem borelSpace_GL : BorelSpace G := AutomorphicForm.borelSpace_glBorelOf E

attribute [local instance] borelSpace_GL

theorem measurableSet_Pset : MeasurableSet (Pset : Set G) := isOpen_Pset.measurableSet

def β (c : ℝ) (g : G) : ℝ := (Pset : Set G).indicator (fun _ => c) g

theorem measurable_β (c : ℝ) : Measurable (β (K := K) (L := L) (v := v) c) :=
  measurable_const.indicator measurableSet_Pset

theorem β_nonneg {c : ℝ} (hc : 0 ≤ c) (g : G) : 0 ≤ β c g := by
  unfold β; exact Set.indicator_nonneg (fun _ _ => hc) g

theorem β_le {c : ℝ} (hc : 0 ≤ c) (g : G) : β c g ≤ c := by
  unfold β; exact Set.indicator_le_self' (fun _ _ => hc) g

section Torus

variable {a b : v.adicCompletion K} {γ : GL (Fin 2) (v.adicCompletion K)}

local notation "T" => AutomorphicForm.localCentralizer K v γ

theorem entries_eq_zero_of_mem (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    {g : GF} (hg : g ∈ AutomorphicForm.localCentralizer K v γ) :
    (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  rw [AutomorphicForm.localCentralizer, Subgroup.mem_centralizer_iff] at hg
  simp only [Set.mem_singleton_iff, forall_eq] at hg
  rw [Units.ext_iff, Units.val_mul, Units.val_mul, hγ] at hg
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab
  have h01 := congrFun (congrFun hg 0) 1
  have h10 := congrFun (congrFun hg 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h01 h10
  constructor
  · have : (a - b) * (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by linear_combination h01
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hab'
    · exact h
  · have : (a - b) * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination -h10
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hab'
    · exact h

theorem mem_of_entries_eq_zero (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    {g : GF} (h01 : (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0) (h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    g ∈ AutomorphicForm.localCentralizer K v γ := by
  rw [AutomorphicForm.localCentralizer, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [Units.ext_iff, Units.val_mul, Units.val_mul, hγ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h10] <;> ring

def d₀ (t : GF) : F := (t : Matrix (Fin 2) (Fin 2) F) 0 0
def d₁ (t : GF) : F := (t : Matrix (Fin 2) (Fin 2) F) 1 1

theorem continuous_d₀ : Continuous (d₀ : GF → F) := Units.continuous_val.matrix_elem 0 0
theorem continuous_d₁ : Continuous (d₁ : GF → F) := Units.continuous_val.matrix_elem 1 1

theorem d₀_mul (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b]) (s t : T) :
    d₀ ((s * t : T) : GF) = d₀ (s : GF) * d₀ (t : GF) := by
  obtain ⟨hs01, -⟩ := entries_eq_zero_of_mem hab hγ s.2
  obtain ⟨-, ht10⟩ := entries_eq_zero_of_mem hab hγ t.2
  show ((((s : GF) * (t : GF) : GF)) : Matrix (Fin 2) (Fin 2) F) 0 0 = _
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp [d₀, hs01, ht10]

theorem d₁_mul (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b]) (s t : T) :
    d₁ ((s * t : T) : GF) = d₁ (s : GF) * d₁ (t : GF) := by
  obtain ⟨-, hs10⟩ := entries_eq_zero_of_mem hab hγ s.2
  obtain ⟨ht01, -⟩ := entries_eq_zero_of_mem hab hγ t.2
  show ((((s : GF) * (t : GF) : GF)) : Matrix (Fin 2) (Fin 2) F) 1 1 = _
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp [d₁, hs10, ht01]

theorem d₀_one : d₀ ((1 : T) : GF) = 1 := by simp [d₀]
theorem d₁_one : d₁ ((1 : T) : GF) = 1 := by simp [d₁]

theorem d₀_inv (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b]) (t : T) :
    d₀ ((t⁻¹ : T) : GF) = (d₀ (t : GF))⁻¹ := by
  have h := d₀_mul hab hγ t⁻¹ t
  rw [inv_mul_cancel, d₀_one] at h
  exact (eq_inv_of_mul_eq_one_left h.symm)

theorem d₁_inv (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b]) (t : T) :
    d₁ ((t⁻¹ : T) : GF) = (d₁ (t : GF))⁻¹ := by
  have h := d₁_mul hab hγ t⁻¹ t
  rw [inv_mul_cancel, d₁_one] at h
  exact (eq_inv_of_mul_eq_one_left h.symm)

theorem d₀_ne_zero (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b]) (t : T) :
    d₀ (t : GF) ≠ 0 := by
  intro h
  have := d₀_mul hab hγ t⁻¹ t
  rw [inv_mul_cancel, d₀_one, h, mul_zero] at this
  exact one_ne_zero this

theorem d₁_ne_zero (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b]) (t : T) :
    d₁ (t : GF) ≠ 0 := by
  intro h
  have := d₁_mul hab hγ t⁻¹ t
  rw [inv_mul_cancel, d₁_one, h, mul_zero] at this
  exact one_ne_zero this

def diagT (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (c₀ c₁ : F) (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0) : T :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![c₀, 0; 0, c₁]
      (by rw [Matrix.det_fin_two_of]; simp [h₀, h₁]),
    mem_of_entries_eq_zero hγ rfl rfl⟩

theorem d₀_diagT (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (c₀ c₁ : F) (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0) : d₀ ((diagT hγ c₀ c₁ h₀ h₁ : T) : GF) = c₀ := rfl

theorem d₁_diagT (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (c₀ c₁ : F) (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0) : d₁ ((diagT hγ c₀ c₁ h₀ h₁ : T) : GF) = c₁ := rfl

theorem t2Space_GF : T2Space GF := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → F))
  exact Units.isEmbedding_embedProduct.t2Space

theorem secondCountableTopology_GF : SecondCountableTopology GF := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) F) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → F))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

attribute [local instance] t2Space_GF secondCountableTopology_GF
  AutomorphicForm.locallyCompactSpace_localGL AutomorphicForm.localCentralizerBorel

theorem borelSpace_T : @BorelSpace T _ (AutomorphicForm.localCentralizerBorel K v γ) :=
  @BorelSpace.mk _ _ (AutomorphicForm.localCentralizerBorel K v γ) rfl

theorem isClosed_T : IsClosed ((AutomorphicForm.localCentralizer K v γ : Subgroup GF) : Set GF) :=
  Set.isClosed_centralizer _

theorem locallyCompactSpace_T : LocallyCompactSpace T :=
  (isClosed_T (γ := γ)).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem secondCountableTopology_T : SecondCountableTopology T :=
  TopologicalSpace.Subtype.secondCountableTopology _

attribute [local instance] borelSpace_T locallyCompactSpace_T secondCountableTopology_T

def TO : Set T := Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v

theorem isOpen_TO : IsOpen (TO : Set T) :=
  (AutomorphicForm.isOpen_localIntegralSet K v).preimage continuous_subtype_val

theorem isCompact_TO : IsCompact (TO : Set T) :=
  (isClosed_T (γ := γ)).isClosedEmbedding_subtypeVal.isCompact_preimage
    (AutomorphicForm.isCompact_localIntegralSet K v)

theorem one_mem_TO : (1 : T) ∈ (TO : Set T) := AutomorphicForm.one_mem_localIntegralSet K v

theorem measurableSet_TO : MeasurableSet (TO : Set T) := isOpen_TO.measurableSet

theorem mem_TO_iff (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b]) (t : T) :
    t ∈ (TO : Set T) ↔ Valued.v (d₀ (t : GF)) = 1 ∧ Valued.v (d₁ (t : GF)) = 1 := by
  obtain ⟨h01, h10⟩ := entries_eq_zero_of_mem hab hγ t.2
  obtain ⟨hi01, hi10⟩ := entries_eq_zero_of_mem hab hγ (t⁻¹).2
  have hinv : (((t : GF)⁻¹ : GF) : Matrix (Fin 2) (Fin 2) F) = (((t⁻¹ : T) : GF) : Matrix (Fin 2) (Fin 2) F) := rfl
  rw [TO, mem_preimage, AutomorphicForm.mem_localIntegralSet]
  simp only [HeightOneSpectrum.mem_adicCompletionIntegers, Fin.forall_fin_two, hinv, h01, h10, hi01, hi10,
    map_zero, zero_le', and_true, true_and]
  have e0 : (((t⁻¹ : T) : GF) : Matrix (Fin 2) (Fin 2) F) 0 0 = (d₀ (t : GF))⁻¹ := d₀_inv hab hγ t
  have e1 : (((t⁻¹ : T) : GF) : Matrix (Fin 2) (Fin 2) F) 1 1 = (d₁ (t : GF))⁻¹ := d₁_inv hab hγ t
  rw [e0, e1, map_inv₀, map_inv₀]
  change (Valued.v (d₀ (t : GF)) ≤ 1 ∧ Valued.v (d₁ (t : GF)) ≤ 1) ∧
      (Valued.v (d₀ (t : GF)))⁻¹ ≤ 1 ∧ (Valued.v (d₁ (t : GF)))⁻¹ ≤ 1 ↔ _
  have h0 : Valued.v (d₀ (t : GF)) ≠ 0 := (Valuation.ne_zero_iff _).2 (d₀_ne_zero hab hγ t)
  have h1 : Valued.v (d₁ (t : GF)) ≠ 0 := (Valuation.ne_zero_iff _).2 (d₁_ne_zero hab hγ t)
  rw [inv_le_one₀ (zero_lt_iff.2 h0), inv_le_one₀ (zero_lt_iff.2 h1)]
  constructor
  · rintro ⟨⟨a0, a1⟩, b0, b1⟩; exact ⟨le_antisymm a0 b0, le_antisymm a1 b1⟩
  · rintro ⟨a0, a1⟩; exact ⟨⟨a0.le, a1.le⟩, a0.ge, a1.ge⟩

def shell (k₀ k₁ : ℤ) : Set T :=
  {t | Valued.v (d₀ (t : GF)) = WithZero.exp k₀ ∧ Valued.v (d₁ (t : GF)) = WithZero.exp k₁}

theorem shell_eq_preimage (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (k₀ k₁ : ℤ) (t₀ : T) (h₀ : Valued.v (d₀ (t₀ : GF)) = WithZero.exp k₀)
    (h₁ : Valued.v (d₁ (t₀ : GF)) = WithZero.exp k₁) :
    shell k₀ k₁ = (fun s : T => t₀⁻¹ * s) ⁻¹' (TO : Set T) := by
  ext s
  rw [mem_preimage, mem_TO_iff hab hγ, shell, mem_setOf_eq, d₀_mul hab hγ, d₁_mul hab hγ,
    d₀_inv hab hγ, d₁_inv hab hγ, map_mul, map_mul, map_inv₀, map_inv₀, h₀, h₁]
  have e0 : (WithZero.exp k₀ : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.exp_ne_zero
  have e1 : (WithZero.exp k₁ : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.exp_ne_zero
  rw [inv_mul_eq_one₀ e0, inv_mul_eq_one₀ e1, eq_comm, eq_comm (a := WithZero.exp k₁)]

theorem exists_mem_shell (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (k₀ k₁ : ℤ) : ∃ t₀ : T, Valued.v (d₀ (t₀ : GF)) = WithZero.exp k₀ ∧
      Valued.v (d₁ (t₀ : GF)) = WithZero.exp k₁ := by
  obtain ⟨c₀, hc₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v (WithZero.exp k₀)
  obtain ⟨c₁, hc₁⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v (WithZero.exp k₁)
  have h₀ : c₀ ≠ 0 := fun h => by rw [h, map_zero] at hc₀; exact WithZero.exp_ne_zero hc₀.symm
  have h₁ : c₁ ≠ 0 := fun h => by rw [h, map_zero] at hc₁; exact WithZero.exp_ne_zero hc₁.symm
  exact ⟨diagT hγ c₀ c₁ h₀ h₁, hc₀, hc₁⟩

variable (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
  [τ.IsHaarMeasure]

theorem measure_shell (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b]) (k₀ k₁ : ℤ) :
    τ (shell k₀ k₁) = τ TO := by
  obtain ⟨t₀, h₀, h₁⟩ := exists_mem_shell hγ k₀ k₁
  rw [shell_eq_preimage hab hγ k₀ k₁ t₀ h₀ h₁]
  exact measure_preimage_mul τ _ _

theorem measurableSet_shell (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b]) (k₀ k₁ : ℤ) :
    MeasurableSet (shell (γ := γ) k₀ k₁) := by
  obtain ⟨t₀, h₀, h₁⟩ := exists_mem_shell hγ k₀ k₁
  rw [shell_eq_preimage hab hγ k₀ k₁ t₀ h₀ h₁]
  exact measurableSet_TO.preimage (measurable_const_mul _)

theorem TO_pos : 0 < τ TO := isOpen_TO.measure_pos τ ⟨1, one_mem_TO⟩

theorem TO_lt_top : τ TO < ⊤ := isCompact_TO.measure_lt_top

theorem real_TO_pos : 0 < τ.real TO :=
  ENNReal.toReal_pos (TO_pos τ).ne' (TO_lt_top τ).ne

theorem e₀_toTensorGL_mul (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (t : T) (u : G) :
    e₀ (AutomorphicForm.toTensorGL K L F (t : GF) * u) = algebraMap F E (d₀ (t : GF)) * e₀ u := by
  obtain ⟨h01, -⟩ := entries_eq_zero_of_mem hab hγ t.2
  show ((((AutomorphicForm.toTensorGL K L F (t : GF)) : G) * u : G) : Matrix (Fin 2) (Fin 2) E) 0 0 = _
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hmap : ∀ i j, ((AutomorphicForm.toTensorGL K L F (t : GF) : G) : Matrix (Fin 2) (Fin 2) E) i j =
      algebraMap F E (((t : GF) : Matrix (Fin 2) (Fin 2) F) i j) := fun i j => rfl
  rw [hmap, hmap, h01, map_zero, zero_mul, add_zero]
  rfl

theorem e₁_toTensorGL_mul (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    (t : T) (u : G) :
    e₁ (AutomorphicForm.toTensorGL K L F (t : GF) * u) = algebraMap F E (d₁ (t : GF)) * e₁ u := by
  obtain ⟨-, h10⟩ := entries_eq_zero_of_mem hab hγ t.2
  show ((((AutomorphicForm.toTensorGL K L F (t : GF)) : G) * u : G) : Matrix (Fin 2) (Fin 2) E) 1 1 = _
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hmap : ∀ i j, ((AutomorphicForm.toTensorGL K L F (t : GF) : G) : Matrix (Fin 2) (Fin 2) E) i j =
      algebraMap F E (((t : GF) : Matrix (Fin 2) (Fin 2) F) i j) := fun i j => rfl
  rw [hmap, hmap, h10, map_zero, zero_mul, zero_add]
  rfl

theorem isUnit_e₀_e₁ {u : G} (h01 : (u : Matrix (Fin 2) (Fin 2) E) 0 1 = 0) :
    IsUnit (e₀ u) ∧ IsUnit (e₁ u) := by
  have hdet : IsUnit ((u : Matrix (Fin 2) (Fin 2) E).det) := Matrix.isUnits_det_units u
  rw [Matrix.det_fin_two, h01, zero_mul, sub_zero] at hdet
  exact ⟨isUnit_of_mul_isUnit_left hdet, isUnit_of_mul_isUnit_right hdet⟩

theorem preimage_Pset_eq_shell (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    {u : G} (h01 : (u : Matrix (Fin 2) (Fin 2) E) 0 1 = 0) :
    ∃ k₀ k₁ : ℤ, (fun t : T => AutomorphicForm.toTensorGL K L F (t : GF) * u) ⁻¹' (Pset : Set G) = shell k₀ k₁ := by
  obtain ⟨hu0, hu1⟩ := isUnit_e₀_e₁ h01
  have hN0 : Algebra.norm F (e₀ u) ≠ 0 := norm_ne_zero_of_isUnit hu0
  have hN1 : Algebra.norm F (e₁ u) ≠ 0 := norm_ne_zero_of_isUnit hu1
  set m₀ : ℤ := WithZero.log (Valued.v (Algebra.norm F (e₀ u))) with hm₀
  set m₁ : ℤ := WithZero.log (Valued.v (Algebra.norm F (e₁ u))) with hm₁
  have hv0 : Valued.v (Algebra.norm F (e₀ u)) = WithZero.exp m₀ :=
    (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hN0)).symm
  have hv1 : Valued.v (Algebra.norm F (e₁ u)) = WithZero.exp m₁ :=
    (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hN1)).symm
  refine ⟨-(m₀ / n), -(m₁ / n), ?_⟩
  ext t
  have ht0 : Valued.v (d₀ (t : GF)) ≠ 0 := (Valuation.ne_zero_iff _).2 (d₀_ne_zero hab hγ t)
  have ht1 : Valued.v (d₁ (t : GF)) ≠ 0 := (Valuation.ne_zero_iff _).2 (d₁_ne_zero hab hγ t)
  have hk0 : Valued.v (d₀ (t : GF)) = WithZero.exp (WithZero.log (Valued.v (d₀ (t : GF)))) :=
    (WithZero.exp_log ht0).symm
  have hk1 : Valued.v (d₁ (t : GF)) = WithZero.exp (WithZero.log (Valued.v (d₁ (t : GF)))) :=
    (WithZero.exp_log ht1).symm
  simp only [mem_preimage, Pset, mem_setOf_eq, shell]
  rw [e₀_toTensorGL_mul hab hγ, e₁_toTensorGL_mul hab hγ, norm_algebraMap_mul, norm_algebraMap_mul,
    inW_pow_mul_iff finrank_pos hk0 hv0, inW_pow_mul_iff finrank_pos hk1 hv1]
  constructor
  · rintro ⟨a0, a1⟩
    exact ⟨by rw [hk0, a0], by rw [hk1, a1]⟩
  · rintro ⟨a0, a1⟩
    rw [a0, WithZero.log_exp, a1, WithZero.log_exp]
    exact ⟨rfl, rfl⟩

theorem integral_β (hab : a ≠ b) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b])
    {u : G} (h01 : (u : Matrix (Fin 2) (Fin 2) E) 0 1 = 0) :
    ∫ t : T, β (τ.real TO)⁻¹ (AutomorphicForm.toTensorGL K L F (t : GF) * u) ∂τ = 1 := by
  obtain ⟨k₀, k₁, hk⟩ := preimage_Pset_eq_shell (K := K) (L := L) hab hγ h01
  have hfun : (fun t : T => β (τ.real TO)⁻¹ (AutomorphicForm.toTensorGL K L F (t : GF) * u)) =
      (shell k₀ k₁).indicator fun _ => (τ.real TO)⁻¹ := by
    funext t
    rw [← hk]
    simp only [β, Set.indicator, mem_preimage]
    rfl
  rw [hfun, integral_indicator_const _ (measurableSet_shell hab hγ k₀ k₁), smul_eq_mul,
    Measure.real, measure_shell τ hab hγ, ← Measure.real, mul_inv_cancel₀ (real_TO_pos τ).ne']

end Torus

end KcTorusSectionFn

end

open KcTorusSectionFn in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (a b : v.adicCompletion K) (hab : a ≠ b)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![a, 0; 0, b])
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ) :
    ∃ β : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ,
      Measurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] β ∧
      (∀ x, 0 ≤ β x) ∧ (∃ C : ℝ, ∀ x, β x ≤ C) ∧
      ∀ u : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 →
        (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 →
        (letI := AutomorphicForm.localCentralizerBorel K v γ
         ∫ t : AutomorphicForm.localCentralizer K v γ,
            β (AutomorphicForm.toTensorGL K L (v.adicCompletion K)
              (t : GL (Fin 2) (v.adicCompletion K)) * u) ∂τ) = 1 := by
  haveI := hτ
  letI := AutomorphicForm.localCentralizerBorel K v γ
  have hc : 0 ≤ (τ.real (TO (γ := γ)))⁻¹ := inv_nonneg.2 (real_TO_pos (γ := γ) τ).le
  exact ⟨KcTorusSectionFn.β (τ.real (TO (γ := γ)))⁻¹, measurable_β _, β_nonneg hc, ⟨_, β_le hc⟩,
    fun u h01 _ => integral_β τ hab hγ h01⟩

end S_AutomorphicForm_exists_measurable_forall_integral_localCentralizer_toTensorGL_mul_eq_one_of_diagonal
end P2MW
export P2MW.S_AutomorphicForm_exists_measurable_forall_integral_localCentralizer_toTensorGL_mul_eq_one_of_diagonal (solution)
