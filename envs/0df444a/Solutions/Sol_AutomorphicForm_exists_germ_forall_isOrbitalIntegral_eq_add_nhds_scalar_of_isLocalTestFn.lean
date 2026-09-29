-- Prove2me | solution 1 for AutomorphicForm.exists_germ_forall_isOrbitalIntegral_eq_add_nhds_scalar_of_isLocalTestFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/0ae92b84-95ce-56cc-81a8-32279e172e96

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_TwistedNormClasses
import Theorems.Thm_AutomorphicForm_exists_forall_nhds_scalar_forall_isOrbitalIntegral_eq_add_mul_of_mem_localCentralizer_of_not_isSquare
import Theorems.Thm_AutomorphicForm_exists_nhds_scalar_forall_isOrbitalIntegral_eq_mul_integral_unipotentGL2_conj_of_diagonal
import Theorems.Thm_AutomorphicForm_exists_map_val_eq_map_conj_and_isOrbitalIntegral_conj_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_germ_forall_isOrbitalIntegral_eq_add_nhds_scalar_of_isLocalTestFn
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.TateLocal.conductorExponentAt_one NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

namespace KcEllGermReduce

open AutomorphicForm

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => v.adicCompletion K
local notation "G₂" => GL (Fin 2) (v.adicCompletion K)

theorem t2Space_GL : T2Space G₂ := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → F))
  exact Units.isEmbedding_embedProduct.t2Space

theorem trace_conj (x g : G₂) :
    ((x * g * x⁻¹ : G₂) : Matrix (Fin 2) (Fin 2) F).trace = (g : Matrix (Fin 2) (Fin 2) F).trace := by
  rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.one_mul]

theorem det_conj (x g : G₂) :
    ((x * g * x⁻¹ : G₂) : Matrix (Fin 2) (Fin 2) F).det = (g : Matrix (Fin 2) (Fin 2) F).det := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul]

theorem isRegularSemisimple_conj_iff (x g : G₂) : IsRegularSemisimple (x * g * x⁻¹) ↔ IsRegularSemisimple g := by
  rw [isRegularSemisimple_iff_ne_zero, isRegularSemisimple_iff_ne_zero, trace_conj, det_conj]

theorem mem_localCentralizer_conj_iff (x γ g : G₂) :
    x * g * x⁻¹ ∈ localCentralizer K v (x * γ * x⁻¹) ↔ g ∈ localCentralizer K v γ := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * γ = x⁻¹ * (x * g * x⁻¹ * (x * γ * x⁻¹)) * x := by group
      _ = x⁻¹ * (x * γ * x⁻¹ * (x * g * x⁻¹)) * x := by rw [h]
      _ = γ * g := by group
  · intro h
    calc x * g * x⁻¹ * (x * γ * x⁻¹) = x * (g * γ) * x⁻¹ := by group
      _ = x * (γ * g) * x⁻¹ := by rw [h]
      _ = x * γ * x⁻¹ * (x * g * x⁻¹) := by group

noncomputable def conjEquiv (x γ : G₂) : localCentralizer K v γ ≃ₜ* localCentralizer K v (x * γ * x⁻¹) where
  toFun t := ⟨x * t * x⁻¹, (mem_localCentralizer_conj_iff K v x γ t).2 t.2⟩
  invFun t' := ⟨x⁻¹ * t' * x, by
    have h := (mem_localCentralizer_conj_iff K v x⁻¹ (x * γ * x⁻¹) t').2 t'.2
    simpa [mul_assoc] using h⟩
  left_inv t := by ext; simp [mul_assoc]
  right_inv t' := by ext; simp [mul_assoc]
  map_mul' s t := by ext; simp [mul_assoc]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

@[scoped simp] theorem coe_conjEquiv (x γ : G₂) (t : localCentralizer K v γ) :
    ((conjEquiv K v x γ t : localCentralizer K v (x * γ * x⁻¹)) : G₂) = x * t * x⁻¹ := rfl

theorem continuous_conj (x : G₂) : Continuous fun g : G₂ => x * g * x⁻¹ :=
  (continuous_const.mul continuous_id).mul continuous_const

theorem conj_scalar (x : G₂) (c : Fˣ) :
    x * Matrix.GeneralLinearGroup.scalar (Fin 2) c * x⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  have hc : Matrix.GeneralLinearGroup.scalar (Fin 2) c * x⁻¹ = x⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
    refine Units.ext ?_
    simp only [Units.val_mul]
    exact (Matrix.scalar_commute (n := Fin 2) (c : F) (fun r' => Commute.all _ _) _).eq
  rw [mul_assoc, hc, ← mul_assoc, mul_inv_cancel, one_mul]

theorem preimage_conj_mem_nhds (x : G₂) (c : Fˣ) {W : Set G₂}
    (hW : W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) :
    (fun g : G₂ => x * g * x⁻¹) ⁻¹' W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
  refine (continuous_conj K v x).continuousAt.preimage_mem_nhds ?_
  rwa [conj_scalar]

theorem apply_ne_of_diagonal_regular (t₀ : G₂)
    (h01 : (t₀ : Matrix (Fin 2) (Fin 2) F) 0 1 = 0) (h10 : (t₀ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (ht₀ : IsRegularSemisimple t₀) :
    (t₀ : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ (t₀ : Matrix (Fin 2) (Fin 2) F) 1 1 := by
  intro heq
  apply (isRegularSemisimple_iff_ne_zero t₀).1 ht₀
  rw [Matrix.trace_fin_two, Matrix.det_fin_two, h01, h10, heq]
  ring

theorem diagonal_of_mem_localCentralizer (t₀ g : G₂)
    (h01 : (t₀ : Matrix (Fin 2) (Fin 2) F) 0 1 = 0) (h10 : (t₀ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (ht₀ : IsRegularSemisimple t₀) (hg : g ∈ localCentralizer K v t₀) :
    (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  have hab := apply_ne_of_diagonal_regular K v t₀ h01 h10 ht₀
  have hcomm : (g : Matrix (Fin 2) (Fin 2) F) * (t₀ : Matrix (Fin 2) (Fin 2) F) =
      (t₀ : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) := by
    rw [← Units.val_mul, ← Units.val_mul, (Subgroup.mem_centralizer_singleton_iff.1 hg)]
  have e01 := congrFun (congrFun hcomm 0) 1
  have e10 := congrFun (congrFun hcomm 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, mul_zero, zero_mul, add_zero, zero_add] at e01 e10
  constructor
  · have : (g : Matrix (Fin 2) (Fin 2) F) 0 1 * ((t₀ : Matrix (Fin 2) (Fin 2) F) 1 1 - (t₀ : Matrix (Fin 2) (Fin 2) F) 0 0) = 0 := by
      rw [mul_sub, e01]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h).symm hab
  · have : (g : Matrix (Fin 2) (Fin 2) F) 1 0 * ((t₀ : Matrix (Fin 2) (Fin 2) F) 0 0 - (t₀ : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
      rw [mul_sub, e10]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) hab

theorem mul_comm_of_diagonal (a b : G₂)
    (ha01 : (a : Matrix (Fin 2) (Fin 2) F) 0 1 = 0) (ha10 : (a : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (hb01 : (b : Matrix (Fin 2) (Fin 2) F) 0 1 = 0) (hb10 : (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    a * b = b * a := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha01, ha10, hb01, hb10, mul_comm]

theorem localCentralizer_le_of_split (x t₀ γ₀ γ : G₂) (hx : x * γ₀ * x⁻¹ = t₀)
    (h01 : (t₀ : Matrix (Fin 2) (Fin 2) F) 0 1 = 0) (h10 : (t₀ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (ht₀ : IsRegularSemisimple t₀) (hγ : γ ∈ localCentralizer K v γ₀) (hγreg : IsRegularSemisimple γ) :
    localCentralizer K v γ ≤ localCentralizer K v γ₀ := by
  intro g hg
  have hγ' : x * γ * x⁻¹ ∈ localCentralizer K v t₀ := by
    rw [← hx]; exact (mem_localCentralizer_conj_iff K v x γ₀ γ).2 hγ
  have hγ'd := diagonal_of_mem_localCentralizer K v t₀ (x * γ * x⁻¹) h01 h10 ht₀ hγ'
  have hγ'reg : IsRegularSemisimple (x * γ * x⁻¹) := (isRegularSemisimple_conj_iff K v x γ).2 hγreg
  have hg' : x * g * x⁻¹ ∈ localCentralizer K v (x * γ * x⁻¹) := (mem_localCentralizer_conj_iff K v x γ g).2 hg
  have hg'd := diagonal_of_mem_localCentralizer K v (x * γ * x⁻¹) (x * g * x⁻¹) hγ'd.1 hγ'd.2 hγ'reg hg'
  have hgt : x * g * x⁻¹ ∈ localCentralizer K v t₀ :=
    Subgroup.mem_centralizer_singleton_iff.2 (mul_comm_of_diagonal K v _ _ hg'd.1 hg'd.2 h01 h10)
  rw [← hx] at hgt
  exact (mem_localCentralizer_conj_iff K v x γ₀ g).1 hgt

theorem isSquare_disc_of_diagonal (γ₀ : G₂)
    (h01 : (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 1 = 0) (h10 : (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    IsSquare ((γ₀ : Matrix (Fin 2) (Fin 2) F).trace ^ 2 - 4 * (γ₀ : Matrix (Fin 2) (Fin 2) F).det) :=
  ⟨(γ₀ : Matrix (Fin 2) (Fin 2) F) 0 0 - (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 1, by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two, h01, h10]; ring⟩

theorem charZero_F : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective

theorem ne_smul_one_of_disc_ne_zero {M : Matrix (Fin 2) (Fin 2) F}
    (h : Matrix.trace M ^ 2 - 4 * Matrix.det M ≠ 0) (e : F) : M ≠ e • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rintro rfl
  apply h
  rw [Matrix.trace_smul, Matrix.trace_one, Matrix.det_smul, Matrix.det_one, Fintype.card_fin]
  simp
  ring

theorem exists_conj_eq_diagonal (γ : G₂) (hγ : IsRegularSemisimple γ)
    (hsq : IsSquare ((γ : Matrix (Fin 2) (Fin 2) F).trace ^ 2 - 4 * (γ : Matrix (Fin 2) (Fin 2) F).det)) :
    ∃ x t₀ : G₂, (t₀ : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧ (t₀ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      IsRegularSemisimple t₀ ∧ x * γ * x⁻¹ = t₀ := by
  haveI := charZero_F K v
  set s : F := (γ : Matrix (Fin 2) (Fin 2) F).trace with hs
  set n : F := (γ : Matrix (Fin 2) (Fin 2) F).det with hn
  have hdisc : s ^ 2 - 4 * n ≠ 0 := (isRegularSemisimple_iff_ne_zero γ).1 hγ
  obtain ⟨r, hr⟩ := hsq
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hdisc (by rw [hr, mul_zero])
  set l₁ : F := (s + r) / 2 with hl₁
  set l₂ : F := (s - r) / 2 with hl₂
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hsum : l₁ + l₂ = s := by rw [hl₁, hl₂]; field_simp; ring
  have hprod : l₁ * l₂ = n := by
    have : s ^ 2 - r * r = 4 * n := by rw [← hr]; ring
    rw [hl₁, hl₂]
    field_simp
    linear_combination this
  have hn0 : n ≠ 0 := by
    intro h0
    exact (Matrix.GeneralLinearGroup.det_ne_zero γ) (by rw [← hn, h0])
  have hl : l₁ * l₂ ≠ 0 := by rw [hprod]; exact hn0
  let t₀ : G₂ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![l₁, 0; 0, l₂]
    (by rw [Matrix.det_fin_two_of]; simpa using hl)
  have ht₀val : ((t₀ : G₂) : Matrix (Fin 2) (Fin 2) F) = !![l₁, 0; 0, l₂] := rfl
  have hreg : ((t₀ : G₂) : Matrix (Fin 2) (Fin 2) F).trace ^ 2 - 4 * ((t₀ : G₂) : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [ht₀val, Matrix.trace_fin_two_of, Matrix.det_fin_two_of, hsum, mul_zero, sub_zero, hprod]
    exact hdisc
  have hne : ∀ e : F, ((t₀ : G₂) : Matrix (Fin 2) (Fin 2) F) ≠ e • (1 : Matrix (Fin 2) (Fin 2) F) :=
    ne_smul_one_of_disc_ne_zero K v hreg
  have hneγ : ∀ e : F, ((γ : G₂) : Matrix (Fin 2) (Fin 2) F) ≠ e • (1 : Matrix (Fin 2) (Fin 2) F) :=
    ne_smul_one_of_disc_ne_zero K v hdisc
  have htr : ((t₀ : G₂) : Matrix (Fin 2) (Fin 2) F).trace = (γ : Matrix (Fin 2) (Fin 2) F).trace := by
    rw [ht₀val, Matrix.trace_fin_two_of, hsum]
  have hdet : ((t₀ : G₂) : Matrix (Fin 2) (Fin 2) F).det = (γ : Matrix (Fin 2) (Fin 2) F).det := by
    rw [ht₀val, Matrix.det_fin_two_of, mul_zero, sub_zero, hprod]
  obtain ⟨Q, hQ⟩ := LT.TwistedNorm.GL2.exists_conj_of_trace_eq_det_eq _ _ hne hneγ htr hdet
  refine ⟨Q, t₀, rfl, rfl, (isRegularSemisimple_iff_ne_zero _).2 hreg, ?_⟩
  rw [hQ]
  group

theorem exists_conj_elliptic (γ : G₂) (hγ : IsRegularSemisimple γ)
    (hsq : ¬ IsSquare ((γ : Matrix (Fin 2) (Fin 2) F).trace ^ 2 - 4 * (γ : Matrix (Fin 2) (Fin 2) F).det)) :
    ∃ (x : G₂) (d : F) (_ : ¬ IsSquare d) (u : G₂),
      (u : Matrix (Fin 2) (Fin 2) F) = !![0, 1; d, 0] ∧
      localCentralizer K v (x * γ * x⁻¹) = localCentralizer K v u := by
  haveI := charZero_F K v
  set s : F := (γ : Matrix (Fin 2) (Fin 2) F).trace with hs
  set n : F := (γ : Matrix (Fin 2) (Fin 2) F).det with hn
  have hdisc : s ^ 2 - 4 * n ≠ 0 := (isRegularSemisimple_iff_ne_zero γ).1 hγ
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  set d : F := s / 2 * (s / 2) - n with hd_def
  have h4d : s ^ 2 - 4 * n = (2 : F) * (2 * d) := by rw [hd_def]; field_simp; ring
  have hd : ¬ IsSquare d := by
    rintro ⟨e, he⟩
    apply hsq
    refine ⟨2 * e, ?_⟩
    rw [h4d, he]; ring
  have hd0 : d ≠ 0 := fun h0 => hd ⟨0, by rw [h0, mul_zero]⟩
  have hn0 : n ≠ 0 := by
    intro h0
    exact (Matrix.GeneralLinearGroup.det_ne_zero γ) (by rw [← hn, h0])
  let u : G₂ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; d, 0]
    (by rw [Matrix.det_fin_two_of]; simpa using hd0)
  have huval : ((u : G₂) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; d, 0] := rfl
  let δ₀ : G₂ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![s / 2, 1; d, s / 2]
    (by rw [Matrix.det_fin_two_of, hd_def]; ring_nf; simpa using hn0)
  have hδval : ((δ₀ : G₂) : Matrix (Fin 2) (Fin 2) F) = !![s / 2, 1; d, s / 2] := rfl
  have htr : ((δ₀ : G₂) : Matrix (Fin 2) (Fin 2) F).trace = (γ : Matrix (Fin 2) (Fin 2) F).trace := by
    rw [hδval, Matrix.trace_fin_two_of, ← hs]; ring
  have hdet : ((δ₀ : G₂) : Matrix (Fin 2) (Fin 2) F).det = (γ : Matrix (Fin 2) (Fin 2) F).det := by
    rw [hδval, Matrix.det_fin_two_of, ← hn, hd_def]; ring
  have hne : ∀ e : F, ((δ₀ : G₂) : Matrix (Fin 2) (Fin 2) F) ≠ e • (1 : Matrix (Fin 2) (Fin 2) F) := by
    intro e h
    have := congrFun (congrFun h 0) 1
    rw [hδval] at this
    simp at this
  have hneγ : ∀ e : F, ((γ : G₂) : Matrix (Fin 2) (Fin 2) F) ≠ e • (1 : Matrix (Fin 2) (Fin 2) F) :=
    ne_smul_one_of_disc_ne_zero K v hdisc
  obtain ⟨Q, hQ⟩ := LT.TwistedNorm.GL2.exists_conj_of_trace_eq_det_eq _ _ hne hneγ htr hdet
  have hx : Q * γ * Q⁻¹ = δ₀ := by rw [hQ]; group

  have hsum : ((δ₀ : G₂) : Matrix (Fin 2) (Fin 2) F) = (s / 2) • (1 : Matrix (Fin 2) (Fin 2) F) + (u : Matrix (Fin 2) (Fin 2) F) := by
    rw [hδval, huval]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hCent : localCentralizer K v δ₀ = localCentralizer K v u := by
    ext g
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, Units.ext_iff,
      Units.ext_iff, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, hsum, mul_add, add_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, add_right_inj]
  refine ⟨Q, d, hd, u, huval, ?_⟩
  rw [hx]
  exact hCent

theorem isClosed_localCentralizer (γ : G₂) : IsClosed ((localCentralizer K v γ : Subgroup G₂) : Set G₂) := by
  haveI := t2Space_GL K v
  have hset : ((localCentralizer K v γ : Subgroup G₂) : Set G₂) = {g : G₂ | g * γ = γ * g} := by
    ext g
    exact Subgroup.mem_centralizer_singleton_iff
  rw [hset]
  exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

theorem measurableEmbedding_val (γ : G₂) :
    @MeasurableEmbedding (localCentralizer K v γ) G₂ (localCentralizerBorel K v γ) (localGLBorel K v) Subtype.val := by
  letI : MeasurableSpace G₂ := localGLBorel K v
  haveI : BorelSpace G₂ := borelSpace_localGLBorel K v
  have h1 : MeasurableEmbedding (Subtype.val : ((localCentralizer K v γ : Subgroup G₂) : Set G₂) → G₂) :=
    MeasurableEmbedding.subtype_coe (isClosed_localCentralizer K v γ).measurableSet
  have hms : localCentralizerBorel K v γ =
      (Subtype.instMeasurableSpace : MeasurableSpace (localCentralizer K v γ)) :=
    (@BorelSpace.measurable_eq (localCentralizer K v γ) _ Subtype.instMeasurableSpace
      (Subtype.borelSpace ((localCentralizer K v γ : Subgroup G₂) : Set G₂))).symm
  rw [hms]
  exact h1

theorem preimage_conj_image_val (x γ : G₂) (s : Set (localCentralizer K v (x * γ * x⁻¹))) :
    (fun g : G₂ => x * g * x⁻¹) ⁻¹' (Subtype.val '' s) = Subtype.val '' ((conjEquiv K v x γ) ⁻¹' s) := by
  ext g
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨t', ht', hgt'⟩
    have hg : g ∈ localCentralizer K v γ := by
      have h := t'.2
      rw [hgt'] at h
      exact (mem_localCentralizer_conj_iff K v x γ g).1 h
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    have : conjEquiv K v x γ ⟨g, hg⟩ = t' := Subtype.ext (by rw [coe_conjEquiv]; exact hgt'.symm)
    rw [this]
    exact ht'
  · rintro ⟨t, ht, rfl⟩
    exact ⟨conjEquiv K v x γ t, ht, rfl⟩

theorem isHaarMeasure_comap_val_map_conj (x γ : G₂) (νT : @Measure G₂ (localGLBorel K v))
    (h : @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v γ)
      (@Measure.comap _ _ (localCentralizerBorel K v γ) (localGLBorel K v) Subtype.val νT)) :
    @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v (x * γ * x⁻¹))
      (@Measure.comap _ _ (localCentralizerBorel K v (x * γ * x⁻¹)) (localGLBorel K v) Subtype.val
        (@Measure.map _ _ (localGLBorel K v) (localGLBorel K v) (fun g : G₂ => x * g * x⁻¹) νT)) := by
  letI : MeasurableSpace G₂ := localGLBorel K v
  haveI : BorelSpace G₂ := borelSpace_localGLBorel K v
  letI := localCentralizerBorel K v γ
  letI := localCentralizerBorel K v (x * γ * x⁻¹)
  haveI : BorelSpace (localCentralizer K v γ) := ⟨rfl⟩
  haveI : BorelSpace (localCentralizer K v (x * γ * x⁻¹)) := ⟨rfl⟩
  haveI := h
  have hemb := measurableEmbedding_val K v γ
  have hemb' := measurableEmbedding_val K v (x * γ * x⁻¹)
  have hcx : Measurable fun g : G₂ => x * g * x⁻¹ := (continuous_conj K v x).measurable
  have he : Measurable (conjEquiv K v x γ : localCentralizer K v γ → localCentralizer K v (x * γ * x⁻¹)) :=
    (map_continuous (conjEquiv K v x γ)).measurable
  have key : Measure.comap Subtype.val (Measure.map (fun g : G₂ => x * g * x⁻¹) νT) =
      Measure.map (conjEquiv K v x γ) (Measure.comap Subtype.val νT) := by
    ext s hs
    rw [hemb'.comap_apply, Measure.map_apply hcx (hemb'.measurableSet_image.2 hs), Measure.map_apply he hs,
      hemb.comap_apply, preimage_conj_image_val]
  rw [key]
  exact (conjEquiv K v x γ).isHaarMeasure_map _

theorem guard_of_eq {H₁ H₂ : Subgroup G₂} (hH : H₁ = H₂) (ρ : @Measure G₂ (localGLBorel K v))
    (h : @Measure.IsHaarMeasure H₁ _ _ (borel H₁) (@Measure.comap H₁ G₂ (borel H₁) (localGLBorel K v) Subtype.val ρ)) :
    @Measure.IsHaarMeasure H₂ _ _ (borel H₂) (@Measure.comap H₂ G₂ (borel H₂) (localGLBorel K v) Subtype.val ρ) := by
  subst hH
  exact h

theorem measure_pos_lt_top_of_guard (γ₀ x : G₂) (νT : @Measure G₂ (localGLBorel K v))
    (h : @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v γ₀)
      (@Measure.comap _ _ (localCentralizerBorel K v γ₀) (localGLBorel K v) Subtype.val νT)) :
    0 < νT {g : G₂ | g ∈ localCentralizer K v γ₀ ∧ x * g * x⁻¹ ∈ localIntegralSet K v} ∧
      νT {g : G₂ | g ∈ localCentralizer K v γ₀ ∧ x * g * x⁻¹ ∈ localIntegralSet K v} < ⊤ := by
  letI : MeasurableSpace G₂ := localGLBorel K v
  haveI : BorelSpace G₂ := borelSpace_localGLBorel K v
  letI := localCentralizerBorel K v γ₀
  haveI : BorelSpace (localCentralizer K v γ₀) := ⟨rfl⟩
  haveI := h
  have hemb := measurableEmbedding_val K v γ₀
  set U : Set (localCentralizer K v γ₀) := {t | x * (t : G₂) * x⁻¹ ∈ localIntegralSet K v} with hU
  have hUo : IsOpen U :=
    (isOpen_localIntegralSet K v).preimage ((continuous_conj K v x).comp continuous_subtype_val)
  have h1U : (1 : localCentralizer K v γ₀) ∈ U := by
    show x * ((1 : localCentralizer K v γ₀) : G₂) * x⁻¹ ∈ localIntegralSet K v
    rw [OneMemClass.coe_one, mul_one, mul_inv_cancel]
    exact one_mem_localIntegralSet K v
  have hUc : IsCompact U := by

    let φ : G₂ ≃ₜ G₂ := (Homeomorph.mulLeft x).trans (Homeomorph.mulRight x⁻¹)
    have hφ : (fun g : G₂ => x * g * x⁻¹) = φ := by
      funext g
      simp [φ, Homeomorph.trans_apply]
    have hc : IsCompact ((fun g : G₂ => x * g * x⁻¹) ⁻¹' localIntegralSet K v) := by
      rw [hφ]
      exact φ.isCompact_preimage.2 (isCompact_localIntegralSet K v)
    have hce : Topology.IsClosedEmbedding (Subtype.val : localCentralizer K v γ₀ → G₂) :=
      (isClosed_localCentralizer K v γ₀).isClosedEmbedding_subtypeVal
    exact hce.isCompact_preimage hc
  have himage : Subtype.val '' U = {g : G₂ | g ∈ localCentralizer K v γ₀ ∧ x * g * x⁻¹ ∈ localIntegralSet K v} := by
    ext g
    simp only [Set.mem_image, Set.mem_setOf_eq, hU]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t.2, ht⟩
    · rintro ⟨hg, hgx⟩
      exact ⟨⟨g, hg⟩, hgx, rfl⟩
  have hval : Measure.comap Subtype.val νT U = νT (Subtype.val '' U) := hemb.comap_apply νT U
  rw [← himage, ← hval]
  exact ⟨hUo.measure_pos _ ⟨1, h1U⟩, hUc.measure_lt_top⟩

end KcEllGermReduce
p2m_reactivate "P2MW.S_AutomorphicForm_exists_germ_forall_isOrbitalIntegral_eq_add_nhds_scalar_of_isLocalTestFn.KcEllGermReduce"

open KcEllGermReduce AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ) :
    ∃ ν : (GL (Fin 2) (v.adicCompletion K) → ℂ) → ℂ,
      ∀ (γ₀ : GL (Fin 2) (v.adicCompletion K)), AutomorphicForm.IsRegularSemisimple γ₀ →
      ∀ (νT : @Measure (GL (Fin 2) (v.adicCompletion K)) (AutomorphicForm.localGLBorel K v)),
      ∃ (A : ℂ) (B : GL (Fin 2) (v.adicCompletion K) → ℂ),

        (∀ (f : GL (Fin 2) (v.adicCompletion K) → ℂ), AutomorphicForm.IsLocalTestFn K v f →
          letI := AutomorphicForm.localGLBorel K v
          ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
            ∀ γ ∈ W, γ ∈ AutomorphicForm.localCentralizer K v γ₀ → AutomorphicForm.IsRegularSemisimple γ →
            ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ)),
              @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ →
              @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ) (AutomorphicForm.localGLBorel K v)
                  Subtype.val τ = νT →
              ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v γ τ f I →
                I = A * f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) + B γ * ν f) ∧

        (((γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
            (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0) →
          (@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₀)
              (@Measure.comap _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) (AutomorphicForm.localGLBorel K v)
                Subtype.val νT)) →
          A = 0 ∧
          letI := AutomorphicForm.localGLBorel K v
          ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
            ∀ γ ∈ W, γ ∈ AutomorphicForm.localCentralizer K v γ₀ → AutomorphicForm.IsRegularSemisimple γ → B γ ≠ 0) ∧

        ((∀ g : GL (Fin 2) (v.adicCompletion K),
            ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
               ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)) →
          (@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₀)
              (@Measure.comap _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) (AutomorphicForm.localGLBorel K v)
                Subtype.val νT)) →
          A ≠ 0) := by

  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := localGLBorel K v
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion K)) := borelSpace_localGLBorel K v
  haveI := t2Space_GL K v
  letI : MeasurableSpace (v.adicCompletion K) := borel _
  haveI : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
  let ν₀ : Measure (v.adicCompletion K) := Measure.addHaar

  refine ⟨fun f => ∫ k, (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) k *
      (∫ y, f (Matrix.GeneralLinearGroup.scalar (Fin 2) c * (k⁻¹ * unipotentGL2 y * k)) ∂ν₀) ∂(localHaar K v), ?_⟩
  intro γ₀ hγ₀ νT
  by_cases hsq : IsSquare ((γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace ^ 2 -
      4 * (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det)
  ·
    obtain ⟨x, t₀, h01, h10, ht₀, hx⟩ := exists_conj_eq_diagonal K v γ₀ hγ₀ hsq

    let m : ENNReal := νT {g | g ∈ localCentralizer K v γ₀ ∧ x * g * x⁻¹ ∈ localIntegralSet K v}
    let B : GL (Fin 2) (v.adicCompletion K) → ℂ := fun γ =>
      ((m.toReal⁻¹ * (ν₀ (v.adicCompletionIntegers K : Set (v.adicCompletion K))).toReal⁻¹ *
        ‖1 - ((x * γ * x⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 /
            ((x * γ * x⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0‖⁻¹ : ℝ) : ℂ)
    refine ⟨0, B, ?_, ?_, ?_⟩
    ·
      intro f hf
      obtain ⟨W₃, hW₃, h3⟩ :=
        AutomorphicForm.exists_nhds_scalar_forall_isOrbitalIntegral_eq_mul_integral_unipotentGL2_conj_of_diagonal
          K v c ν₀ f hf
      refine ⟨(fun g => x * g * x⁻¹) ⁻¹' W₃, preimage_conj_mem_nhds K v x c hW₃, ?_⟩
      intro γ hγW hγT hγreg τ hτ hmap I hI
      obtain ⟨τ', hτ'map, hτ'H, hiff⟩ :=
        AutomorphicForm.exists_map_val_eq_map_conj_and_isOrbitalIntegral_conj_iff K v γ x τ
      have hI' := (hiff f I).2 hI
      have hγ'T : x * γ * x⁻¹ ∈ localCentralizer K v t₀ := by
        rw [← hx]; exact (mem_localCentralizer_conj_iff K v x γ₀ γ).2 hγT
      obtain ⟨h'01, h'10⟩ := diagonal_of_mem_localCentralizer K v t₀ (x * γ * x⁻¹) h01 h10 ht₀ hγ'T
      have hγ'reg : IsRegularSemisimple (x * γ * x⁻¹) := (isRegularSemisimple_conj_iff K v x γ).2 hγreg
      have h := h3 (x * γ * x⁻¹) hγW h'01 h'10 hγ'reg τ' (hτ'H hτ) I hI'

      letI := localCentralizerBorel K v (x * γ * x⁻¹)
      letI := localCentralizerBorel K v γ
      have hval' : Measurable (Subtype.val : localCentralizer K v (x * γ * x⁻¹) → GL (Fin 2) (v.adicCompletion K)) :=
        (measurableEmbedding_val K v (x * γ * x⁻¹)).measurable
      have hval : Measurable (Subtype.val : localCentralizer K v γ → GL (Fin 2) (v.adicCompletion K)) :=
        (measurableEmbedding_val K v γ).measurable
      have hKm : MeasurableSet (localIntegralSet K v) := (isOpen_localIntegralSet K v).measurableSet
      have hcx : Measurable fun g : GL (Fin 2) (v.adicCompletion K) => x * g * x⁻¹ := (continuous_conj K v x).measurable
      have hle := localCentralizer_le_of_split K v x t₀ γ₀ γ hx h01 h10 ht₀ hγT hγreg
      have hmass : τ' {t : localCentralizer K v (x * γ * x⁻¹) |
          (t : GL (Fin 2) (v.adicCompletion K)) ∈ localIntegralSet K v} = m := by
        have e1 : τ' {t : localCentralizer K v (x * γ * x⁻¹) | (t : GL (Fin 2) (v.adicCompletion K)) ∈ localIntegralSet K v} =
            Measure.map Subtype.val τ' (localIntegralSet K v) := by
          rw [Measure.map_apply hval' hKm]; rfl
        have hSm : MeasurableSet {g : GL (Fin 2) (v.adicCompletion K) |
            g ∈ localCentralizer K v γ₀ ∧ x * g * x⁻¹ ∈ localIntegralSet K v} :=
          ((isClosed_localCentralizer K v γ₀).measurableSet).inter (hcx hKm)
        rw [e1, hτ'map, Measure.map_apply hcx hKm, Measure.map_apply hval (hcx hKm)]
        show τ _ = νT {g : GL (Fin 2) (v.adicCompletion K) |
            g ∈ localCentralizer K v γ₀ ∧ x * g * x⁻¹ ∈ localIntegralSet K v}
        rw [← hmap, Measure.map_apply hval hSm]
        congr 1
        ext t
        simp only [Set.mem_preimage, Set.mem_setOf_eq]
        exact ⟨fun ht => ⟨hle t.2, ht⟩, fun ht => ht.2⟩
      rw [hmass] at h
      rw [h, zero_mul, zero_add]
    ·
      rintro - hguard
      refine ⟨rfl, Set.univ, Filter.univ_mem, ?_⟩
      intro γ _ hγT hγreg
      have hγ'T : x * γ * x⁻¹ ∈ localCentralizer K v t₀ := by
        rw [← hx]; exact (mem_localCentralizer_conj_iff K v x γ₀ γ).2 hγT
      obtain ⟨h'01, h'10⟩ := diagonal_of_mem_localCentralizer K v t₀ (x * γ * x⁻¹) h01 h10 ht₀ hγ'T
      have hγ'reg : IsRegularSemisimple (x * γ * x⁻¹) := (isRegularSemisimple_conj_iff K v x γ).2 hγreg
      have hab := apply_ne_of_diagonal_regular K v (x * γ * x⁻¹) h'01 h'10 hγ'reg
      have ha0 : ((x * γ * x⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 ≠ 0 := by
        intro h0
        apply Matrix.GeneralLinearGroup.det_ne_zero (x * γ * x⁻¹)
        rw [Matrix.det_fin_two, h'01, h0]; ring
      obtain ⟨hmpos, hmtop⟩ := measure_pos_lt_top_of_guard K v γ₀ x νT hguard
      have hm : m.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hmpos.ne', hmtop.ne⟩
      have hO : (ν₀ (v.adicCompletionIntegers K : Set (v.adicCompletion K))).toReal ≠ 0 := by
        refine ENNReal.toReal_ne_zero.2 ⟨?_, ?_⟩
        · exact ((AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 K) K).out v).measure_pos ν₀ ⟨0, zero_mem _⟩ |>.ne'
        · exact (isCompact_iff_compactSpace.2 (AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v)).measure_lt_top.ne
      have hn : ‖1 - ((x * γ * x⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 /
            ((x * γ * x⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0‖ ≠ 0 := by
        rw [norm_ne_zero_iff, sub_ne_zero, ne_eq, eq_div_iff ha0, one_mul]
        exact hab
      show ((m.toReal⁻¹ * (ν₀ (v.adicCompletionIntegers K : Set (v.adicCompletion K))).toReal⁻¹ *
        ‖1 - ((x * γ * x⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 /
            ((x * γ * x⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0‖⁻¹ : ℝ) : ℂ) ≠ 0
      exact Complex.ofReal_ne_zero.2 (mul_ne_zero (mul_ne_zero (inv_ne_zero hm) (inv_ne_zero hO)) (inv_ne_zero hn))
    ·
      intro hns _
      exfalso
      refine hns x⁻¹ ?_
      rw [inv_inv, hx]
      exact ⟨h01, h10⟩
  ·
    obtain ⟨x, d, hd, u, hu, hCent⟩ := exists_conj_elliptic K v γ₀ hγ₀ hsq

    let νT' : Measure (GL (Fin 2) (v.adicCompletion K)) := Measure.map (fun g => x * g * x⁻¹) νT
    obtain ⟨A, B', h1, h2⟩ :=
      AutomorphicForm.exists_forall_nhds_scalar_forall_isOrbitalIntegral_eq_add_mul_of_mem_localCentralizer_of_not_isSquare
        K v c d hd u hu ν₀ νT'
    refine ⟨A, fun γ => B' (x * γ * x⁻¹), ?_, ?_, ?_⟩
    ·
      intro f hf
      obtain ⟨W₁, hW₁, h1'⟩ := h1 f hf
      refine ⟨(fun g => x * g * x⁻¹) ⁻¹' W₁, preimage_conj_mem_nhds K v x c hW₁, ?_⟩
      intro γ hγW hγT hγreg τ hτ hmap I hI
      obtain ⟨τ', hτ'map, hτ'H, hiff⟩ :=
        AutomorphicForm.exists_map_val_eq_map_conj_and_isOrbitalIntegral_conj_iff K v γ x τ
      have hI' := (hiff f I).2 hI
      have hγ'T : x * γ * x⁻¹ ∈ localCentralizer K v u := by
        rw [← hCent]; exact (mem_localCentralizer_conj_iff K v x γ₀ γ).2 hγT
      have hγ'reg : IsRegularSemisimple (x * γ * x⁻¹) := (isRegularSemisimple_conj_iff K v x γ).2 hγreg
      have hmap' : @Measure.map _ _ (localCentralizerBorel K v (x * γ * x⁻¹)) (localGLBorel K v)
          Subtype.val τ' = νT' := by
        show _ = Measure.map (fun g => x * g * x⁻¹) νT
        rw [hτ'map, hmap]
      exact h1' (x * γ * x⁻¹) hγW hγ'T hγ'reg τ' (hτ'H hτ) hmap' I hI'
    ·
      rintro ⟨h01, h10⟩ -
      exact absurd (isSquare_disc_of_diagonal K v γ₀ h01 h10) hsq
    ·
      intro _ hguard
      apply h2
      exact guard_of_eq K v hCent νT' (isHaarMeasure_comap_val_map_conj K v x γ₀ νT hguard)

end S_AutomorphicForm_exists_germ_forall_isOrbitalIntegral_eq_add_nhds_scalar_of_isLocalTestFn
end P2MW
export P2MW.S_AutomorphicForm_exists_germ_forall_isOrbitalIntegral_eq_add_nhds_scalar_of_isLocalTestFn (solution)
