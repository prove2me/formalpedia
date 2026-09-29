-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_apply_eq_ideleNorm_rpow_of_continuous_of_trivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/0ec685fb-f808-5031-9cf0-b40ae09c20e8

import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_apply_eq_ideleNorm_rpow_of_continuous_of_trivial
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open NumberField NumberField.TateGlobal
open scoped NNReal

noncomputable section

namespace ModulusProof

variable (K : Type) [Field K] [NumberField K]

def posUnit (t : ℝ) (ht : 0 < t) : ℝ≥0ˣ :=
  Units.mk0 ⟨t, ht.le⟩ (by
    intro h
    have h' := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
    simp only [NNReal.coe_mk, NNReal.coe_zero] at h'
    exact ht.ne' h')

theorem posUnit_val (t : ℝ) (ht : 0 < t) : (((posUnit t ht : ℝ≥0ˣ) : ℝ≥0) : ℝ) = t := rfl

theorem ideleNorm_one : ideleNorm K (1 : (AdeleRing (𝓞 K) K)ˣ) = 1 := by
  have h := ideleNorm_mul (F := K) 1 1
  rw [one_mul] at h
  have hp := ideleNorm_pos (F := K) (1 : (AdeleRing (𝓞 K) K)ˣ)
  nlinarith [h, hp]

theorem ideleNorm_inv (x : (AdeleRing (𝓞 K) K)ˣ) : ideleNorm K x⁻¹ = (ideleNorm K x)⁻¹ := by
  have h := ideleNorm_mul (F := K) x x⁻¹
  rw [mul_inv_cancel, ideleNorm_one] at h
  have hp := ideleNorm_pos (F := K) x
  field_simp
  linarith [h]

end ModulusProof

open ModulusProof in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1) :
    ∃ w : ℝ, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) := by
  classical

  set A : (AdeleRing (𝓞 K) K)ˣ → ℝ := fun z => ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ with hA
  have hA_mul : ∀ x y, A (x * y) = A x * A y := by
    intro x y
    have : (⟨x * y, Subgroup.mem_top (x * y)⟩ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ)) =
        ⟨x, Subgroup.mem_top x⟩ * ⟨y, Subgroup.mem_top y⟩ := rfl
    simp only [hA, this, map_mul, Units.val_mul, norm_mul]
  have hA_pos : ∀ x, 0 < A x := fun x => by
    simp only [hA]; exact norm_pos_iff.mpr (Units.ne_zero _)
  have hA_one : A 1 = 1 := by
    have : (⟨(1 : (AdeleRing (𝓞 K) K)ˣ), Subgroup.mem_top 1⟩ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ)) = 1 := rfl
    simp only [hA, this, map_one, Units.val_one, norm_one]
  have hA_inv : ∀ x, A x⁻¹ = (A x)⁻¹ := fun x => by
    have h := hA_mul x x⁻¹
    rw [mul_inv_cancel, hA_one] at h
    have hp := hA_pos x
    field_simp
    linarith [h]
  have hA_pow : ∀ x (n : ℕ), A (x ^ n) = A x ^ n := by
    intro x n; induction n with
    | zero => simp [hA_one]
    | succ n ih => rw [pow_succ, hA_mul, ih, pow_succ]
  have hA_cont : Continuous A := continuous_norm.comp hξc
  have hA_K : ∀ η : Kˣ, A (Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom η) = 1 := by
    intro η
    have h := hξt (Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom η) ⟨η, rfl⟩
    simp only [hA, h, Units.val_one, norm_one]

  obtain ⟨Kc, hKc, hKc1, hfund⟩ :=
    NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul K
  obtain ⟨C, hC⟩ := (hKc.image hA_cont).bddAbove
  have hbound : ∀ x ∈ normOneIdeles K, A x ≤ max C 1 := by
    intro x hx
    obtain ⟨η, κ, hκ, rfl⟩ := hfund x hx
    rw [hA_mul, hA_K, one_mul]
    exact (hC ⟨κ, hκ, rfl⟩).trans (le_max_left _ _)
  have hle1 : ∀ x ∈ normOneIdeles K, A x ≤ 1 := by
    intro x hx
    by_contra hgt
    push_neg at hgt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (max C 1) hgt
    have := hbound (x ^ n) (Subgroup.pow_mem _ hx n)
    rw [hA_pow] at this
    exact absurd (lt_of_lt_of_le hn this) (lt_irrefl _)
  have hone : ∀ x ∈ normOneIdeles K, A x = 1 := by
    intro x hx
    refine le_antisymm (hle1 x hx) ?_
    have h := hle1 x⁻¹ (Subgroup.inv_mem _ hx)
    rw [hA_inv] at h
    exact (inv_le_one₀ (hA_pos x)).mp h

  obtain ⟨s, hs, hsn, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq K
  have hfac : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      A z = A (s (posUnit (ideleNorm K z) (ideleNorm_pos z))) := by
    intro z
    set r := posUnit (ideleNorm K z) (ideleNorm_pos z) with hr
    have hmem : z * (s r)⁻¹ ∈ normOneIdeles K := by
      rw [mem_normOneIdeles_iff, ideleNorm_mul, ModulusProof.ideleNorm_inv, hsn r, hr, posUnit_val]
      exact mul_inv_cancel₀ (ideleNorm_pos z).ne'
    have h := hone _ hmem
    rw [hA_mul, hA_inv] at h
    have hp := hA_pos (s r)
    field_simp at h
    linarith [h]

  set H : ℝ → ℝ := fun x => Real.log (A (s (posUnit (Real.exp x) (Real.exp_pos x)))) with hH
  have hexp_mul : ∀ x y, posUnit (Real.exp (x + y)) (Real.exp_pos (x + y)) =
      posUnit (Real.exp x) (Real.exp_pos x) * posUnit (Real.exp y) (Real.exp_pos y) := by
    intro x y; apply Units.ext; apply Subtype.ext
    show Real.exp (x + y) = Real.exp x * Real.exp y
    exact Real.exp_add x y
  have hH_add : ∀ x y, H (x + y) = H x + H y := by
    intro x y
    simp only [hH, hexp_mul, map_mul, hA_mul]
    rw [Real.log_mul (hA_pos _).ne' (hA_pos _).ne']
  have hcont_pos : Continuous fun x : ℝ => posUnit (Real.exp x) (Real.exp_pos x) := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact (Real.continuous_exp.subtype_mk _ : Continuous fun x : ℝ => (⟨Real.exp x, (Real.exp_pos x).le⟩ : ℝ≥0))
    · have : (fun x : ℝ => ((posUnit (Real.exp x) (Real.exp_pos x))⁻¹ : ℝ≥0ˣ).val) =
          fun x : ℝ => (⟨Real.exp (-x), (Real.exp_pos (-x)).le⟩ : ℝ≥0) := by
        funext x
        rw [Units.val_inv_eq_inv_val]
        apply Subtype.ext
        show (Real.exp x)⁻¹ = Real.exp (-x)
        rw [Real.exp_neg]
      rw [this]
      exact (Real.continuous_exp.comp continuous_neg).subtype_mk _
  have hH_cont : Continuous H :=
    (hA_cont.comp (hs.comp hcont_pos)).log fun x => (hA_pos _).ne'
  have hH0 : H 0 = 0 := by
    have h := hH_add 0 0; rw [add_zero] at h; linarith
  let Hhom : ℝ →+ ℝ := { toFun := H, map_zero' := hH0, map_add' := hH_add }
  have hlin : ∀ x : ℝ, H x = x * H 1 := by
    intro x
    have h := map_real_smul Hhom hH_cont x 1
    simp only [smul_eq_mul, mul_one] at h
    exact h

  refine ⟨H 1, fun z => ?_⟩
  have hz := hfac z
  have ht : 0 < ideleNorm K z := ideleNorm_pos z
  have hunit : posUnit (ideleNorm K z) ht = posUnit (Real.exp (Real.log (ideleNorm K z))) (Real.exp_pos _) := by
    apply Units.ext; apply Subtype.ext
    show ideleNorm K z = Real.exp (Real.log (ideleNorm K z))
    rw [Real.exp_log ht]
  have hHz : H (Real.log (ideleNorm K z)) = Real.log (A z) := by
    simp only [hH]; rw [← hunit, ← hz]
  show A z = ideleNorm K z ^ H 1
  rw [Real.rpow_def_of_pos ht, ← hlin, hHz, Real.exp_log (hA_pos z)]

end
end S_AutomorphicForm_exists_forall_norm_apply_eq_ideleNorm_rpow_of_continuous_of_trivial
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_apply_eq_ideleNorm_rpow_of_continuous_of_trivial (solution)
