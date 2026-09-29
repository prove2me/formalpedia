-- Prove2me | solution 1 for AutomorphicForm.exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/859e73f1-0b71-56fa-aee2-d41153053b23

import Definitions.Def_NumberField_AdelicTraceFin
import Theorems.Thm_NumberField_AdelicFourier_exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar
import Theorems.Thm_NumberField_StandardAddChar_stdAddChar_apply_mk_zero_eq_fourierChar_trace
import Theorems.Thm_NumberField_AdelicBox_integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar

open NumberField

namespace GlobalAddCharFrequency

open IsDedekindDomain AutomorphicForm

variable {F : Type} [Field F] [NumberField F]

private theorem forall_eq_of_forall_mk_zero_eq
    (f : AdeleRing (𝓞 F) F → ℂ) (η : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hfc : Continuous f) (hηc : Continuous η)
    (hfmul : ∀ y z : AdeleRing (𝓞 F) F, f (y + z) = f y * f z)
    (hfF : ∀ x : F, f (algebraMap F (AdeleRing (𝓞 F) F) x) = 1)
    (hηF : ∀ x : F, η (algebraMap F (AdeleRing (𝓞 F) F) x) = 1)
    (harch : ∀ u : InfiniteAdeleRing F,
      f ((u, 0) : AdeleRing (𝓞 F) F) = η ((u, 0) : AdeleRing (𝓞 F) F)) :
    ∀ y : AdeleRing (𝓞 F) F, f y = η y := by
  have hη0 : ∀ z : AdeleRing (𝓞 F) F, η z ≠ 0 := by
    intro z
    have h1 : η z * η (-z) = 1 := by
      rw [← AddChar.map_add_eq_mul η z (-z), add_neg_cancel, AddChar.map_zero_eq_one]
    exact left_ne_zero_of_mul_eq_one h1
  have hadd : ∀ y z t : AdeleRing (𝓞 F) F, t = y + z → f y = η y → f z = η z → f t = η t := by
    intro y z t ht hy hz
    subst ht
    rw [hfmul, AddChar.map_add_eq_mul, hy, hz]
  have hcancel : ∀ y z t : AdeleRing (𝓞 F) F, t = y + z → f t = η t → f z = η z → f y = η y := by
    intro y z t ht hyt hz
    subst ht
    rw [hfmul, AddChar.map_add_eq_mul, hz] at hyt
    exact mul_right_cancel₀ (hη0 z) hyt
  have hfin_principal : ∀ x : F,
      f ((0, algebraMap F (FiniteAdeleRing (𝓞 F) F) x) : AdeleRing (𝓞 F) F)
        = η ((0, algebraMap F (FiniteAdeleRing (𝓞 F) F) x) : AdeleRing (𝓞 F) F) := by
    intro x
    refine hcancel _ ((algebraMap F (InfiniteAdeleRing F) x, 0) : AdeleRing (𝓞 F) F)
      (algebraMap F (AdeleRing (𝓞 F) F) x) ?_ ((hfF x).trans (hηF x).symm) (harch _)
    exact Prod.ext (zero_add _).symm (add_zero _).symm
  have hclosed : IsClosed {w : FiniteAdeleRing (𝓞 F) F |
      f ((0, w) : AdeleRing (𝓞 F) F) = η ((0, w) : AdeleRing (𝓞 F) F)} := by
    have hι : Continuous fun w : FiniteAdeleRing (𝓞 F) F => ((0, w) : AdeleRing (𝓞 F) F) :=
      continuous_const.prodMk continuous_id
    exact isClosed_eq (hfc.comp hι) (hηc.comp hι)
  have hrange : Set.range (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F)) ⊆
      {w : FiniteAdeleRing (𝓞 F) F |
        f ((0, w) : AdeleRing (𝓞 F) F) = η ((0, w) : AdeleRing (𝓞 F) F)} := by
    rintro _ ⟨o, rfl⟩
    show f ((0, algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) o) : AdeleRing (𝓞 F) F)
      = η ((0, algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) o) : AdeleRing (𝓞 F) F)
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F) o]
    exact hfin_principal _
  have hint : ∀ w ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F,
      f ((0, w) : AdeleRing (𝓞 F) F) = η ((0, w) : AdeleRing (𝓞 F) F) := by
    intro w hw
    exact closure_minimal hrange hclosed
      (AdelicBox.integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers F hw)
  have hfin : ∀ w : FiniteAdeleRing (𝓞 F) F,
      f ((0, w) : AdeleRing (𝓞 F) F) = η ((0, w) : AdeleRing (𝓞 F) F) := by
    intro w
    obtain ⟨k, hk⟩ := AdelicBox.exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 F) F w
    refine hcancel _ ((0, algebraMap F (FiniteAdeleRing (𝓞 F) F) k) : AdeleRing (𝓞 F) F)
      ((0, algebraMap F (FiniteAdeleRing (𝓞 F) F) k + w) : AdeleRing (𝓞 F) F)
      ?_ (hint _ hk) (hfin_principal k)
    exact Prod.ext (add_zero (0 : InfiniteAdeleRing F)).symm (add_comm _ _)
  intro y
  refine hadd ((0, y.2) : AdeleRing (𝓞 F) F) ((y.1, 0) : AdeleRing (𝓞 F) F) y ?_ (hfin y.2) (harch y.1)
  exact Prod.ext (zero_add y.1).symm (add_zero y.2).symm

private theorem forall_apply_mul_eq_stdAddChar {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}
    (hψ : IsGlobalAddChar F ψ) (a : F)
    (harch : ∀ u : InfiniteAdeleRing F,
      ψ ((algebraMap F (InfiniteAdeleRing F) a * u, 0) : AdeleRing (𝓞 F) F)
        = StandardAddChar.stdAddChar F ((u, 0) : AdeleRing (𝓞 F) F)) :
    ∀ y : AdeleRing (𝓞 F) F,
      ψ (algebraMap F (AdeleRing (𝓞 F) F) a * y) = StandardAddChar.stdAddChar F y := by
  have hstd : IsGlobalAddChar F (StandardAddChar.stdAddChar F) :=
    (StandardAddChar.adelicTraceData F).isGlobalAddChar_psiK
  refine forall_eq_of_forall_mk_zero_eq (fun y => ψ (algebraMap F (AdeleRing (𝓞 F) F) a * y))
    (StandardAddChar.stdAddChar F) ?_ hstd.continuous ?_ ?_ hstd.principalInvariant ?_
  · have hc : Continuous ψ := hψ.continuous
    fun_prop
  · intro y z
    show ψ (algebraMap F (AdeleRing (𝓞 F) F) a * (y + z))
      = ψ (algebraMap F (AdeleRing (𝓞 F) F) a * y) * ψ (algebraMap F (AdeleRing (𝓞 F) F) a * z)
    rw [mul_add, AddChar.map_add_eq_mul]
  · intro x
    show ψ (algebraMap F (AdeleRing (𝓞 F) F) a * algebraMap F (AdeleRing (𝓞 F) F) x) = 1
    rw [← map_mul (algebraMap F (AdeleRing (𝓞 F) F)) a x]
    exact hψ.principalInvariant (a * x)
  · intro u
    refine (congrArg ψ ?_).trans (harch u)
    exact Prod.ext rfl (mul_zero _)

end GlobalAddCharFrequency

open GlobalAddCharFrequency AutomorphicForm in
theorem solution
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ) :
    ∃ a : F, a ≠ 0 ∧
      (∀ x : AdeleRing (𝓞 F) F,
        ψ x = StandardAddChar.stdAddChar F (algebraMap F (AdeleRing (𝓞 F) F) a * x)) := by
  obtain ⟨a, ha, harch⟩ :=
    NumberField.AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar F hψ
  have hkey := forall_apply_mul_eq_stdAddChar hψ a fun u =>
    (harch u).trans (NumberField.StandardAddChar.stdAddChar_apply_mk_zero_eq_fourierChar_trace F u).symm
  refine ⟨a⁻¹, inv_ne_zero ha, fun x => ?_⟩
  have h := hkey (algebraMap F (AdeleRing (𝓞 F) F) a⁻¹ * x)
  rw [← mul_assoc, ← map_mul (algebraMap F (AdeleRing (𝓞 F) F)) a a⁻¹, mul_inv_cancel₀ ha, map_one,
    one_mul] at h
  exact h

end S_AutomorphicForm_exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar
end P2MW
export P2MW.S_AutomorphicForm_exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar (solution)
