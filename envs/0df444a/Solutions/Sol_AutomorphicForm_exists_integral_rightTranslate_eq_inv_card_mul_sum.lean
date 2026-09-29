-- Prove2me | solution 1 for AutomorphicForm.exists_integral_rightTranslate_eq_inv_card_mul_sum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/a5662e67-f431-566b-9732-978514e6f078

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_MeasureTheory_exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_integral_rightTranslate_eq_inv_card_mul_sum

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm AutomorphicForm.CuspidalConstituent
open scoped BigOperators

theorem solution
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    [MeasurableSpace U] [BorelSpace U] (μ : Measure U) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, φ (x * u) = φ x)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ finiteAdelicGL2Subgroup F) :
    ∃ (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F),
      (∀ i, ∃ u ∈ U, ∃ u' ∈ U, reps i = u * g * u') ∧
      (∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ U, ∃ u' ∈ U, x = u * g * u') → ∃ i, ∃ u ∈ U, x = reps i * u) ∧
      (∀ i j, (reps i)⁻¹ * reps j ∈ U → i = j) ∧ 0 < n ∧
      ∀ x : AdelicGL2 (𝓞 F) F, ∫ u, φ (x * (u : AdelicGL2 (𝓞 F) F) * g) ∂μ = (n : ℂ)⁻¹ * ∑ i, φ (x * reps i) := by
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have hUf : U ≤ finiteAdelicGL2Subgroup F := hUO ▸ inf_le_right

  let Hs : Subgroup U :=
    { carrier := {v | g⁻¹ * (v : AdelicGL2 (𝓞 F) F) * g ∈ U}
      one_mem' := by simp [U.one_mem]
      mul_mem' := fun {a b} ha hb => by
        have : g⁻¹ * ((a : AdelicGL2 (𝓞 F) F) * b) * g =
            (g⁻¹ * a * g) * (g⁻¹ * b * g) := by group
        show g⁻¹ * ((a : AdelicGL2 (𝓞 F) F) * b) * g ∈ U
        rw [this]; exact U.mul_mem ha hb
      inv_mem' := fun {a} ha => by
        have : g⁻¹ * (a : AdelicGL2 (𝓞 F) F)⁻¹ * g = (g⁻¹ * a * g)⁻¹ := by group
        show g⁻¹ * (a : AdelicGL2 (𝓞 F) F)⁻¹ * g ∈ U
        rw [this]; exact U.inv_mem ha }
  have hmemHs : ∀ v : U, v ∈ Hs ↔ g⁻¹ * (v : AdelicGL2 (𝓞 F) F) * g ∈ U := fun v => Iff.rfl
  have hHo : IsOpen (Hs : Set U) := by
    have hc : Continuous fun v : U => g⁻¹ * (v : AdelicGL2 (𝓞 F) F) * g :=
      (continuous_const.mul continuous_subtype_val).mul continuous_const
    have hset : (Hs : Set U) = (fun v : U => g⁻¹ * (v : AdelicGL2 (𝓞 F) F) * g) ⁻¹' (O : Set _) := by
      ext v
      simp only [SetLike.mem_coe, Set.mem_preimage, hmemHs]
      have hmemU : ∀ y : AdelicGL2 (𝓞 F) F, y ∈ U ↔ y ∈ O ∧ y ∈ finiteAdelicGL2Subgroup F := fun y => by
        rw [hUO]; exact Subgroup.mem_inf
      rw [hmemU]
      refine ⟨fun hv => hv.1, fun hv => ⟨hv, ?_⟩⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) (hUf v.2)) hg
    rw [hset]; exact hO.preimage hc
  obtain ⟨n, r, -, hn0, hcov, hdist, hint⟩ :=
    MeasureTheory.exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup μ Hs hHo
  refine ⟨n, fun i => (r i : AdelicGL2 (𝓞 F) F) * g, ?_, ?_, ?_, hn0, ?_⟩
  · intro i
    exact ⟨r i, (r i).2, 1, U.one_mem, by rw [mul_one]⟩
  · rintro x ⟨u, hu, u', hu', rfl⟩
    obtain ⟨i, hi⟩ := hcov ⟨u, hu⟩
    rw [hmemHs] at hi
    refine ⟨i, (g⁻¹ * ((r i : AdelicGL2 (𝓞 F) F)⁻¹ * u) * g) * u', U.mul_mem hi hu', ?_⟩
    group
  · intro i j hij
    apply hdist i j
    rw [hmemHs]
    have : g⁻¹ * (((r i)⁻¹ * r j : U) : AdelicGL2 (𝓞 F) F) * g =
        ((r i : AdelicGL2 (𝓞 F) F) * g)⁻¹ * ((r j : AdelicGL2 (𝓞 F) F) * g) := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]; group
    rw [this]; exact hij
  · intro x
    have hinv : ∀ v : U, ∀ w ∈ Hs, φ (x * ((v * w : U) : AdelicGL2 (𝓞 F) F) * g) =
        φ (x * (v : AdelicGL2 (𝓞 F) F) * g) := by
      intro v w hw
      rw [hmemHs] at hw
      have : x * ((v * w : U) : AdelicGL2 (𝓞 F) F) * g =
          (x * (v : AdelicGL2 (𝓞 F) F) * g) * (g⁻¹ * (w : AdelicGL2 (𝓞 F) F) * g) := by
        simp only [Subgroup.coe_mul]; group
      rw [this, hφ _ _ hw]
    simpa [mul_assoc] using hint (fun v : U => φ (x * (v : AdelicGL2 (𝓞 F) F) * g)) hinv

end S_AutomorphicForm_exists_integral_rightTranslate_eq_inv_card_mul_sum
end P2MW
export P2MW.S_AutomorphicForm_exists_integral_rightTranslate_eq_inv_card_mul_sum (solution)
