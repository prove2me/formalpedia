-- Prove2me | solution 1 for AutomorphicForm.WhittakerModel.exists_forall_diagZ_mul_eq_zero_and_norm_le_mul_zpow_of_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/f044254b-6171-5b0d-9fe7-8c53c65f792c

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_polynomial_forall_diagZ_mul_eq_zero_and_sum_coeff_mul_eq_zero_of_admissible
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_WhittakerModel_exists_forall_diagZ_mul_eq_zero_and_norm_le_mul_zpow_of_admissible

set_option autoImplicit false
set_option linter.unusedVariables false

open IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal NumberField.AdelicLevel

namespace KirillovGaugeM47

theorem continuous_of_open_stabiliser {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (f : G → ℂ) (U : Subgroup G) (hU : IsOpen (U : Set G)) (hinv : ∀ k ∈ U, ∀ g : G, f (g * k) = f g) :
    Continuous f := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hopen : IsOpen ((fun u : G => g * u) '' (U : Set G)) := (isOpenMap_mul_left g) _ hU
  have hmem : g ∈ (fun u : G => g * u) '' (U : Set G) := ⟨1, U.one_mem, mul_one g⟩
  refine (continuousAt_const : ContinuousAt (fun _ : G => f g) g).congr ?_
  filter_upwards [hopen.mem_nhds hmem] with x hx
  obtain ⟨u, hu, rfl⟩ := hx
  exact (hinv u hu g).symm

theorem exists_bound_on_compact {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (f : G → ℂ) (hf : Continuous f) (S : Set G) (hS : IsCompact S) (g₀ : G) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k ∈ S, ‖f (g₀ * k)‖ ≤ B := by
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn
    ((hf.comp (continuous_const.mul continuous_id)).continuousOn : ContinuousOn (fun k => f (g₀ * k)) S)
  exact ⟨max B 0, le_max_right _ _, fun k hk => (hB k hk).trans (le_max_left _ _)⟩

theorem exists_bound_on_compact_range {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (f : G → ℂ) (hf : Continuous f) (S : Set G) (hS : IsCompact S) (g : ℕ → G) (M : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j : ℕ, j < M → ∀ k ∈ S, ‖f (g j * k)‖ ≤ B := by
  induction M with
  | zero => exact ⟨0, le_rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ M ih =>
    obtain ⟨B, hB0, hB⟩ := ih
    obtain ⟨B', hB0', hB'⟩ := exists_bound_on_compact f hf S hS (g M)
    refine ⟨max B B', le_max_of_le_left hB0, fun j hj k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact (hB j hj k hk).trans (le_max_left _ _)
    · exact (hB' k hk).trans (le_max_right _ _)

theorem norm_le_of_recurrence (a : ℤ → ℂ) (d M : ℕ) (c : ℕ → ℂ) (hc0 : c 0 ≠ 0) (B : ℝ) (hB0 : 0 ≤ B)
    (hneg : ∀ j : ℤ, j < 0 → a j = 0)
    (hinit : ∀ j : ℕ, j < M → ‖a j‖ ≤ B)
    (hrec : ∀ m : ℕ, M ≤ m → ∑ i ∈ Finset.range (d + 1), c i * a ((m : ℤ) - (i : ℤ)) = 0) :
    ∀ j : ℕ, ‖a j‖ ≤ B * ((∑ i ∈ Finset.range (d + 1), ‖c i‖) / ‖c 0‖) ^ j := by
  set S : ℝ := (∑ i ∈ Finset.range (d + 1), ‖c i‖) / ‖c 0‖ with hSdef
  have hc0pos : 0 < ‖c 0‖ := norm_pos_iff.2 hc0
  have hsumS : S * ‖c 0‖ = ∑ i ∈ Finset.range (d + 1), ‖c i‖ := by
    rw [hSdef, div_mul_cancel₀ _ hc0pos.ne']
  have hS1 : 1 ≤ S := by
    rw [hSdef, le_div_iff₀ hc0pos, one_mul]
    have h0mem : 0 ∈ Finset.range (d + 1) := Finset.mem_range.2 (Nat.succ_pos d)
    exact Finset.single_le_sum (f := fun i => ‖c i‖) (fun i _ => norm_nonneg (c i)) h0mem
  have hS0 : 0 ≤ S := zero_le_one.trans hS1
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hjM : j < M
    · calc ‖a j‖ ≤ B := hinit j hjM
        _ = B * 1 := (mul_one B).symm
        _ ≤ B * S ^ j := mul_le_mul_of_nonneg_left (one_le_pow₀ hS1) hB0
    · push_neg at hjM
      have hsum := hrec j hjM
      rw [Finset.sum_range_succ'] at hsum
      have hkey : c 0 * a (j : ℤ) = -∑ i ∈ Finset.range d, c (i + 1) * a ((j : ℤ) - ((i + 1 : ℕ) : ℤ)) := by
        have h0 : ((j : ℤ) - ((0 : ℕ) : ℤ)) = (j : ℤ) := by simp
        rw [h0] at hsum
        linear_combination hsum
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      ·
        have hz : ∀ i ∈ Finset.range d, c (i + 1) * a (((0 : ℕ) : ℤ) - ((i + 1 : ℕ) : ℤ)) = 0 := by
          intro i hi
          rw [hneg _ (by push_cast; omega), mul_zero]
        rw [Finset.sum_eq_zero hz, neg_zero] at hkey
        have : a ((0 : ℕ) : ℤ) = 0 := (mul_eq_zero.1 hkey).resolve_left hc0
        rw [this, norm_zero]
        positivity
      ·
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, (Nat.succ_pred_eq_of_pos hjpos).symm⟩
        have hterm : ∀ i ∈ Finset.range d,
            ‖c (i + 1) * a (((j' + 1 : ℕ) : ℤ) - ((i + 1 : ℕ) : ℤ))‖ ≤ ‖c (i + 1)‖ * (B * S ^ j') := by
          intro i hi
          rw [norm_mul]
          gcongr
          by_cases hlt : ((j' + 1 : ℕ) : ℤ) - ((i + 1 : ℕ) : ℤ) < 0
          · rw [hneg _ hlt, norm_zero]; positivity
          · push_neg at hlt
            obtain ⟨n, hn⟩ : ∃ n : ℕ, (((j' + 1 : ℕ) : ℤ) - ((i + 1 : ℕ) : ℤ)) = (n : ℤ) :=
              ⟨_, (Int.toNat_of_nonneg hlt).symm⟩
            have hnj : n ≤ j' := by omega
            have hnj' : n < j' + 1 := Nat.lt_succ_of_le hnj
            rw [hn]
            calc ‖a n‖ ≤ B * S ^ n := ih n hnj'
              _ ≤ B * S ^ j' := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hS1 hnj) hB0
        have hbound : ‖c 0‖ * ‖a ((j' + 1 : ℕ) : ℤ)‖ ≤ (∑ i ∈ Finset.range d, ‖c (i + 1)‖) * (B * S ^ j') := by
          rw [← norm_mul, hkey, norm_neg, Finset.sum_mul]
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
        have hle : (∑ i ∈ Finset.range d, ‖c (i + 1)‖) ≤ S * ‖c 0‖ := by
          rw [hsumS, Finset.sum_range_succ']
          linarith [norm_nonneg (c 0)]
        have h3 : ‖c 0‖ * ‖a ((j' + 1 : ℕ) : ℤ)‖ ≤ ‖c 0‖ * (B * S ^ (j' + 1)) := by
          calc ‖c 0‖ * ‖a ((j' + 1 : ℕ) : ℤ)‖ ≤ (∑ i ∈ Finset.range d, ‖c (i + 1)‖) * (B * S ^ j') := hbound
            _ ≤ (S * ‖c 0‖) * (B * S ^ j') := mul_le_mul_of_nonneg_right hle (by positivity)
            _ = ‖c 0‖ * (B * S ^ (j' + 1)) := by ring
        exact le_of_mul_le_mul_left h3 hc0pos

end KirillovGaugeM47

open KirillovGaugeM47 in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (V : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))
    (hstab : ∀ W ∈ V, ∀ h : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * h)) ∈ V)
    (hlaw : ∀ W ∈ V, ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * W g)
    (hsm : ∀ W ∈ V, ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g)
    (hadm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), ∀ W ∈ V, (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) →
        W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    ∀ W ∈ V, ∃ (N₁ : ℤ) (C R : ℝ), 0 ≤ C ∧ 0 < R ∧
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ m : ℤ,
        (m < N₁ → W (diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k) = 0) ∧
        ‖W (diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤ C * R ^ m := by
  intro W hW
  obtain ⟨N₁, D, M, hD0, hrec⟩ :=
    AutomorphicForm.WhittakerModel.exists_polynomial_forall_diagZ_mul_eq_zero_and_sum_coeff_mul_eq_zero_of_admissible
      p V hstab hlaw hsm hadm hπ hϖ W hW

  obtain ⟨U, hUo, hUinv⟩ := hsm W hW
  have hWc : Continuous W := continuous_of_open_stabiliser W U hUo hUinv
  have hKc : IsCompact (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p ⊤ top_ne_bot).1

  obtain ⟨B, hB0, hB⟩ := exists_bound_on_compact_range W hWc _ hKc
    (fun j : ℕ => diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ (N₁ + (j : ℤ))) M

  have hc0 : D.coeff 0 ≠ 0 := by rwa [Polynomial.coeff_zero_eq_eval_zero]
  have hc0pos : 0 < ‖D.coeff 0‖ := norm_pos_iff.2 hc0
  have hS1 : 1 ≤ (∑ i ∈ Finset.range (D.natDegree + 1), ‖D.coeff i‖) / ‖D.coeff 0‖ := by
    rw [le_div_iff₀ hc0pos, one_mul]
    exact Finset.single_le_sum (f := fun i => ‖D.coeff i‖) (fun i _ => norm_nonneg _)
      (Finset.mem_range.2 (Nat.succ_pos _))
  have hSpos : 0 < (∑ i ∈ Finset.range (D.natDegree + 1), ‖D.coeff i‖) / ‖D.coeff 0‖ := one_pos.trans_le hS1
  refine ⟨N₁, B * ((∑ i ∈ Finset.range (D.natDegree + 1), ‖D.coeff i‖) / ‖D.coeff 0‖) ^ (-N₁),
    (∑ i ∈ Finset.range (D.natDegree + 1), ‖D.coeff i‖) / ‖D.coeff 0‖, by positivity, hSpos, fun k hk m => ?_⟩
  obtain ⟨hvan, hrec'⟩ := hrec k hk
  refine ⟨fun hm => hvan m hm, ?_⟩

  have hgrow := norm_le_of_recurrence
    (fun j : ℤ => W (diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ (N₁ + j) * k))
    D.natDegree M (fun i => D.coeff i) hc0 B hB0
    (fun j hj => hvan (N₁ + j) (by omega))
    (fun j hj => hB j hj k hk)
    (fun m' hm' => by
      have h := hrec' m' hm'
      refine (Finset.sum_congr rfl fun i _ => ?_).trans h
      show D.coeff i * W (diagZ _ hπ (N₁ + ((m' : ℤ) - (i : ℤ))) * k) = D.coeff i * W (diagZ _ hπ (N₁ + m' - i) * k)
      rw [← add_sub_assoc])
  by_cases hm : m < N₁
  · rw [hvan m hm, norm_zero]; positivity
  · push_neg at hm
    obtain ⟨j, hj⟩ : ∃ j : ℕ, m = N₁ + (j : ℤ) := ⟨(m - N₁).toNat, by omega⟩
    subst hj
    have hz : B * ((∑ i ∈ Finset.range (D.natDegree + 1), ‖D.coeff i‖) / ‖D.coeff 0‖) ^ (-N₁) *
        ((∑ i ∈ Finset.range (D.natDegree + 1), ‖D.coeff i‖) / ‖D.coeff 0‖) ^ (N₁ + (j : ℤ)) =
        B * ((∑ i ∈ Finset.range (D.natDegree + 1), ‖D.coeff i‖) / ‖D.coeff 0‖) ^ j := by
      rw [zpow_add₀ hSpos.ne', zpow_neg, zpow_natCast]
      field_simp
    rw [hz]
    exact hgrow j

end S_AutomorphicForm_WhittakerModel_exists_forall_diagZ_mul_eq_zero_and_norm_le_mul_zpow_of_admissible
end P2MW
export P2MW.S_AutomorphicForm_WhittakerModel_exists_forall_diagZ_mul_eq_zero_and_norm_le_mul_zpow_of_admissible (solution)
