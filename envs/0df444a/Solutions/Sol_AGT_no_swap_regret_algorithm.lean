-- Prove2me | solution 1 for AGT.no_swap_regret_algorithm
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-12T19:48:17.701481+00:00
-- url     : https://prove2.me/submissions/d33905bd-dc64-4bbb-ba31-d140a804cb17

import Theorems.Thm_AGT_polynomial_weights_bound
import Theorems.Thm_AGT_external_to_swap_reduction
import Definitions.Def_agt_regret
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace AGT

open Finset

/-! ### The Polynomial Weights algorithm as an `OnlineAlgorithm` -/

/-- Clamp a loss vector coordinatewise into `[0,1]`. -/
private def clampLoss {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => max 0 (min 1 (x i))

private lemma clampLoss_mem {m : ℕ} (x : Fin m → ℝ) (i : Fin m) :
    clampLoss x i ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

private lemma clampLoss_eq {m : ℕ} (x : Fin m → ℝ) (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    clampLoss x = x := by
  funext i
  have h := hx i
  simp only [clampLoss]
  rw [min_eq_right h.2, max_eq_right h.1]

/-- The `[0,1]`-valued loss sequence reconstructed from an observed history. -/
private def pwHist {m : ℕ} (h : List (Fin m → ℝ)) : ℕ → Fin m → ℝ :=
  fun t => clampLoss (h.getD t (fun _ => 0))

private lemma pwHist_mem {m : ℕ} (h : List (Fin m → ℝ)) (t : ℕ) (i : Fin m) :
    pwHist h t i ∈ Set.Icc (0 : ℝ) 1 := clampLoss_mem _ _

/-- The Polynomial Weights algorithm with learning rate `η`, packaged as an
`OnlineAlgorithm`. -/
private noncomputable def pwAlg (η : ℝ) (m : ℕ) : OnlineAlgorithm m :=
  fun h => pwProb η (pwHist h) h.length

private lemma pwWeights_congr {m : ℕ} (η : ℝ) (ℓ₁ ℓ₂ : ℕ → Fin m → ℝ) :
    ∀ t : ℕ, (∀ s, s < t → ℓ₁ s = ℓ₂ s) → pwWeights η ℓ₁ t = pwWeights η ℓ₂ t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
      intro h
      have h1 : pwWeights η ℓ₁ t = pwWeights η ℓ₂ t := ih fun s hs => h s (by omega)
      have h2 : ℓ₁ t = ℓ₂ t := h t (by omega)
      funext i
      simp [pwWeights, h1, h2]

private lemma pwWeights_pos {m : ℕ} {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (ℓ : ℕ → Fin m → ℝ) (hℓ : ∀ t i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) :
    ∀ t i, 0 < pwWeights η ℓ t i := by
  intro t
  induction t with
  | zero => intro i; simp [pwWeights]
  | succ t ih =>
      intro i
      have hpos := ih i
      have hb := hℓ t i
      have hfac : 0 < 1 - η * ℓ t i := by nlinarith [hb.1, hb.2]
      simpa [pwWeights] using mul_pos hpos hfac

private lemma pwProb_lottery {m : ℕ} {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (ℓ : ℕ → Fin (m + 1) → ℝ) (hℓ : ∀ t i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) :
    IsLottery (pwProb η ℓ t) := by
  have hpos := pwWeights_pos hη0 hη ℓ hℓ t
  have hsum : 0 < ∑ j, pwWeights η ℓ t j :=
    Finset.sum_pos (fun j _ => hpos j) ⟨0, Finset.mem_univ 0⟩
  refine ⟨fun i => le_of_lt (div_pos (hpos i) hsum), ?_⟩
  have : (∑ i, pwProb η ℓ t i) = (∑ i, pwWeights η ℓ t i) / (∑ j, pwWeights η ℓ t j) := by
    simp only [pwProb, div_eq_mul_inv, ← Finset.sum_mul]
  rw [this]
  exact div_self (ne_of_gt hsum)

private lemma pwAlg_lottery {m : ℕ} {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (h : List (Fin (m + 1) → ℝ)) : IsLottery (pwAlg η (m + 1) h) :=
  pwProb_lottery hη0 hη (pwHist h) (fun t i => pwHist_mem h t i) h.length

private lemma algPlay_pwAlg {m : ℕ} (η : ℝ) (ℓ : ℕ → Fin m → ℝ)
    (hℓ : ∀ t i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) :
    algPlay (pwAlg η m) ℓ t = pwProb η ℓ t := by
  have hlen : ((List.range t).map ℓ).length = t := by simp
  have hget : ∀ s, s < t → pwHist ((List.range t).map ℓ) s = ℓ s := by
    intro s hs
    have hs' : s < ((List.range t).map ℓ).length := by omega
    have hval : ((List.range t).map ℓ).getD s (fun _ => 0) = ℓ s := by
      rw [List.getD_eq_getElem?_getD]
      rw [List.getElem?_map, List.getElem?_range (by omega)]
      simp
    simp only [pwHist, hval]
    exact clampLoss_eq _ (fun i => hℓ s i)
  have hw : pwWeights η (pwHist ((List.range t).map ℓ)) t = pwWeights η ℓ t :=
    pwWeights_congr η _ _ t hget
  simp only [algPlay, pwAlg, hlen]
  funext i
  simp only [pwProb, hw]

/-! ### The trivial bound `L_A ≤ T` -/

private lemma algLoss_le_horizon {m : ℕ} (A : OnlineAlgorithm m) (hA : ∀ h, IsLottery (A h))
    (ℓ : ℕ → Fin m → ℝ) (hℓ : ∀ t i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    algLoss A ℓ T ≤ (T : ℝ) := by
  have hstep : ∀ t ∈ Finset.range T, (∑ i, algPlay A ℓ t i * ℓ t i) ≤ (1 : ℝ) := by
    intro t _
    obtain ⟨hnn, hsum⟩ := hA ((List.range t).map ℓ)
    have : (∑ i, algPlay A ℓ t i * ℓ t i) ≤ ∑ i, algPlay A ℓ t i * 1 := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hb := hℓ t i
      have hp : 0 ≤ algPlay A ℓ t i := hnn i
      nlinarith [hb.2]
    simpa [algPlay, hsum] using this
  calc algLoss A ℓ T = ∑ t ∈ Finset.range T, ∑ i, algPlay A ℓ t i * ℓ t i := rfl
    _ ≤ ∑ _t ∈ Finset.range T, (1 : ℝ) := Finset.sum_le_sum hstep
    _ = (T : ℝ) := by simp

/-! ### Polynomial Weights tuned at `η = min {√(ln N / T), 1/2}` -/

/-- Tuned Polynomial Weights has external regret at most `2√(T ln N)` at horizon `T`. -/
private lemma pw_external {n : ℕ} (T : ℕ) (hT : 0 < T) (hL : 0 < Real.log ((n : ℝ) + 1)) :
    ∃ A : OnlineAlgorithm (n + 1), (∀ h, IsLottery (A h)) ∧
      ∀ ℓ : ℕ → Fin (n + 1) → ℝ, (∀ t i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) →
        ∀ k, algLoss A ℓ T ≤ actionLoss ℓ k T + 2 * Real.sqrt ((T : ℝ) * Real.log ((n : ℝ) + 1)) := by
  set L : ℝ := Real.log ((n : ℝ) + 1) with hLdef
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hs0 : 0 < Real.sqrt (L / T) := Real.sqrt_pos.mpr (div_pos hL hTR)
  set s : ℝ := Real.sqrt (L / T) with hsdef
  have hs2 : s ^ 2 = L / T := Real.sq_sqrt (le_of_lt (div_pos hL hTR))
  have hLs : L = s ^ 2 * T := by
    rw [hs2]; field_simp
  set η : ℝ := min s (1 / 2) with hηdef
  have hη0 : 0 < η := lt_min hs0 (by norm_num)
  have hη : η ≤ 1 / 2 := min_le_right _ _
  have hTLnn : (0 : ℝ) ≤ (T : ℝ) * L := le_of_lt (mul_pos hTR hL)
  refine ⟨pwAlg η (n + 1), fun h => pwAlg_lottery hη0 hη h, ?_⟩
  intro ℓ hℓ k
  have hplay : algLoss (pwAlg η (n + 1)) ℓ T
      = ∑ t ∈ Finset.range T, ∑ i, pwProb η ℓ t i * ℓ t i := by
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [algPlay_pwAlg η ℓ hℓ t]
  have hactionLoss_nonneg : 0 ≤ actionLoss ℓ k T :=
    Finset.sum_nonneg fun t _ => (hℓ t k).1
  by_cases hcase : s ≤ 1 / 2
  · -- tuned regime: `η = s` and `η T + L / η = 2√(T L)`
    have hηeq : η = s := min_eq_left hcase
    have hbound := polynomial_weights_bound η hη0 hη ℓ hℓ T k
    have hQ : ∑ t ∈ Finset.range T, (ℓ t k) ^ 2 ≤ (T : ℝ) := by
      calc ∑ t ∈ Finset.range T, (ℓ t k) ^ 2 ≤ ∑ _t ∈ Finset.range T, (1 : ℝ) := by
            refine Finset.sum_le_sum fun t _ => ?_
            have h := hℓ t k
            nlinarith [h.1, h.2]
        _ = (T : ℝ) := by simp
    have hkey : η * (T : ℝ) + L / η = 2 * Real.sqrt ((T : ℝ) * L) := by
      have hsqeq : (T : ℝ) * L = (s * T) ^ 2 := by rw [hLs]; ring
      have hsTnn : 0 ≤ s * (T : ℝ) := le_of_lt (mul_pos hs0 hTR)
      rw [hsqeq, Real.sqrt_sq hsTnn, hηeq, hLs]
      field_simp
      ring
    have hQterm : η * ∑ t ∈ Finset.range T, (ℓ t k) ^ 2 ≤ η * (T : ℝ) :=
      mul_le_mul_of_nonneg_left hQ (le_of_lt hη0)
    rw [hplay]
    calc ∑ t ∈ Finset.range T, ∑ i, pwProb η ℓ t i * ℓ t i
        ≤ actionLoss ℓ k T + η * ∑ t ∈ Finset.range T, (ℓ t k) ^ 2 + L / η := hbound
      _ ≤ actionLoss ℓ k T + η * (T : ℝ) + L / η := by linarith
      _ = actionLoss ℓ k T + 2 * Real.sqrt ((T : ℝ) * L) := by rw [← hkey]; ring
  · -- small-horizon regime: the trivial bound `L_A ≤ T ≤ 2√(T L)` suffices
    have hsgt : (1 : ℝ) / 2 < s := not_le.mp hcase
    have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTR
    have hL4 : (T : ℝ) / 4 < L := by
      have h1 : (1 : ℝ) / 4 < s ^ 2 := by nlinarith
      rw [hs2] at h1
      have h3 : (1 : ℝ) / 4 * T < L / (T : ℝ) * T := mul_lt_mul_of_pos_right h1 hTR
      have h4 : L / (T : ℝ) * T = L := by field_simp
      rw [h4] at h3
      linarith
    have hr := Real.sq_sqrt hTLnn
    have hrnn : 0 ≤ Real.sqrt ((T : ℝ) * L) := Real.sqrt_nonneg _
    have hTle : (T : ℝ) ≤ 2 * Real.sqrt ((T : ℝ) * L) := by
      nlinarith [hr, hrnn, hTR, hL4]
    have htriv : algLoss (pwAlg η (n + 1)) ℓ T ≤ (T : ℝ) :=
      algLoss_le_horizon _ (fun h => pwAlg_lottery hη0 hη h) ℓ hℓ T
    linarith

end AGT

/-! ### The capstone -/

open AGT

theorem solution {n : ℕ} (T : ℕ) :
    ∃ H : OnlineAlgorithm (n + 1), (∀ h, IsLottery (H h)) ∧
      ∀ ℓ : ℕ → Fin (n + 1) → ℝ, (∀ t i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) →
        ∀ F : Fin (n + 1) → Fin (n + 1),
          algLoss H ℓ T ≤ swapLoss H ℓ F T +
            2 * (n + 1) * Real.sqrt (T * Real.log (n + 1)) := by
  have hhalf0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hhalf : (1 : ℝ) / 2 ≤ 1 / 2 := le_refl _
  rcases Nat.eq_zero_or_pos T with hT | hT
  · -- no rounds: both losses vanish
    subst hT
    refine ⟨pwAlg (1 / 2) (n + 1), fun h => pwAlg_lottery hhalf0 hhalf h, ?_⟩
    intro ℓ hℓ F
    have hnn : 0 ≤ 2 * ((n : ℝ) + 1) * Real.sqrt ((0 : ℝ) * Real.log ((n : ℝ) + 1)) := by
      positivity
    simp only [algLoss, swapLoss, Finset.range_zero, Finset.sum_empty, Nat.cast_zero]
    linarith
  · by_cases hn : n = 0
    · -- a single action: every modification rule is the identity
      subst hn
      refine ⟨pwAlg (1 / 2) 1, fun h => pwAlg_lottery hhalf0 hhalf h, ?_⟩
      intro ℓ hℓ F
      have hF : ∀ i : Fin (0 + 1), F i = i := by
        intro i
        have h1 := (F i).isLt
        have h2 := i.isLt
        exact Fin.ext (by omega)
      have heq : swapLoss (pwAlg (1 / 2) 1) ℓ F T = algLoss (pwAlg (1 / 2) 1) ℓ T := by
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => ?_
        rw [hF i]
      rw [heq]
      have : Real.log (((0 : ℕ) : ℝ) + 1) = 0 := by norm_num
      rw [this]
      simp
    · -- the main case
      have hnpos : 0 < (n : ℝ) := by
        have : 0 < n := Nat.pos_of_ne_zero hn
        exact_mod_cast this
      have hL : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by linarith)
      obtain ⟨A, hAdist, hA⟩ := pw_external T hT hL
      obtain ⟨H, hHdist, hH⟩ :=
        external_to_swap_reduction T (2 * Real.sqrt ((T : ℝ) * Real.log ((n : ℝ) + 1)))
          A hAdist hA
      refine ⟨H, hHdist, ?_⟩
      intro ℓ hℓ F
      have h := hH ℓ hℓ F
      have hring : ((n : ℝ) + 1) * (2 * Real.sqrt ((T : ℝ) * Real.log ((n : ℝ) + 1)))
          = 2 * ((n : ℝ) + 1) * Real.sqrt ((T : ℝ) * Real.log ((n : ℝ) + 1)) := by ring
      linarith [h, hring.ge, hring.le]
