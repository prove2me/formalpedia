-- Prove2me | Definitions.Def_friedmann_parity_lib_transport
-- name    : friedmann_parity_lib_transport
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-08T03:40:05.594051+00:00
-- url     : https://prove2.me/theorems/8a33c07a-fe0c-4d5e-b50c-9ad308b99f3d
-- title:
--   Friedmann parity games: parity order versus discounted order on sink games (proved library)
-- statement:
--   A sorry-free library module that extends `friedmann_parity_lib_valuation` and uses the payoff model `friedmann_payoff`. Let $G$ be a sink game: priority $1$ at the sink $z$, priorities above $1$ elsewhere, and every strategy dominating the initial one reaches $z$. Let $H$ be its induced discounted game, with rewards $(-N)^{\Omega(v)}$ and discount $\beta=1-1/(4N^3M)$.
--
--   The module proves that for every legal player-0 strategy $\sigma$ whose valuations dominate those of the initial strategy,
--
--   $$\operatorname{val}_\sigma(v)\prec\operatorname{val}_\sigma(w)\iff\operatorname{val}^H_\sigma(v)<\operatorname{val}^H_\sigma(w).$$
--
--   It also proves the supporting facts: Bellman expansions and discount bounds for $H$, existence of discounted-optimal counterstrategies, the path-sum formula for plays into the sink, and the sign lemmas. The theorem `sink_discounted_order_lib` has the suffix `_lib` so that it does not clash with the mission theorem `FriedmannParity.sink_discounted_order`.
-- source:
--   Oliver Friedmann, An Exponential Lower Bound for the Latest Deterministic Strategy Iteration Algorithms, LMCS 7(3:19), 2011, arXiv:1106.0778, §9 (reduction to discounted payoff games)

import Definitions.Def_friedmann_parity_lib_valuation
import Definitions.Def_friedmann_payoff
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace FriedmannParity

open scoped BigOperators
open Matrix

section SinkTransport

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Part 0: Discounted Bellman Equation -/

lemma transition_mulVec
    (H : FriedmannDiscounted.Game V) (σ τ : V → V) (x : V → ℚ) (v : V) :
    (FriedmannDiscounted.transition H σ τ *ᵥ x) v = x (step H.arena σ τ v) := by
  classical
  dsimp [FriedmannDiscounted.transition, step, mulVec, dotProduct]
  simp

lemma one_sub_discount_transition_mulVec
    (H : FriedmannDiscounted.Game V) (σ τ : V → V) (x : V → ℚ) (v : V) :
    ((1 - H.discount • FriedmannDiscounted.transition H σ τ) *ᵥ x) v =
      x v - H.discount * x (step H.arena σ τ v) := by
  rw [sub_mulVec, one_mulVec, Pi.sub_apply, ← transition_mulVec H σ τ x v]
  congr 1
  dsimp [mulVec, dotProduct]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

lemma isUnit_det_one_sub_discount_transition
    (H : FriedmannDiscounted.Game V) (hH : FriedmannDiscounted.WellFormed H) (σ τ : V → V) :
    IsUnit (1 - H.discount • FriedmannDiscounted.transition H σ τ).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  rcases Matrix.exists_mulVec_eq_zero_iff.mpr hdet with ⟨x, hxne, hx⟩
  have hfp : ∀ v, x v = H.discount * x (step H.arena σ τ v) := by
    intro v
    have hv := congrFun hx v
    rw [Pi.zero_apply, one_sub_discount_transition_mulVec] at hv
    linarith
  have hne : (Finset.univ : Finset V).Nonempty := by
    by_contra hempty
    apply hxne
    ext v
    exact False.elim (hempty ⟨v, Finset.mem_univ v⟩)
  set M := Finset.univ.sup' hne (fun v => |x v|)
  have hM : ∀ v, |x v| ≤ M := fun v => Finset.le_sup' (fun u => |x u|) (Finset.mem_univ v)
  obtain ⟨v₀, _, hv₀⟩ := Finset.exists_mem_eq_sup' hne (fun v => |x v|)
  have hβ0 : 0 < H.discount := hH.2.1
  have hβ1 : H.discount < 1 := hH.2.2
  by_cases hMpos : 0 < M
  · have hstep : |x v₀| = H.discount * |x (step H.arena σ τ v₀)| := by
      rw [hfp v₀, abs_mul, abs_of_pos hβ0]
    have hle : H.discount * |x (step H.arena σ τ v₀)| ≤ H.discount * M :=
      mul_le_mul_of_nonneg_left (hM _) (le_of_lt hβ0)
    have hlt : H.discount * M < 1 * M :=
      mul_lt_mul_of_pos_right hβ1 hMpos
    linarith
  · apply hxne
    ext v
    have h1 : |x v| ≤ 0 := le_trans (hM v) (not_lt.mp hMpos)
    exact abs_nonpos_iff.mp h1

lemma discounted_playValue_step {H : FriedmannDiscounted.Game V}
    (hH : FriedmannDiscounted.WellFormed H) (σ τ : V → V) (u : V) :
    FriedmannDiscounted.playValue H σ τ u =
      H.reward u + H.discount * FriedmannDiscounted.playValue H σ τ (step H.arena σ τ u) := by
  have hunit := isUnit_det_one_sub_discount_transition H hH σ τ
  set A := 1 - H.discount • FriedmannDiscounted.transition H σ τ
  have hmul : A *ᵥ FriedmannDiscounted.playValue H σ τ = H.reward := by
    unfold FriedmannDiscounted.playValue
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv A hunit, one_mulVec]
  have hu := congrFun hmul u
  rw [one_sub_discount_transition_mulVec] at hu
  linarith

/-! ### Part 1: Basic Properties of `IsSinkGame` and `FriedmannDiscounted.induced` -/

lemma isSinkGame_wellFormed {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) : WellFormed G :=
  hSink.1

lemma isSinkGame_priority_sink {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) : G.priority sink = 1 :=
  hSink.2.2.2.1

lemma isSinkGame_one_lt_priority_of_ne {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {u : V} (hu : u ≠ sink) : 1 < G.priority u :=
  hSink.2.2.2.2.1 u hu

lemma isSinkGame_one_le_priority {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) (u : V) : 1 ≤ G.priority u := by
  by_cases hu : u = sink
  · subst hu
    have hp := isSinkGame_priority_sink hSink
    omega
  · have hp := isSinkGame_one_lt_priority_of_ne hSink hu
    omega

lemma isSinkGame_priority_eq_one_iff {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) (u : V) : G.priority u = 1 ↔ u = sink := by
  constructor
  · intro hp
    by_contra hu
    have := isSinkGame_one_lt_priority_of_ne hSink hu
    omega
  · rintro rfl
    exact isSinkGame_priority_sink hSink

lemma isSinkGame_card_pos {G : Game V} {ι : V → V} {sink : V}
    (_hSink : IsSinkGame G ι sink) : 1 ≤ Fintype.card V :=
  Fintype.card_pos_iff.mpr ⟨sink⟩

lemma two_le_card_of_ne {u v : V} (huv : u ≠ v) : 2 ≤ Fintype.card V := by
  have hsub : ({u, v} : Finset V) ⊆ Finset.univ := Finset.subset_univ _
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_pair huv, Finset.card_univ] at hcard
  exact hcard

noncomputable def maxRewardNat (G : Game V) : ℕ :=
  Finset.univ.sup (fun v => (Fintype.card V) ^ G.priority v)

lemma le_maxRewardNat (G : Game V) (u : V) :
    (Fintype.card V) ^ G.priority u ≤ maxRewardNat G :=
  Finset.le_sup (f := fun v => (Fintype.card V) ^ G.priority v) (Finset.mem_univ u)

lemma isSinkGame_card_le_maxRewardNat {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) : Fintype.card V ≤ maxRewardNat G := by
  have h := le_maxRewardNat G sink
  rw [isSinkGame_priority_sink hSink, pow_one] at h
  exact h

lemma isSinkGame_one_le_maxRewardNat {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) : 1 ≤ maxRewardNat G :=
  le_trans (isSinkGame_card_pos hSink) (isSinkGame_card_le_maxRewardNat hSink)

lemma induced_discount_eq (G : Game V) :
    (FriedmannDiscounted.induced G).discount =
      1 - 1 / (4 * (Fintype.card V : ℚ) ^ 3 * (maxRewardNat G : ℚ)) :=
  rfl

lemma one_sub_induced_discount (G : Game V) :
    1 - (FriedmannDiscounted.induced G).discount =
      1 / (4 * (Fintype.card V : ℚ) ^ 3 * (maxRewardNat G : ℚ)) := by
  rw [induced_discount_eq]
  ring

lemma isSinkGame_induced_denom_ge_four {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) :
    (4 : ℚ) ≤ 4 * (Fintype.card V : ℚ) ^ 3 * (maxRewardNat G : ℚ) := by
  have hN : (1 : ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast isSinkGame_card_pos hSink
  have hM : (1 : ℚ) ≤ (maxRewardNat G : ℚ) := by exact_mod_cast isSinkGame_one_le_maxRewardNat hSink
  have hN3 : (1 : ℚ) ≤ (Fintype.card V : ℚ) ^ 3 := one_le_pow₀ hN
  nlinarith

lemma isSinkGame_wellFormed_induced {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) :
    FriedmannDiscounted.WellFormed (FriedmannDiscounted.induced G) := by
  have hden := isSinkGame_induced_denom_ge_four hSink
  have hden_pos : (0 : ℚ) < 4 * (Fintype.card V : ℚ) ^ 3 * (maxRewardNat G : ℚ) := by linarith
  have hpos : (0 : ℚ) < 1 / (4 * (Fintype.card V : ℚ) ^ 3 * (maxRewardNat G : ℚ)) :=
    div_pos one_pos hden_pos
  have hlt1 : 1 / (4 * (Fintype.card V : ℚ) ^ 3 * (maxRewardNat G : ℚ)) < 1 := by
    rw [div_lt_iff₀ hden_pos]
    linarith
  refine ⟨(isSinkGame_wellFormed hSink).1, ?_, ?_⟩
  · rw [induced_discount_eq]; linarith
  · rw [induced_discount_eq]; linarith

lemma card_mul_one_sub_induced_discount_mul_maxReward
    {G : Game V} {ι : V → V} {sink : V} (hSink : IsSinkGame G ι sink) :
    (Fintype.card V : ℚ) * (1 - (FriedmannDiscounted.induced G).discount) *
      (maxRewardNat G : ℚ) = 1 / (4 * (Fintype.card V : ℚ) ^ 2) := by
  have hN_pos : (0 : ℚ) < (Fintype.card V : ℚ) := by
    exact_mod_cast isSinkGame_card_pos hSink
  have hM_pos : (0 : ℚ) < (maxRewardNat G : ℚ) := by
    exact_mod_cast isSinkGame_one_le_maxRewardNat hSink
  have hN_ne : (Fintype.card V : ℚ) ≠ 0 := ne_of_gt hN_pos
  have hM_ne : (maxRewardNat G : ℚ) ≠ 0 := ne_of_gt hM_pos
  rw [one_sub_induced_discount]
  field_simp

lemma card_mul_one_sub_induced_discount_mul_maxReward_le_quarter
    {G : Game V} {ι : V → V} {sink : V} (hSink : IsSinkGame G ι sink) :
    (Fintype.card V : ℚ) * (1 - (FriedmannDiscounted.induced G).discount) *
      (maxRewardNat G : ℚ) ≤ 1 / 4 := by
  rw [card_mul_one_sub_induced_discount_mul_maxReward hSink]
  have hN : (1 : ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast isSinkGame_card_pos hSink
  have hN2 : (1 : ℚ) ≤ (Fintype.card V : ℚ) ^ 2 := one_le_pow₀ hN
  have hden : (4 : ℚ) ≤ 4 * (Fintype.card V : ℚ) ^ 2 := by linarith
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

lemma card_mul_one_sub_induced_discount_le_quarter
    {G : Game V} {ι : V → V} {sink : V} (hSink : IsSinkGame G ι sink) :
    (Fintype.card V : ℚ) * (1 - (FriedmannDiscounted.induced G).discount) ≤ 1 / 4 := by
  have h1 := card_mul_one_sub_induced_discount_mul_maxReward_le_quarter hSink
  have hM : (1 : ℚ) ≤ (maxRewardNat G : ℚ) := by exact_mod_cast isSinkGame_one_le_maxRewardNat hSink
  have hH := isSinkGame_wellFormed_induced hSink
  have hnonneg : 0 ≤ (Fintype.card V : ℚ) * (1 - (FriedmannDiscounted.induced G).discount) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith [hH.2.2])
  nlinarith

lemma one_sub_pow_le {β : ℚ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ∀ m : ℕ, 1 - β ^ m ≤ (m : ℚ) * (1 - β)
  | 0 => by simp
  | m + 1 => by
    have ih := one_sub_pow_le hβ0 hβ1 m
    have hpow : β ^ m ≤ 1 := pow_le_one₀ hβ0 hβ1
    have h1 : 1 - β ^ (m + 1) = (1 - β ^ m) + β ^ m * (1 - β) := by ring
    have h2 : β ^ m * (1 - β) ≤ 1 * (1 - β) :=
      mul_le_mul_of_nonneg_right hpow (by linarith)
    push_cast
    linarith

lemma induced_discount_pow_bounds {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {t : ℕ} (ht : t ≤ Fintype.card V) :
    1 - (Fintype.card V : ℚ) * (1 - (FriedmannDiscounted.induced G).discount) ≤
      (FriedmannDiscounted.induced G).discount ^ t ∧
    (FriedmannDiscounted.induced G).discount ^ t ≤ 1 := by
  let H := FriedmannDiscounted.induced G
  have hH := isSinkGame_wellFormed_induced hSink
  have hβ0 : 0 ≤ H.discount := le_of_lt hH.2.1
  have hβ1 : H.discount ≤ 1 := le_of_lt hH.2.2
  have hpow1 : H.discount ^ t ≤ 1 := pow_le_one₀ hβ0 hβ1
  have hsub := one_sub_pow_le hβ0 hβ1 t
  have htQ : (t : ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast ht
  have hmul : (t : ℚ) * (1 - H.discount) ≤ (Fintype.card V : ℚ) * (1 - H.discount) :=
    mul_le_mul_of_nonneg_right htQ (by linarith)
  exact ⟨by linarith, hpow1⟩

lemma one_half_le_induced_discount_pow {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {t : ℕ} (ht : t ≤ Fintype.card V) :
    (1 / 2 : ℚ) ≤ (FriedmannDiscounted.induced G).discount ^ t := by
  have hb := (induced_discount_pow_bounds hSink ht).1
  have hq := card_mul_one_sub_induced_discount_le_quarter hSink
  linarith

lemma induced_reward_of_even {G : Game V} {u : V} (he : G.priority u % 2 = 0) :
    (FriedmannDiscounted.induced G).reward u = (Fintype.card V : ℚ) ^ G.priority u := by
  change (- (Fintype.card V : ℚ)) ^ G.priority u = _
  exact (Nat.even_iff.mpr he).neg_pow (Fintype.card V : ℚ)

lemma induced_reward_of_odd {G : Game V} {u : V} (ho : G.priority u % 2 = 1) :
    (FriedmannDiscounted.induced G).reward u = - ((Fintype.card V : ℚ) ^ G.priority u) := by
  change (- (Fintype.card V : ℚ)) ^ G.priority u = _
  exact (Nat.odd_iff.mpr ho).neg_pow (Fintype.card V : ℚ)

lemma abs_induced_reward (G : Game V) (u : V) :
    |(FriedmannDiscounted.induced G).reward u| = (Fintype.card V : ℚ) ^ G.priority u := by
  change |(- (Fintype.card V : ℚ)) ^ G.priority u| = _
  rw [abs_pow, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]

lemma abs_induced_reward_le_maxReward (G : Game V) (u : V) :
    |(FriedmannDiscounted.induced G).reward u| ≤ (maxRewardNat G : ℚ) := by
  rw [abs_induced_reward]
  exact_mod_cast le_maxRewardNat G u

lemma abs_induced_reward_add_card_le (G : Game V) (u : V) :
    |(FriedmannDiscounted.induced G).reward u + (Fintype.card V : ℚ)| ≤
      (Fintype.card V : ℚ) ^ G.priority u + (Fintype.card V : ℚ) := by
  calc |(FriedmannDiscounted.induced G).reward u + (Fintype.card V : ℚ)|
      ≤ |(FriedmannDiscounted.induced G).reward u| + |(Fintype.card V : ℚ)| := abs_add_le _ _
    _ = (Fintype.card V : ℚ) ^ G.priority u + (Fintype.card V : ℚ) := by
      rw [abs_induced_reward, abs_of_nonneg (Nat.cast_nonneg _)]

lemma abs_induced_reward_add_card_le_two_maxReward
    {G : Game V} {ι : V → V} {sink : V} (hSink : IsSinkGame G ι sink) (u : V) :
    |(FriedmannDiscounted.induced G).reward u + (Fintype.card V : ℚ)| ≤
      2 * (maxRewardNat G : ℚ) := by
  have h1 := abs_induced_reward_add_card_le G u
  have h2 : (Fintype.card V : ℚ) ^ G.priority u ≤ (maxRewardNat G : ℚ) := by
    exact_mod_cast le_maxRewardNat G u
  have h3 : (Fintype.card V : ℚ) ≤ (maxRewardNat G : ℚ) := by
    exact_mod_cast isSinkGame_card_le_maxRewardNat hSink
  linarith

lemma sum_Ico_pow_le {B : ℚ} (hB : 2 ≤ B) (a : ℕ) :
    ∀ m : ℕ, a ≤ m → ∑ i ∈ Finset.Ico a m, B ^ i ≤ B ^ m - B ^ a
  | 0, ha => by
    have ha0 : a = 0 := by omega
    subst ha0
    simp
  | m + 1, ha => by
    rcases eq_or_lt_of_le ha with rfl | hlt
    · simp
    · have ham : a ≤ m := by omega
      rw [Finset.sum_Ico_succ_top ham]
      have ih := sum_Ico_pow_le hB a m ham
      have hpow : 0 ≤ B ^ m := pow_nonneg (by linarith) m
      have hmul : 2 * B ^ m ≤ B * B ^ m :=
        mul_le_mul_of_nonneg_right hB hpow
      have hsucc : B ^ (m + 1) = B * B ^ m := by ring
      linarith

/-! ### Part 2: Finite Bellman Expansion and Optimal Counterstrategy in Discounted Games -/

lemma discounted_playValue_expand {H : FriedmannDiscounted.Game V}
    (hH : FriedmannDiscounted.WellFormed H) (σ τ : V → V) (v : V) :
    ∀ m : ℕ,
      FriedmannDiscounted.playValue H σ τ v =
        (∑ t ∈ Finset.range m, H.discount ^ t * H.reward (play H.arena σ τ v t)) +
          H.discount ^ m * FriedmannDiscounted.playValue H σ τ (play H.arena σ τ v m)
  | 0 => by simp [play_zero]
  | m + 1 => by
    rw [discounted_playValue_expand hH σ τ v m, Finset.sum_range_succ, play_succ',
        discounted_playValue_step hH σ τ (play H.arena σ τ v m)]
    ring

lemma discounted_playValue_sub_const_expand {H : FriedmannDiscounted.Game V}
    (hH : FriedmannDiscounted.WellFormed H) (σ τ : V → V) (v : V) {c r₀ : ℚ}
    (hc : c = r₀ + H.discount * c) :
    ∀ m : ℕ,
      FriedmannDiscounted.playValue H σ τ v - c =
        (∑ t ∈ Finset.range m,
          H.discount ^ t * (H.reward (play H.arena σ τ v t) - r₀)) +
          H.discount ^ m * (FriedmannDiscounted.playValue H σ τ (play H.arena σ τ v m) - c)
  | 0 => by simp [play_zero]
  | m + 1 => by
    have hstep : FriedmannDiscounted.playValue H σ τ (play H.arena σ τ v m) - c =
        (H.reward (play H.arena σ τ v m) - r₀) +
          H.discount * (FriedmannDiscounted.playValue H σ τ (step H.arena σ τ (play H.arena σ τ v m)) - c) := by
      have h1 := discounted_playValue_step hH σ τ (play H.arena σ τ v m)
      linarith
    rw [discounted_playValue_sub_const_expand hH σ τ v hc m, Finset.sum_range_succ, play_succ', hstep]
    ring

noncomputable def minDiscStrategy (H : FriedmannDiscounted.Game V)
    (σ τ₁ τ₂ : V → V) (u : V) : V := by
  classical
  exact if FriedmannDiscounted.playValue H σ τ₁ u ≤ FriedmannDiscounted.playValue H σ τ₂ u
    then τ₁ u else τ₂ u

lemma minDiscStrategy_legal {H : FriedmannDiscounted.Game V} {σ τ₁ τ₂ : V → V}
    (hτ₁ : Legal H.arena true τ₁) (hτ₂ : Legal H.arena true τ₂) :
    Legal H.arena true (minDiscStrategy H σ τ₁ τ₂) := by
  intro u hu
  unfold minDiscStrategy
  split_ifs
  · exact hτ₁ u hu
  · exact hτ₂ u hu

lemma playValue_minDiscStrategy_le {H : FriedmannDiscounted.Game V}
    (hH : FriedmannDiscounted.WellFormed H) (σ τ₁ τ₂ : V → V) (v : V) :
    FriedmannDiscounted.playValue H σ (minDiscStrategy H σ τ₁ τ₂) v ≤
      min (FriedmannDiscounted.playValue H σ τ₁ v) (FriedmannDiscounted.playValue H σ τ₂ v) := by
  let τ₃ := minDiscStrategy H σ τ₁ τ₂
  let m : V → ℚ := fun u =>
    min (FriedmannDiscounted.playValue H σ τ₁ u) (FriedmannDiscounted.playValue H σ τ₂ u)
  have hβ0 : 0 < H.discount := hH.2.1
  have hβ1 : H.discount < 1 := hH.2.2
  have hm_step : ∀ u, H.reward u + H.discount * m (step H.arena σ τ₃ u) ≤ m u := by
    intro u
    dsimp only [m, τ₃, step, minDiscStrategy]
    by_cases hle : FriedmannDiscounted.playValue H σ τ₁ u ≤ FriedmannDiscounted.playValue H σ τ₂ u
    · rw [min_eq_left hle, if_pos hle]
      have h1 := discounted_playValue_step hH σ τ₁ u
      dsimp only [step] at h1
      have hmin : m (if H.arena.owner u = false then σ u else τ₁ u) ≤
          FriedmannDiscounted.playValue H σ τ₁ (if H.arena.owner u = false then σ u else τ₁ u) :=
        min_le_left _ _
      nlinarith
    · rw [min_eq_right (le_of_not_ge hle), if_neg hle]
      have h2 := discounted_playValue_step hH σ τ₂ u
      dsimp only [step] at h2
      have hmin : m (if H.arena.owner u = false then σ u else τ₂ u) ≤
          FriedmannDiscounted.playValue H σ τ₂ (if H.arena.owner u = false then σ u else τ₂ u) :=
        min_le_right _ _
      nlinarith
  have hdiff : ∀ u,
      FriedmannDiscounted.playValue H σ τ₃ u - m u ≤
        H.discount * (FriedmannDiscounted.playValue H σ τ₃ (step H.arena σ τ₃ u) - m (step H.arena σ τ₃ u)) := by
    intro u
    have h3 := discounted_playValue_step hH σ τ₃ u
    have hm := hm_step u
    linarith
  have hne : (Finset.univ : Finset V).Nonempty := ⟨v, Finset.mem_univ v⟩
  set M := Finset.univ.sup' hne (fun u => FriedmannDiscounted.playValue H σ τ₃ u - m u)
  have hle_M : ∀ u, FriedmannDiscounted.playValue H σ τ₃ u - m u ≤ M :=
    fun u => Finset.le_sup' (fun w => FriedmannDiscounted.playValue H σ τ₃ w - m w) (Finset.mem_univ u)
  obtain ⟨u₀, _, hu₀⟩ := Finset.exists_mem_eq_sup' hne
    (fun u => FriedmannDiscounted.playValue H σ τ₃ u - m u)
  have hM_step : M ≤ H.discount * M := by
    calc M = FriedmannDiscounted.playValue H σ τ₃ u₀ - m u₀ := hu₀
      _ ≤ H.discount * (FriedmannDiscounted.playValue H σ τ₃ (step H.arena σ τ₃ u₀) -
            m (step H.arena σ τ₃ u₀)) := hdiff u₀
      _ ≤ H.discount * M := mul_le_mul_of_nonneg_left (hle_M _) (le_of_lt hβ0)
  have hM_nonpos : M ≤ 0 := by nlinarith
  have hv := hle_M v
  linarith

lemma exists_disc_counterstrategy_list {H : FriedmannDiscounted.Game V}
    (hH : FriedmannDiscounted.WellFormed H) (σ : V → V) (L : List (V → V)) :
    ∃ ϱ : V → V,
      Legal H.arena true ϱ ∧
      ∀ τ ∈ L, Legal H.arena true τ →
        ∀ v, FriedmannDiscounted.playValue H σ ϱ v ≤ FriedmannDiscounted.playValue H σ τ v := by
  induction L with
  | nil =>
    have hex : ∀ v, ∃ w, H.arena.edge v w := hH.1
    refine ⟨fun v => Classical.choose (hex v), fun v _ => Classical.choose_spec (hex v), ?_⟩
    intro τ hmem
    nomatch hmem
  | cons τ₁ L ih =>
    rcases ih with ⟨τ₂, hτ₂, hle₂⟩
    by_cases hτ₁ : Legal H.arena true τ₁
    · refine ⟨minDiscStrategy H σ τ₁ τ₂, minDiscStrategy_legal hτ₁ hτ₂, ?_⟩
      intro τ hmem hleg v
      have hmin := playValue_minDiscStrategy_le hH σ τ₁ τ₂ v
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact le_trans hmin (min_le_left _ _)
      · exact le_trans hmin (le_trans (min_le_right _ _) (hle₂ τ hmem' hleg v))
    · refine ⟨τ₂, hτ₂, ?_⟩
      intro τ hmem hleg v
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact False.elim (hτ₁ hleg)
      · exact hle₂ τ hmem' hleg v

lemma exists_disc_optimalCounterstrategy {H : FriedmannDiscounted.Game V}
    (hH : FriedmannDiscounted.WellFormed H) (σ : V → V) :
    ∃ ϱ : V → V,
      Legal H.arena true ϱ ∧
      (∀ v τ, Legal H.arena true τ →
        FriedmannDiscounted.playValue H σ ϱ v ≤ FriedmannDiscounted.playValue H σ τ v) ∧
      ∀ v, FriedmannScalar.value (FriedmannDiscounted.model H) σ v =
        FriedmannDiscounted.playValue H σ ϱ v := by
  rcases exists_disc_counterstrategy_list hH σ (Finset.univ : Finset (V → V)).toList with
    ⟨ϱ, hϱ, hle⟩
  have hmin : ∀ v τ, Legal H.arena true τ →
      FriedmannDiscounted.playValue H σ ϱ v ≤ FriedmannDiscounted.playValue H σ τ v :=
    fun v τ hτ => hle τ (Finset.mem_toList.mpr (Finset.mem_univ τ)) hτ v
  refine ⟨ϱ, hϱ, hmin, ?_⟩
  intro v
  classical
  let M := FriedmannDiscounted.model H
  have hex : ∃ a : ℚ,
      (∃ τ, M.minLegal τ ∧ M.payoff σ τ v = a) ∧
        ∀ τ, M.minLegal τ → a ≤ M.payoff σ τ v :=
    ⟨FriedmannDiscounted.playValue H σ ϱ v, ⟨ϱ, hϱ, rfl⟩, fun τ hτ => hmin v τ hτ⟩
  have hval : FriedmannScalar.value M σ v = Classical.choose hex := by
    unfold FriedmannScalar.value
    rw [dif_pos hex]
  rw [hval]
  rcases Classical.choose_spec hex with ⟨⟨τ₀, hτ₀, hpay₀⟩, hle₀⟩
  apply le_antisymm
  · exact hle₀ ϱ hϱ
  · rw [← hpay₀]
    exact hmin v τ₀ hτ₀

/-! ### Part 3: Plays Reaching the 1-Sink -/

lemma cycleLeader_eq_sink_of_cyclePriority_eq_one {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1) :
    cycleLeader G σ τ v = sink := by
  apply (isSinkGame_wellFormed hSink).2
  rw [← playValue_cyclePriority_eq_priority_cycleLeader, hcp, isSinkGame_priority_sink hSink]

lemma eq_sink_of_mem_recurring_of_cyclePriority_eq_one {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v u : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1)
    (hu : u ∈ recurring (play G σ τ v)) :
    u = sink := by
  have hle : G.priority u ≤ (playValue G σ τ v).cyclePriority := Finset.le_sup hu
  have hge : 1 ≤ G.priority u := isSinkGame_one_le_priority hSink u
  exact (isSinkGame_priority_eq_one_iff hSink u).mp (by omega)

lemma step_sink_eq_sink_of_cyclePriority_eq_one {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1) :
    step G σ τ sink = sink := by
  have hcl := cycleLeader_eq_sink_of_cyclePriority_eq_one hSink hcp
  have hmem : sink ∈ recurring (play G σ τ v) := hcl ▸ cycleLeader_mem_recurring G σ τ v
  exact eq_sink_of_mem_recurring_of_cyclePriority_eq_one hSink hcp (step_mem_recurring hmem)

lemma induced_reward_sink {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) :
    (FriedmannDiscounted.induced G).reward sink = - (Fintype.card V : ℚ) := by
  change (- (Fintype.card V : ℚ)) ^ G.priority sink = - (Fintype.card V : ℚ)
  rw [isSinkGame_priority_sink hSink, pow_one]

lemma discounted_playValue_sink_of_cyclePriority_eq_one {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1) :
    FriedmannDiscounted.playValue (FriedmannDiscounted.induced G) σ τ sink =
      - (Fintype.card V : ℚ) / (1 - (FriedmannDiscounted.induced G).discount) := by
  let H := FriedmannDiscounted.induced G
  have hH := isSinkGame_wellFormed_induced hSink
  have hstep := discounted_playValue_step hH σ τ sink
  have hsink_step : step H.arena σ τ sink = sink :=
    step_sink_eq_sink_of_cyclePriority_eq_one hSink hcp
  rw [hsink_step, induced_reward_sink hSink] at hstep
  have hβ1 : H.discount < 1 := hH.2.2
  rw [eq_div_iff (by linarith)]
  linarith

lemma mem_playValue_path_iff_of_cyclePriority_eq_one {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v u : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1) :
    u ∈ (playValue G σ τ v).path ↔
      ∃ t < (playValue G σ τ v).length, play G σ τ v t = u := by
  rw [mem_playValue_path_iff, hcp]
  constructor
  · exact fun h => h.1
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨t, ht, rfl⟩, ?_⟩
    have hne := play_ne_cycleLeader_of_lt_length ht
    rw [cycleLeader_eq_sink_of_cyclePriority_eq_one hSink hcp] at hne
    exact isSinkGame_one_lt_priority_of_ne hSink hne

lemma playValue_path_eq_image_of_cyclePriority_eq_one {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1) :
    (playValue G σ τ v).path =
      (Finset.range (playValue G σ τ v).length).image (play G σ τ v) := by
  ext u
  rw [mem_playValue_path_iff_of_cyclePriority_eq_one hSink hcp, Finset.mem_image]
  simp only [Finset.mem_range]

lemma playValue_path_card_eq_length_of_cyclePriority_eq_one {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1) :
    (playValue G σ τ v).path.card = (playValue G σ τ v).length := by
  rw [playValue_path_eq_image_of_cyclePriority_eq_one hSink hcp]
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj heq
  rw [Finset.mem_coe, Finset.mem_range] at hi hj
  exact play_injective_of_le_length G σ τ v (le_of_lt hi) (le_of_lt hj) heq

lemma ne_sink_of_mem_playValue_path_of_cyclePriority_eq_one {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v u : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1)
    (hu : u ∈ (playValue G σ τ v).path) :
    u ≠ sink := by
  rw [mem_playValue_path_iff, hcp] at hu
  intro rfl
  have hp := isSinkGame_priority_sink hSink
  omega

lemma two_le_priority_of_mem_playValue_path_of_cyclePriority_eq_one
    {G : Game V} {ι : V → V} {sink : V}
    (_hSink : IsSinkGame G ι sink) {σ τ : V → V} {v u : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1)
    (hu : u ∈ (playValue G σ τ v).path) :
    2 ≤ G.priority u := by
  rw [mem_playValue_path_iff, hcp] at hu
  omega

lemma playValue_length_le_card_of_cyclePriority_eq_one {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1) :
    (playValue G σ τ v).length ≤ Fintype.card V := by
  rw [← playValue_path_card_eq_length_of_cyclePriority_eq_one hSink hcp]
  exact Finset.card_le_univ _

lemma valueLT_iff_setLT_of_cyclePriority_eq_one {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ₁ τ₁ σ₂ τ₂ : V → V} {v₁ v₂ : V}
    (hcp₁ : (playValue G σ₁ τ₁ v₁).cyclePriority = 1)
    (hcp₂ : (playValue G σ₂ τ₂ v₂).cyclePriority = 1) :
    ValueLT G (playValue G σ₁ τ₁ v₁) (playValue G σ₂ τ₂ v₂) ↔
      SetLT G (playValue G σ₁ τ₁ v₁).path (playValue G σ₂ τ₂ v₂).path := by
  unfold ValueLT
  rw [hcp₁, hcp₂]
  constructor
  · rintro (hr | ⟨_, hs⟩ | ⟨_, hpath, hl⟩)
    · omega
    · exact hs
    · have hlen : (playValue G σ₁ τ₁ v₁).length = (playValue G σ₂ τ₂ v₂).length := by
        rw [← playValue_path_card_eq_length_of_cyclePriority_eq_one hSink hcp₁,
            ← playValue_path_card_eq_length_of_cyclePriority_eq_one hSink hcp₂, hpath]
      rcases hl with ⟨_, hlt⟩ | ⟨_, hlt⟩ <;> omega
  · intro hs
    exact Or.inr (Or.inl ⟨rfl, hs⟩)

lemma playValue_eq_iff_path_eq_of_cyclePriority_eq_one {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ₁ τ₁ σ₂ τ₂ : V → V} {v₁ v₂ : V}
    (hcp₁ : (playValue G σ₁ τ₁ v₁).cyclePriority = 1)
    (hcp₂ : (playValue G σ₂ τ₂ v₂).cyclePriority = 1) :
    playValue G σ₁ τ₁ v₁ = playValue G σ₂ τ₂ v₂ ↔
      (playValue G σ₁ τ₁ v₁).path = (playValue G σ₂ τ₂ v₂).path := by
  constructor
  · intro h; rw [h]
  · intro hpath
    have hlen : (playValue G σ₁ τ₁ v₁).length = (playValue G σ₂ τ₂ v₂).length := by
      rw [← playValue_path_card_eq_length_of_cyclePriority_eq_one hSink hcp₁,
          ← playValue_path_card_eq_length_of_cyclePriority_eq_one hSink hcp₂, hpath]
    cases hp₁ : playValue G σ₁ τ₁ v₁
    cases hp₂ : playValue G σ₂ τ₂ v₂
    simp only [hp₁, hp₂] at hcp₁ hcp₂ hpath hlen ⊢
    subst hcp₁ hcp₂ hpath hlen
    rfl

lemma playValue_length_play_le (G : Game V) (σ τ : V → V) (w : V) {t : ℕ}
    (ht : t ≤ (playValue G σ τ w).length) :
    (playValue G σ τ (play G σ τ w t)).length ≤ (playValue G σ τ w).length - t := by
  have hcl : ∀ s : ℕ, cycleLeader G σ τ (play G σ τ w s) = cycleLeader G σ τ w := by
    intro s
    induction s with
    | zero => rfl
    | succ s ih => rw [play_succ', cycleLeader_step, ih]
  apply length_le_of_play_eq_cycleLeader
  rw [hcl t, ← play_add]
  have hadd : t + ((playValue G σ τ w).length - t) = (playValue G σ τ w).length := by omega
  rw [hadd]
  exact play_playValue_length G σ τ w

lemma eq_of_playValue_path_eq {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v w : V}
    (hcp_v : (playValue G σ τ v).cyclePriority = 1)
    (hcp_w : (playValue G σ τ w).cyclePriority = 1)
    (hpath : (playValue G σ τ v).path = (playValue G σ τ w).path) :
    v = w := by
  have hlen : (playValue G σ τ v).length = (playValue G σ τ w).length := by
    rw [← playValue_path_card_eq_length_of_cyclePriority_eq_one hSink hcp_v,
        ← playValue_path_card_eq_length_of_cyclePriority_eq_one hSink hcp_w, hpath]
  rcases Nat.eq_zero_or_pos (playValue G σ τ v).length with h0 | hpos
  · have hv : v = sink := by
      have h1 := play_playValue_length G σ τ v
      rw [h0, play_zero, cycleLeader_eq_sink_of_cyclePriority_eq_one hSink hcp_v] at h1
      exact h1
    have hw : w = sink := by
      have h2 := play_playValue_length G σ τ w
      rw [← hlen, h0, play_zero, cycleLeader_eq_sink_of_cyclePriority_eq_one hSink hcp_w] at h2
      exact h2
    exact hv.trans hw.symm
  · have hv_mem : v ∈ (playValue G σ τ v).path := by
      rw [mem_playValue_path_iff_of_cyclePriority_eq_one hSink hcp_v]
      exact ⟨0, hpos, rfl⟩
    rw [hpath, mem_playValue_path_iff_of_cyclePriority_eq_one hSink hcp_w] at hv_mem
    rcases hv_mem with ⟨t, ht, hplay⟩
    have hle := playValue_length_play_le G σ τ w (le_of_lt ht)
    rw [hplay, ← hlen] at hle
    have ht0 : t = 0 := by omega
    rw [ht0, play_zero] at hplay
    exact hplay.symm

/-! ### Part 4: Path Comparison for Plays Reaching the 1-Sink (Lemma 9.7) -/

noncomputable def pathCoeff (G : Game V) (σ τ : V → V) (v u : V) : ℚ := by
  classical
  exact if h : ∃ t < (playValue G σ τ v).length, play G σ τ v t = u then
    (FriedmannDiscounted.induced G).discount ^ (Classical.choose h)
  else 0

lemma pathCoeff_eq_zero_of_notMem {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v u : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1)
    (hu : u ∉ (playValue G σ τ v).path) :
    pathCoeff G σ τ v u = 0 := by
  rw [mem_playValue_path_iff_of_cyclePriority_eq_one hSink hcp] at hu
  unfold pathCoeff
  rw [dif_neg hu]

lemma pathCoeff_play_eq_pow (G : Game V) (σ τ : V → V) (v : V) {t : ℕ}
    (ht : t < (playValue G σ τ v).length) :
    pathCoeff G σ τ v (play G σ τ v t) = (FriedmannDiscounted.induced G).discount ^ t := by
  have hex : ∃ t' < (playValue G σ τ v).length, play G σ τ v t' = play G σ τ v t :=
    ⟨t, ht, rfl⟩
  unfold pathCoeff
  rw [dif_pos hex]
  rcases Classical.choose_spec hex with ⟨ht', heq⟩
  have h_eq := play_injective_of_le_length G σ τ v (le_of_lt ht') (le_of_lt ht) heq
  rw [h_eq]

lemma pathCoeff_bounds_of_mem {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v u : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1)
    (hu : u ∈ (playValue G σ τ v).path) :
    1 - (Fintype.card V : ℚ) * (1 - (FriedmannDiscounted.induced G).discount) ≤
      pathCoeff G σ τ v u ∧
    pathCoeff G σ τ v u ≤ 1 := by
  rw [mem_playValue_path_iff_of_cyclePriority_eq_one hSink hcp] at hu
  rcases hu with ⟨t, ht, rfl⟩
  rw [pathCoeff_play_eq_pow G σ τ v ht]
  have hlen := playValue_length_le_card_of_cyclePriority_eq_one hSink hcp
  exact induced_discount_pow_bounds hSink (le_trans (le_of_lt ht) hlen)

lemma pathCoeff_bounds {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v u : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1) :
    0 ≤ pathCoeff G σ τ v u ∧ pathCoeff G σ τ v u ≤ 1 := by
  by_cases hu : u ∈ (playValue G σ τ v).path
  · have hb := pathCoeff_bounds_of_mem hSink hcp hu
    have hq := card_mul_one_sub_induced_discount_le_quarter hSink
    exact ⟨by linarith, hb.2⟩
  · rw [pathCoeff_eq_zero_of_notMem hSink hcp hu]
    exact ⟨le_rfl, zero_le_one⟩

lemma sum_pathCoeff_mul_eq {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1)
    {S : Finset V} (hsub : (playValue G σ τ v).path ⊆ S) (f : V → ℚ) :
    ∑ u ∈ S, pathCoeff G σ τ v u * f u =
      ∑ t ∈ Finset.range (playValue G σ τ v).length,
        (FriedmannDiscounted.induced G).discount ^ t * f (play G σ τ v t) := by
  have h1 : ∑ u ∈ S, pathCoeff G σ τ v u * f u =
      ∑ u ∈ (playValue G σ τ v).path, pathCoeff G σ τ v u * f u := by
    symm
    apply Finset.sum_subset hsub
    intro u _ hu_not
    rw [pathCoeff_eq_zero_of_notMem hSink hcp hu_not, zero_mul]
  rw [h1, playValue_path_eq_image_of_cyclePriority_eq_one hSink hcp]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    rw [pathCoeff_play_eq_pow G σ τ v ht]
  · intro i hi j hj heq
    rw [Finset.mem_coe, Finset.mem_range] at hi hj
    exact play_injective_of_le_length G σ τ v (le_of_lt hi) (le_of_lt hj) heq

lemma discounted_playValue_sub_sink_eq_sum_pathCoeff {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1)
    {S : Finset V} (hsub : (playValue G σ τ v).path ⊆ S) :
    FriedmannDiscounted.playValue (FriedmannDiscounted.induced G) σ τ v -
      (- (Fintype.card V : ℚ) / (1 - (FriedmannDiscounted.induced G).discount)) =
      ∑ u ∈ S, pathCoeff G σ τ v u *
        ((FriedmannDiscounted.induced G).reward u + (Fintype.card V : ℚ)) := by
  let H := FriedmannDiscounted.induced G
  have hH := isSinkGame_wellFormed_induced hSink
  let c : ℚ := - (Fintype.card V : ℚ) / (1 - H.discount)
  have hc : c = - (Fintype.card V : ℚ) + H.discount * c := by
    dsimp only [c]
    have hβ1 : H.discount < 1 := hH.2.2
    have hne : 1 - H.discount ≠ 0 := by linarith
    field_simp
    ring
  have hexp := discounted_playValue_sub_const_expand hH σ τ v hc (playValue G σ τ v).length
  change FriedmannDiscounted.playValue H σ τ v - c =
    (∑ t ∈ Finset.range (playValue G σ τ v).length,
      H.discount ^ t * (H.reward (play G σ τ v t) - - (Fintype.card V : ℚ))) +
      H.discount ^ (playValue G σ τ v).length *
        (FriedmannDiscounted.playValue H σ τ (play G σ τ v (playValue G σ τ v).length) - c) at hexp
  rw [play_playValue_length, cycleLeader_eq_sink_of_cyclePriority_eq_one hSink hcp,
      discounted_playValue_sink_of_cyclePriority_eq_one hSink hcp] at hexp
  change FriedmannDiscounted.playValue H σ τ v - c = _
  rw [hexp, sub_self, mul_zero, add_zero, sum_pathCoeff_mul_eq hSink hcp hsub]
  apply Finset.sum_congr rfl
  intro t _
  ring

lemma discounted_playValue_lt_of_setLT {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ₁ τ₁ σ₂ τ₂ : V → V} {v₁ v₂ : V}
    (hcp₁ : (playValue G σ₁ τ₁ v₁).cyclePriority = 1)
    (hcp₂ : (playValue G σ₂ τ₂ v₂).cyclePriority = 1)
    (hset : SetLT G (playValue G σ₁ τ₁ v₁).path (playValue G σ₂ τ₂ v₂).path) :
    FriedmannDiscounted.playValue (FriedmannDiscounted.induced G) σ₁ τ₁ v₁ <
      FriedmannDiscounted.playValue (FriedmannDiscounted.induced G) σ₂ τ₂ v₂ := by
  let H := FriedmannDiscounted.induced G
  let U := (playValue G σ₁ τ₁ v₁).path
  let W := (playValue G σ₂ τ₂ v₂).path
  let N : ℚ := (Fintype.card V : ℚ)
  let c : ℚ := - N / (1 - H.discount)
  let g : V → ℚ := fun u =>
    (pathCoeff G σ₂ τ₂ v₂ u - pathCoeff G σ₁ τ₁ v₁ u) * (H.reward u + N)
  have hsub₁ := discounted_playValue_sub_sink_eq_sum_pathCoeff hSink hcp₁
    (Finset.subset_union_left : U ⊆ U ∪ W)
  have hsub₂ := discounted_playValue_sub_sink_eq_sum_pathCoeff hSink hcp₂
    (Finset.subset_union_right : W ⊆ U ∪ W)
  have hdiff : FriedmannDiscounted.playValue H σ₂ τ₂ v₂ -
      FriedmannDiscounted.playValue H σ₁ τ₁ v₁ = ∑ u ∈ U ∪ W, g u := by
    calc FriedmannDiscounted.playValue H σ₂ τ₂ v₂ - FriedmannDiscounted.playValue H σ₁ τ₁ v₁
        = (FriedmannDiscounted.playValue H σ₂ τ₂ v₂ - c) -
            (FriedmannDiscounted.playValue H σ₁ τ₁ v₁ - c) := by ring
      _ = (∑ u ∈ U ∪ W, pathCoeff G σ₂ τ₂ v₂ u * (H.reward u + N)) -
            (∑ u ∈ U ∪ W, pathCoeff G σ₁ τ₁ v₁ u * (H.reward u + N)) := by rw [hsub₂, hsub₁]
      _ = ∑ u ∈ U ∪ W, g u := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun _ _ => by dsimp [g]; ring)
  rcases hset with ⟨u_m, hu_mem, hu_max, hu_par⟩
  let p_m := G.priority u_m
  have hu_union : u_m ∈ U ∪ W := by
    rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff] at hu_mem
    rw [Finset.mem_union]
    rcases hu_mem with ⟨hU, _⟩ | ⟨hW, _⟩
    · exact Or.inl hU
    · exact Or.inr hW
  have hne_sink_union : ∀ u ∈ U ∪ W, u ≠ sink := by
    intro u hu
    rcases Finset.mem_union.mp hu with hU | hW
    · exact ne_sink_of_mem_playValue_path_of_cyclePriority_eq_one hSink hcp₁ hU
    · exact ne_sink_of_mem_playValue_path_of_cyclePriority_eq_one hSink hcp₂ hW
  have hprio_ge_two_union : ∀ u ∈ U ∪ W, 2 ≤ G.priority u := by
    intro u hu
    rcases Finset.mem_union.mp hu with hU | hW
    · exact two_le_priority_of_mem_playValue_path_of_cyclePriority_eq_one hSink hcp₁ hU
    · exact two_le_priority_of_mem_playValue_path_of_cyclePriority_eq_one hSink hcp₂ hW
  have hu_m_ne_sink : u_m ≠ sink := hne_sink_union u_m hu_union
  have hp_m_ge_two : 2 ≤ p_m := hprio_ge_two_union u_m hu_union
  have hN_ge_two_nat : 2 ≤ Fintype.card V := two_le_card_of_ne hu_m_ne_sink
  have hN_ge_two : (2 : ℚ) ≤ N := by
    dsimp only [N]
    exact_mod_cast hN_ge_two_nat
  let S_gt := ((U ∪ W).erase u_m).filter (fun u => p_m < G.priority u)
  let S_lt := ((U ∪ W).erase u_m).filter (fun u => ¬ p_m < G.priority u)
  have hsplit : ∑ u ∈ U ∪ W, g u = g u_m + ((∑ u ∈ S_gt, g u) + (∑ u ∈ S_lt, g u)) := by
    rw [← Finset.add_sum_erase _ _ hu_union,
        ← Finset.sum_filter_add_sum_filter_not ((U ∪ W).erase u_m) (fun u => p_m < G.priority u)]
  -- Bound 1: g u_m ≥ N ^ p_m - N - 1 / 2
  have hpow_ge_N : N ≤ N ^ p_m := by
    have h1 : N ^ 1 ≤ N ^ p_m := pow_le_pow_right₀ (by linarith) (by omega)
    simpa using h1
  have hpow_le_M : N ^ p_m ≤ (maxRewardNat G : ℚ) := by
    dsimp only [N, p_m]
    exact_mod_cast le_maxRewardNat G u_m
  have hg_um_1 : (1 - N * (1 - H.discount)) * (N ^ p_m - N) ≤ g u_m := by
    rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff] at hu_mem
    rcases hu_par with ⟨he, huW⟩ | ⟨ho, huU⟩
    · have hu_notU : u_m ∉ U := by
        rcases hu_mem with ⟨_, hnW⟩ | ⟨_, hnU⟩
        · exact False.elim (hnW huW)
        · exact hnU
      have hc1 := pathCoeff_eq_zero_of_notMem hSink hcp₁ hu_notU
      have hc2 := pathCoeff_bounds_of_mem hSink hcp₂ huW
      have hc2_nonneg := (pathCoeff_bounds hSink hcp₂ (u := u_m)).1
      have hrew := induced_reward_of_even (G := G) he
      dsimp only [g]
      rw [hc1, sub_zero, hrew]
      have h1 : pathCoeff G σ₂ τ₂ v₂ u_m * (N ^ p_m - N) ≤
          pathCoeff G σ₂ τ₂ v₂ u_m * (N ^ p_m + N) :=
        mul_le_mul_of_nonneg_left (by linarith) hc2_nonneg
      have h2 : (1 - N * (1 - H.discount)) * (N ^ p_m - N) ≤
          pathCoeff G σ₂ τ₂ v₂ u_m * (N ^ p_m - N) :=
        mul_le_mul_of_nonneg_right hc2.1 (by linarith)
      linarith
    · have hu_notW : u_m ∉ W := by
        rcases hu_mem with ⟨_, hnW⟩ | ⟨_, hnU⟩
        · exact hnW
        · exact False.elim (hnU huU)
      have hc2 := pathCoeff_eq_zero_of_notMem hSink hcp₂ hu_notW
      have hc1 := pathCoeff_bounds_of_mem hSink hcp₁ huU
      have hrew := induced_reward_of_odd (G := G) ho
      dsimp only [g]
      rw [hc2, zero_sub, hrew]
      have heq : - pathCoeff G σ₁ τ₁ v₁ u_m * (- N ^ p_m + N) =
          pathCoeff G σ₁ τ₁ v₁ u_m * (N ^ p_m - N) := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hc1.1 (by linarith)
  have hg_um : N ^ p_m - N - 1 / 2 ≤ g u_m := by
    have hq := card_mul_one_sub_induced_discount_mul_maxReward_le_quarter hSink
    have hH := isSinkGame_wellFormed_induced hSink
    have hnonneg : 0 ≤ N * (1 - H.discount) :=
      mul_nonneg (by linarith) (by linarith [hH.2.2])
    have hle : N * (1 - H.discount) * (N ^ p_m - N) ≤
        N * (1 - H.discount) * (maxRewardNat G : ℚ) :=
      mul_le_mul_of_nonneg_left (by linarith) hnonneg
    linarith
  -- Bound 2: -(1 / 2) ≤ ∑ u ∈ S_gt, g u
  have hS_gt_term : ∀ u ∈ S_gt, |g u| ≤ 1 / (2 * N) := by
    intro u hu
    rw [Finset.mem_filter, Finset.mem_erase] at hu
    rcases hu with ⟨⟨_, hu_UW⟩, hpu⟩
    have hu_UW' : u ∈ U ∧ u ∈ W := by
      rcases Finset.mem_union.mp hu_UW with hU | hW
      · refine ⟨hU, ?_⟩
        by_contra hnW
        have hsd : u ∈ (U \ W) ∪ (W \ U) :=
          Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hU, hnW⟩))
        have := hu_max u hsd
        omega
      · refine ⟨?_, hW⟩
        by_contra hnU
        have hsd : u ∈ (U \ W) ∪ (W \ U) :=
          Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hW, hnU⟩))
        have := hu_max u hsd
        omega
    have hb1 := pathCoeff_bounds_of_mem hSink hcp₁ hu_UW'.1
    have hb2 := pathCoeff_bounds_of_mem hSink hcp₂ hu_UW'.2
    have habs_c : |pathCoeff G σ₂ τ₂ v₂ u - pathCoeff G σ₁ τ₁ v₁ u| ≤ N * (1 - H.discount) :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have habs_r := abs_induced_reward_add_card_le_two_maxReward hSink u
    dsimp only [g]
    rw [abs_mul]
    have hmul : |pathCoeff G σ₂ τ₂ v₂ u - pathCoeff G σ₁ τ₁ v₁ u| * |H.reward u + N| ≤
        (N * (1 - H.discount)) * (2 * (maxRewardNat G : ℚ)) :=
      mul_le_mul habs_c habs_r (abs_nonneg _) (by linarith [hb1.1, hb1.2])
    have heq : (N * (1 - H.discount)) * (2 * (maxRewardNat G : ℚ)) =
        2 * (N * (1 - H.discount) * (maxRewardNat G : ℚ)) := by ring
    rw [heq, card_mul_one_sub_induced_discount_mul_maxReward hSink] at hmul
    have hle_div : 2 * (1 / (4 * N ^ 2)) ≤ 1 / (2 * N) := by
      have hN2 : 2 * N ≤ 2 * N ^ 2 := by nlinarith
      have h1 : 2 * (1 / (4 * N ^ 2)) = 1 / (2 * N ^ 2) := by ring
      rw [h1, div_le_div_iff₀ (by nlinarith) (by linarith)]
      linarith
    linarith
  have hS_gt : - (1 / 2 : ℚ) ≤ ∑ u ∈ S_gt, g u := by
    have habs : |∑ u ∈ S_gt, g u| ≤ 1 / 2 := by
      have hcard_S_gt : (S_gt.card : ℚ) ≤ N := by
        dsimp only [N]
        exact_mod_cast Finset.card_le_univ S_gt
      have hdiv_nonneg : (0 : ℚ) ≤ 1 / (2 * N) :=
        div_nonneg zero_le_one (by linarith)
      calc |∑ u ∈ S_gt, g u|
          ≤ ∑ u ∈ S_gt, |g u| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _u ∈ S_gt, (1 / (2 * N)) := Finset.sum_le_sum hS_gt_term
        _ = (S_gt.card : ℚ) * (1 / (2 * N)) := by simp
        _ ≤ N * (1 / (2 * N)) := mul_le_mul_of_nonneg_right hcard_S_gt hdiv_nonneg
        _ = 1 / 2 := by
          have hN_ne : N ≠ 0 := by linarith
          field_simp
    exact (abs_le.mp habs).1
  -- Bound 3: -(N ^ p_m - 2 * N) ≤ ∑ u ∈ S_lt, g u
  have hS_lt_term : ∀ u ∈ S_lt, |g u| ≤ N ^ G.priority u + N := by
    intro u _
    have hb1 := pathCoeff_bounds hSink hcp₁ (u := u)
    have hb2 := pathCoeff_bounds hSink hcp₂ (u := u)
    have habs_c : |pathCoeff G σ₂ τ₂ v₂ u - pathCoeff G σ₁ τ₁ v₁ u| ≤ 1 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have habs_r := abs_induced_reward_add_card_le G u
    dsimp only [g]
    rw [abs_mul]
    calc |pathCoeff G σ₂ τ₂ v₂ u - pathCoeff G σ₁ τ₁ v₁ u| * |H.reward u + N|
        ≤ 1 * (N ^ G.priority u + N) :=
          mul_le_mul habs_c habs_r (abs_nonneg _) zero_le_one
      _ = N ^ G.priority u + N := one_mul _
  have hS_lt_pow : ∑ u ∈ S_lt, N ^ G.priority u ≤ N ^ p_m - N ^ 2 := by
    have hsub_Ico : S_lt.image G.priority ⊆ Finset.Ico 2 p_m := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨u, hu, rfl⟩
      rw [Finset.mem_filter, Finset.mem_erase] at hu
      rcases hu with ⟨⟨hu_ne, hu_UW⟩, hnot_gt⟩
      have hge2 := hprio_ge_two_union u hu_UW
      have hne_pm : G.priority u ≠ p_m := fun heq => hu_ne ((isSinkGame_wellFormed hSink).2 heq)
      rw [Finset.mem_Ico]
      exact ⟨hge2, by omega⟩
    have hinj_on : Set.InjOn G.priority S_lt := by
      intro x _ y _ hxy
      exact (isSinkGame_wellFormed hSink).2 hxy
    calc ∑ u ∈ S_lt, N ^ G.priority u
        = ∑ p ∈ S_lt.image G.priority, N ^ p :=
          (Finset.sum_image (f := fun p => N ^ p) hinj_on).symm
      _ ≤ ∑ p ∈ Finset.Ico 2 p_m, N ^ p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_Ico (fun _ _ _ => pow_nonneg (by linarith) _)
      _ ≤ N ^ p_m - N ^ 2 := sum_Ico_pow_le hN_ge_two 2 p_m hp_m_ge_two
  have hS_lt_card : (S_lt.card : ℚ) ≤ N - 2 := by
    have hsub_erase : S_lt ⊆ (Finset.univ.erase sink).erase u_m := by
      intro u hu
      rw [Finset.mem_filter, Finset.mem_erase] at hu
      rcases hu with ⟨⟨hu_ne_um, hu_UW⟩, _⟩
      have hu_ne_sink := hne_sink_union u hu_UW
      rw [Finset.mem_erase, Finset.mem_erase]
      exact ⟨hu_ne_um, hu_ne_sink, Finset.mem_univ u⟩
    have hcard_le := Finset.card_le_card hsub_erase
    have hum_mem_erase : u_m ∈ (Finset.univ : Finset V).erase sink :=
      Finset.mem_erase.mpr ⟨hu_m_ne_sink, Finset.mem_univ u_m⟩
    rw [Finset.card_erase_of_mem hum_mem_erase,
        Finset.card_erase_of_mem (Finset.mem_univ sink), Finset.card_univ] at hcard_le
    have hcard_nat : S_lt.card + 2 ≤ Fintype.card V := by omega
    have hcard_Q : ((S_lt.card + 2 : ℕ) : ℚ) ≤ N := by
      dsimp only [N]
      exact_mod_cast hcard_nat
    push_cast at hcard_Q
    linarith
  have hS_lt : - (N ^ p_m - 2 * N) ≤ ∑ u ∈ S_lt, g u := by
    have habs : |∑ u ∈ S_lt, g u| ≤ N ^ p_m - 2 * N := by
      calc |∑ u ∈ S_lt, g u|
          ≤ ∑ u ∈ S_lt, |g u| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ u ∈ S_lt, (N ^ G.priority u + N) := Finset.sum_le_sum hS_lt_term
        _ = (∑ u ∈ S_lt, N ^ G.priority u) + (∑ _u ∈ S_lt, N) := Finset.sum_add_distrib
        _ = (∑ u ∈ S_lt, N ^ G.priority u) + (S_lt.card : ℚ) * N := by simp
        _ ≤ (N ^ p_m - N ^ 2) + (N - 2) * N :=
          add_le_add hS_lt_pow (mul_le_mul_of_nonneg_right hS_lt_card (by linarith))
        _ = N ^ p_m - 2 * N := by ring
    exact (abs_le.mp habs).1
  linarith

/-! ### Part 5: Excluding Non-Sink Cycles (Lemma 9.6) and Main Theorem -/

lemma abs_sum_range_reward_le {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) (σ τ : V → V) (v : V) {k : ℕ}
    (hk : k ≤ Fintype.card V) :
    |∑ t ∈ Finset.range k,
      (FriedmannDiscounted.induced G).discount ^ t *
        (FriedmannDiscounted.induced G).reward (play G σ τ v t)| ≤
      (Fintype.card V : ℚ) * (maxRewardNat G : ℚ) := by
  let H := FriedmannDiscounted.induced G
  have hH := isSinkGame_wellFormed_induced hSink
  have hβ0 : 0 ≤ H.discount := le_of_lt hH.2.1
  have hβ1 : H.discount ≤ 1 := le_of_lt hH.2.2
  calc |∑ t ∈ Finset.range k, H.discount ^ t * H.reward (play G σ τ v t)|
      ≤ ∑ t ∈ Finset.range k, |H.discount ^ t * H.reward (play G σ τ v t)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ Finset.range k, (maxRewardNat G : ℚ) := by
      apply Finset.sum_le_sum
      intro t _
      rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
      calc H.discount ^ t * |H.reward (play G σ τ v t)|
          ≤ 1 * (maxRewardNat G : ℚ) :=
            mul_le_mul (pow_le_one₀ hβ0 hβ1) (abs_induced_reward_le_maxReward G _)
              (abs_nonneg _) zero_le_one
        _ = (maxRewardNat G : ℚ) := one_mul _
    _ = (k : ℚ) * (maxRewardNat G : ℚ) := by simp
    _ ≤ (Fintype.card V : ℚ) * (maxRewardNat G : ℚ) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hk
      · exact Nat.cast_nonneg _

lemma discounted_playValue_lt_zero_of_cyclePriority_eq_one
    {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1) :
    FriedmannDiscounted.playValue (FriedmannDiscounted.induced G) σ τ v < 0 := by
  have hH := isSinkGame_wellFormed_induced hSink
  have hk : (playValue G σ τ v).length ≤ Fintype.card V :=
    playValue_length_le_card_of_cyclePriority_eq_one hSink hcp
  have hexp := discounted_playValue_expand hH σ τ v (playValue G σ τ v).length
  change FriedmannDiscounted.playValue (FriedmannDiscounted.induced G) σ τ v =
    (∑ t ∈ Finset.range (playValue G σ τ v).length,
      (FriedmannDiscounted.induced G).discount ^ t *
        (FriedmannDiscounted.induced G).reward (play G σ τ v t)) +
      (FriedmannDiscounted.induced G).discount ^ (playValue G σ τ v).length *
        FriedmannDiscounted.playValue (FriedmannDiscounted.induced G) σ τ
          (play G σ τ v (playValue G σ τ v).length) at hexp
  rw [play_playValue_length, cycleLeader_eq_sink_of_cyclePriority_eq_one hSink hcp,
      discounted_playValue_sink_of_cyclePriority_eq_one hSink hcp] at hexp
  have hsum_le := (abs_le.mp (abs_sum_range_reward_le hSink σ τ v hk)).2
  have hpow_half := one_half_le_induced_discount_pow hSink hk
  have hN1 : (1 : ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast isSinkGame_card_pos hSink
  have hM1 : (1 : ℚ) ≤ (maxRewardNat G : ℚ) := by exact_mod_cast isSinkGame_one_le_maxRewardNat hSink
  have hN4 : (Fintype.card V : ℚ) ≤ (Fintype.card V : ℚ) ^ 4 := le_self_pow₀ hN1 (by omega)
  have hsink_val : - (Fintype.card V : ℚ) / (1 - (FriedmannDiscounted.induced G).discount) =
      - (4 * (Fintype.card V : ℚ) ^ 4 * (maxRewardNat G : ℚ)) := by
    rw [one_sub_induced_discount]
    have hN_ne : (Fintype.card V : ℚ) ≠ 0 := by linarith
    have hM_ne : (maxRewardNat G : ℚ) ≠ 0 := by linarith
    field_simp
  rw [hsink_val] at hexp
  have hsink_ge : 4 * (Fintype.card V : ℚ) * (maxRewardNat G : ℚ) ≤
      4 * (Fintype.card V : ℚ) ^ 4 * (maxRewardNat G : ℚ) := by nlinarith
  have htail_ge : (1 / 2) * (4 * (Fintype.card V : ℚ) * (maxRewardNat G : ℚ)) ≤
      (FriedmannDiscounted.induced G).discount ^ (playValue G σ τ v).length *
        (4 * (Fintype.card V : ℚ) ^ 4 * (maxRewardNat G : ℚ)) :=
    mul_le_mul hpow_half hsink_ge (by nlinarith) (by linarith)
  nlinarith

lemma zero_lt_discounted_playValue_of_cycleLeader_ne_sink
    {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v : V}
    (hrew_ge : reward 1 ≤ reward (playValue G σ τ v).cyclePriority)
    (hw_ne : cycleLeader G σ τ v ≠ sink) :
    0 < FriedmannDiscounted.playValue (FriedmannDiscounted.induced G) σ τ v := by
  let H := FriedmannDiscounted.induced G
  have hH := isSinkGame_wellFormed_induced hSink
  let w := cycleLeader G σ τ v
  let p_w := G.priority w
  let N : ℚ := (Fintype.card V : ℚ)
  have hcp_eq : (playValue G σ τ v).cyclePriority = p_w :=
    playValue_cyclePriority_eq_priority_cycleLeader G σ τ v
  have hp_w_gt_one : 1 < p_w := isSinkGame_one_lt_priority_of_ne hSink hw_ne
  have hp_w_even : p_w % 2 = 0 := by
    rw [hcp_eq] at hrew_ge
    unfold reward at hrew_ge
    rcases Nat.mod_two_eq_zero_or_one p_w with he | ho
    · exact he
    · rw [if_neg (by omega), if_neg (by omega)] at hrew_ge
      omega
  have hN_ge_two : (2 : ℚ) ≤ N := by
    dsimp only [N]
    exact_mod_cast two_le_card_of_ne hw_ne
  -- Simple cycle from w to w of length L = d + 1
  have hw_rec : w ∈ recurring (play G σ τ v) := cycleLeader_mem_recurring G σ τ v
  have hcp_w : (playValue G σ τ w).cyclePriority = (playValue G σ τ v).cyclePriority := by
    simp only [playValue_cyclePriority, recurring_eq_of_mem_recurring hw_rec]
  have hcl_w : cycleLeader G σ τ w = w :=
    cycleLeader_eq_of_cyclePriority_eq (isSinkGame_wellFormed hSink).2 hcp_w
  let w' := step G σ τ w
  have hcl_w' : cycleLeader G σ τ w' = w := (cycleLeader_step G σ τ w).trans hcl_w
  let d := (playValue G σ τ w').length
  let L := d + 1
  have hplay_L : play G σ τ w L = w := by
    dsimp only [L, d, w']
    rw [play_succ]
    exact (play_playValue_length G σ τ w').trans hcl_w'
  have hinj_L : Set.InjOn (play G σ τ w) (Finset.range L) := by
    intro i hi j hj heq
    rw [Finset.mem_coe, Finset.mem_range] at hi hj
    rcases i with _ | i' <;> rcases j with _ | j'
    · rfl
    · exfalso
      rw [play_zero, play_succ] at heq
      have hne := play_ne_cycleLeader_of_lt_length (G := G) (σ := σ) (τ := τ) (v := w') (t := j')
        (by omega)
      rw [hcl_w'] at hne
      exact hne heq.symm
    · exfalso
      rw [play_succ, play_zero] at heq
      have hne := play_ne_cycleLeader_of_lt_length (G := G) (σ := σ) (τ := τ) (v := w') (t := i')
        (by omega)
      rw [hcl_w'] at hne
      exact hne heq
    · rw [play_succ, play_succ] at heq
      have h_eq := play_injective_of_le_length G σ τ w' (by omega) (by omega) heq
      omega
  have hL_le_N : L ≤ Fintype.card V := by
    have hcard := Finset.card_image_of_injOn hinj_L
    rw [Finset.card_range] at hcard
    rw [← hcard]
    exact Finset.card_le_univ _
  -- Expand playValue H σ τ w over L steps
  have hexp_w := discounted_playValue_expand hH σ τ w L
  change FriedmannDiscounted.playValue H σ τ w =
    (∑ t ∈ Finset.range L, H.discount ^ t * H.reward (play G σ τ w t)) +
      H.discount ^ L * FriedmannDiscounted.playValue H σ τ (play G σ τ w L) at hexp_w
  rw [hplay_L] at hexp_w
  have hsum_split : ∑ t ∈ Finset.range L, H.discount ^ t * H.reward (play G σ τ w t) =
      N ^ p_w + ∑ t ∈ Finset.Ico 1 L, H.discount ^ t * H.reward (play G σ τ w t) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < L)]
    simp only [pow_zero, one_mul, play_zero]
    rw [induced_reward_of_even hp_w_even]
  have hIco_bound : -(N ^ p_w - N) ≤
      ∑ t ∈ Finset.Ico 1 L, H.discount ^ t * H.reward (play G σ τ w t) := by
    have habs : |∑ t ∈ Finset.Ico 1 L, H.discount ^ t * H.reward (play G σ τ w t)| ≤
        N ^ p_w - N := by
      have hβ0 : 0 ≤ H.discount := le_of_lt hH.2.1
      have hβ1 : H.discount ≤ 1 := le_of_lt hH.2.2
      have hsub_Ico : (Finset.Ico 1 L).image (fun t => G.priority (play G σ τ w t)) ⊆
          Finset.Ico 1 p_w := by
        intro p hp
        rcases Finset.mem_image.mp hp with ⟨t, ht, rfl⟩
        rw [Finset.mem_Ico] at ht ⊢
        have hmem_t : play G σ τ w t ∈ recurring (play G σ τ v) :=
          play_mem_recurring hw_rec t
        have hle_pw : G.priority (play G σ τ w t) ≤ p_w := by
          rw [← hcp_eq]
          exact Finset.le_sup hmem_t
        have hne_w : play G σ τ w t ≠ w := by
          intro heq
          have h0 : play G σ τ w t = play G σ τ w 0 := heq
          have ht0 := hinj_L (Finset.mem_coe.mpr (Finset.mem_range.mpr ht.2))
            (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))) h0
          omega
        have hne_pw : G.priority (play G σ τ w t) ≠ p_w :=
          fun heq => hne_w ((isSinkGame_wellFormed hSink).2 heq)
        exact ⟨isSinkGame_one_le_priority hSink _, by omega⟩
      have hinj_prio : Set.InjOn (fun t => G.priority (play G σ τ w t)) (Finset.Ico 1 L) := by
        intro i hi j hj heq
        rw [Finset.mem_coe, Finset.mem_Ico] at hi hj
        have hplay_eq := (isSinkGame_wellFormed hSink).2 heq
        exact hinj_L (Finset.mem_coe.mpr (Finset.mem_range.mpr hi.2))
          (Finset.mem_coe.mpr (Finset.mem_range.mpr hj.2)) hplay_eq
      calc |∑ t ∈ Finset.Ico 1 L, H.discount ^ t * H.reward (play G σ τ w t)|
          ≤ ∑ t ∈ Finset.Ico 1 L, |H.discount ^ t * H.reward (play G σ τ w t)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ t ∈ Finset.Ico 1 L, N ^ G.priority (play G σ τ w t) := by
          apply Finset.sum_le_sum
          intro t _
          rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), abs_induced_reward]
          calc H.discount ^ t * N ^ G.priority (play G σ τ w t)
              ≤ 1 * N ^ G.priority (play G σ τ w t) :=
                mul_le_mul_of_nonneg_right (pow_le_one₀ hβ0 hβ1) (pow_nonneg (by linarith) _)
            _ = N ^ G.priority (play G σ τ w t) := one_mul _
        _ = ∑ p ∈ (Finset.Ico 1 L).image (fun t => G.priority (play G σ τ w t)), N ^ p :=
          (Finset.sum_image (f := fun p => N ^ p) hinj_prio).symm
        _ ≤ ∑ p ∈ Finset.Ico 1 p_w, N ^ p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_Ico (fun _ _ _ => pow_nonneg (by linarith) _)
        _ ≤ N ^ p_w - N ^ 1 := sum_Ico_pow_le hN_ge_two 1 p_w (by omega)
        _ = N ^ p_w - N := by rw [pow_one]
    exact (abs_le.mp habs).1
  have hcycle_ge : N ≤ (1 - H.discount ^ L) * FriedmannDiscounted.playValue H σ τ w := by
    linarith
  have h1_sub_pow_pos : 0 < 1 - H.discount ^ L := by
    have hlt : H.discount ^ L < 1 := pow_lt_one₀ (le_of_lt hH.2.1) hH.2.2 (by omega)
    linarith
  have hx_w_pos : 0 < FriedmannDiscounted.playValue H σ τ w := by
    by_contra hle
    have : (1 - H.discount ^ L) * FriedmannDiscounted.playValue H σ τ w ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt h1_sub_pow_pos) (not_lt.mp hle)
    linarith
  have h1_sub_pow_le : 1 - H.discount ^ L ≤ N * (1 - H.discount) := by
    have hb := (induced_discount_pow_bounds hSink hL_le_N).1
    linarith
  have hN_le_mul : N ≤ N * (1 - H.discount) * FriedmannDiscounted.playValue H σ τ w := by
    calc N ≤ (1 - H.discount ^ L) * FriedmannDiscounted.playValue H σ τ w := hcycle_ge
      _ ≤ (N * (1 - H.discount)) * FriedmannDiscounted.playValue H σ τ w :=
        mul_le_mul_of_nonneg_right h1_sub_pow_le (le_of_lt hx_w_pos)
  have hx_w_ge : 4 * N * (maxRewardNat G : ℚ) ≤ FriedmannDiscounted.playValue H σ τ w := by
    have hq := card_mul_one_sub_induced_discount_mul_maxReward hSink
    have hN2 : 1 ≤ N ^ 2 := by nlinarith
    have hmul : (N * (1 - H.discount) * (maxRewardNat G : ℚ)) * (4 * N ^ 2) = 1 := by
      dsimp only [N, H]
      rw [hq]
      have hN_ne : (Fintype.card V : ℚ) ≠ 0 := by linarith
      field_simp
    have h1 : 4 * N ^ 3 * (maxRewardNat G : ℚ) ≤ FriedmannDiscounted.playValue H σ τ w := by
      nlinarith
    have hM1 : (1 : ℚ) ≤ (maxRewardNat G : ℚ) := by exact_mod_cast isSinkGame_one_le_maxRewardNat hSink
    have hN_le_N3 : N ≤ N ^ 3 := by nlinarith
    nlinarith
  -- Now expand playValue H σ τ v to w in k ≤ Fintype.card V steps
  let k := (playValue G σ τ v).length
  have hk : k ≤ Fintype.card V := by
    have hinj_k : Set.InjOn (play G σ τ v) (Finset.range k) := by
      intro i hi j hj heq
      rw [Finset.mem_coe, Finset.mem_range] at hi hj
      exact play_injective_of_le_length G σ τ v (le_of_lt hi) (le_of_lt hj) heq
    have hcard := Finset.card_image_of_injOn hinj_k
    rw [Finset.card_range] at hcard
    rw [← hcard]
    exact Finset.card_le_univ _
  have hexp_v := discounted_playValue_expand hH σ τ v k
  change FriedmannDiscounted.playValue H σ τ v =
    (∑ t ∈ Finset.range k, H.discount ^ t * H.reward (play G σ τ v t)) +
      H.discount ^ k * FriedmannDiscounted.playValue H σ τ (play G σ τ v (playValue G σ τ v).length) at hexp_v
  rw [play_playValue_length] at hexp_v
  have hsum_ge := (abs_le.mp (abs_sum_range_reward_le hSink σ τ v hk)).1
  have hpow_half := one_half_le_induced_discount_pow hSink hk
  have hM1 : (1 : ℚ) ≤ (maxRewardNat G : ℚ) := by exact_mod_cast isSinkGame_one_le_maxRewardNat hSink
  have htail_ge : (1 / 2) * (4 * N * (maxRewardNat G : ℚ)) ≤
      H.discount ^ k * FriedmannDiscounted.playValue H σ τ w :=
    mul_le_mul hpow_half hx_w_ge (by nlinarith) (by linarith)
  nlinarith

end SinkTransport

theorem sink_discounted_order_lib {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (ι : V → V) (sink : V) (hSink : IsSinkGame G ι sink)
    (σ : V → V) (hσ : Legal G false σ)
    (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v)) (v w : V) :
    ValueLT G (value G σ v) (value G σ w) ↔
      FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ v <
      FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ w := by
  let H := FriedmannDiscounted.induced G
  have hG := isSinkGame_wellFormed hSink
  have hH := isSinkGame_wellFormed_induced hSink
  have hcp_val : ∀ u, (value G σ u).cyclePriority = 1 :=
    hSink.2.2.2.2.2.2 σ hσ hAbove
  rcases exists_optimalCounterstrategy G hG σ with ⟨τ_star, hτ_star⟩
  have hval_eq : ∀ u, value G σ u = playValue G σ τ_star u :=
    value_eq_playValue_of_optimalCounterstrategy hG hτ_star
  have hcp_star : ∀ u, (playValue G σ τ_star u).cyclePriority = 1 := by
    intro u
    rw [← hval_eq u]
    exact hcp_val u
  rcases exists_disc_optimalCounterstrategy hH σ with ⟨ϱ, hϱ_leg, hϱ_min, hϱ_val⟩
  have hcp_ϱ : ∀ u, (playValue G σ ϱ u).cyclePriority = 1 := by
    intro u
    have hle_u : ValueLE G (playValue G σ τ_star u) (playValue G σ ϱ u) :=
      hτ_star.2 u ϱ hϱ_leg
    have hrew_ge : reward 1 ≤ reward (playValue G σ ϱ u).cyclePriority := by
      have h := reward_cyclePriority_le_of_valueLE hle_u
      rwa [hcp_star u] at h
    by_contra hne_one
    have hcl_ne : cycleLeader G σ ϱ u ≠ sink := by
      intro hcl
      apply hne_one
      rw [playValue_cyclePriority_eq_priority_cycleLeader, hcl, isSinkGame_priority_sink hSink]
    have hneg := discounted_playValue_lt_zero_of_cyclePriority_eq_one hSink (hcp_star u)
    have hpos := zero_lt_discounted_playValue_of_cycleLeader_ne_sink hSink hrew_ge hcl_ne
    have hmin_u := hϱ_min u τ_star hτ_star.1
    linarith
  have hpath_eq : ∀ u, (playValue G σ τ_star u).path = (playValue G σ ϱ u).path := by
    intro u
    have hle_u : ValueLE G (playValue G σ τ_star u) (playValue G σ ϱ u) :=
      hτ_star.2 u ϱ hϱ_leg
    rcases hle_u with heq | hlt
    · rw [heq]
    · exfalso
      rw [valueLT_iff_setLT_of_cyclePriority_eq_one hSink (hcp_star u) (hcp_ϱ u)] at hlt
      have hlt_disc := discounted_playValue_lt_of_setLT hSink (hcp_star u) (hcp_ϱ u) hlt
      have hmin_u := hϱ_min u τ_star hτ_star.1
      linarith
  rw [hval_eq v, hval_eq w, hϱ_val v, hϱ_val w]
  rw [valueLT_iff_setLT_of_cyclePriority_eq_one hSink (hcp_star v) (hcp_star w)]
  rw [hpath_eq v, hpath_eq w]
  constructor
  · intro hset
    exact discounted_playValue_lt_of_setLT hSink (hcp_ϱ v) (hcp_ϱ w) hset
  · intro hlt_disc
    rcases valueLT_trichotomy hG.2 (playValue G σ ϱ v) (playValue G σ ϱ w) with heq | hlt | hgt
    · exfalso
      have hpath : (playValue G σ ϱ v).path = (playValue G σ ϱ w).path := by rw [heq]
      have hvw := eq_of_playValue_path_eq hSink (hcp_ϱ v) (hcp_ϱ w) hpath
      subst hvw
      exact lt_irrefl _ hlt_disc
    · exact (valueLT_iff_setLT_of_cyclePriority_eq_one hSink (hcp_ϱ v) (hcp_ϱ w)).mp hlt
    · exfalso
      have hset_gt := (valueLT_iff_setLT_of_cyclePriority_eq_one hSink (hcp_ϱ w) (hcp_ϱ v)).mp hgt
      have hgt_disc := discounted_playValue_lt_of_setLT hSink (hcp_ϱ w) (hcp_ϱ v) hset_gt
      linarith

end FriedmannParity

namespace FriedmannDiscounted

open FriedmannParity

end FriedmannDiscounted


