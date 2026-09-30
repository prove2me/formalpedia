-- Prove2me | solution 1 for ArrowDebreu.ThmI.Etilde_equilibrium_is_E_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T21:52:32.611167+00:00
-- url     : https://prove2.me/submissions/6731633f-e703-4b25-bc1a-689f53fb3a21

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmI_economyE
open ArrowDebreu.Shared

open Filter Topology

namespace ArrowDebreu.ThmI

namespace EtildeAux

variable {l m n : ℕ}

/-- Updating a producer's or consumer's action does not change the price. -/
theorem priceOf_update_of_ne (a : Player m n → Fin l → ℝ) (k : Player m n)
    (hk : k ≠ Sum.inr (Sum.inr ())) (v : Fin l → ℝ) :
    priceOf (Function.update a k v) = priceOf a := by
  unfold priceOf
  rw [Function.update_of_ne (Ne.symm hk)]

/-- Updating the price does not change the consumption vectors. -/
theorem consOf_update_price (a : Player m n → Fin l → ℝ) (p : Fin l → ℝ) :
    consOf (Function.update a (Sum.inr (Sum.inr ())) p) = consOf a := by
  funext i
  unfold consOf
  rw [Function.update_of_ne (by simp)]

/-- Updating the price does not change the production plans. -/
theorem prodOf_update_price (a : Player m n → Fin l → ℝ) (p : Fin l → ℝ) :
    prodOf (Function.update a (Sum.inr (Sum.inr ())) p) = prodOf a := by
  funext j
  unfold prodOf
  rw [Function.update_of_ne (by simp)]

/-- Updating the price sets the price. -/
theorem priceOf_update_price (a : Player m n → Fin l → ℝ) (p : Fin l → ℝ) :
    priceOf (Function.update a (Sum.inr (Sum.inr ())) p) = p := by
  unfold priceOf
  rw [Function.update_self]

/-- The consumer's constraint set of `economyE`, unfolded. -/
theorem mem_constr_cons_iff (E : Economy l m n) (X' : Fin m → Set (Fin l → ℝ))
    (Y' : Fin n → Set (Fin l → ℝ)) (a : Player m n → Fin l → ℝ) (i : Fin m) (x : Fin l → ℝ) :
    x ∈ (economyE E X' Y').constr (Sum.inl i) a ↔
      x ∈ X' i ∧ priceOf a ⬝ᵥ x ≤
        priceOf a ⬝ᵥ E.ζ i + max 0 (∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j)) :=
  Iff.rfl

/-- The market participant's optimality at an equilibrium point of `economyE E X' Y'`. -/
theorem market_optimal (E : Economy l m n) (X' : Fin m → Set (Fin l → ℝ))
    (Y' : Fin n → Set (Fin l → ℝ)) (a : Player m n → Fin l → ℝ)
    (ha : (economyE E X' Y').IsEquilibriumPoint a) (p : Fin l → ℝ) (hp : p ∈ priceSimplex l) :
    p ⬝ᵥ excessDemand E (consOf a) (prodOf a) ≤
      priceOf a ⬝ᵥ excessDemand E (consOf a) (prodOf a) := by
  have h := (ha.2 (Sum.inr (Sum.inr ()))).2 p hp
  change priceOf (Function.update a (Sum.inr (Sum.inr ())) p) ⬝ᵥ
      excessDemand E (consOf (Function.update a (Sum.inr (Sum.inr ())) p))
        (prodOf (Function.update a (Sum.inr (Sum.inr ())) p)) ≤
      priceOf a ⬝ᵥ excessDemand E (consOf a) (prodOf a) at h
  rwa [consOf_update_price, prodOf_update_price, priceOf_update_price] at h

/-- Producer `j`'s optimality at an equilibrium point of `economyE E X' Y'`. -/
theorem producer_optimal (E : Economy l m n) (X' : Fin m → Set (Fin l → ℝ))
    (Y' : Fin n → Set (Fin l → ℝ)) (a : Player m n → Fin l → ℝ)
    (ha : (economyE E X' Y').IsEquilibriumPoint a) (j : Fin n) (y : Fin l → ℝ) (hy : y ∈ Y' j) :
    priceOf a ⬝ᵥ y ≤ priceOf a ⬝ᵥ a (Sum.inr (Sum.inl j)) := by
  have h := (ha.2 (Sum.inr (Sum.inl j))).2 y hy
  change priceOf (Function.update a (Sum.inr (Sum.inl j)) y) ⬝ᵥ
      (Function.update a (Sum.inr (Sum.inl j)) y) (Sum.inr (Sum.inl j)) ≤
      priceOf a ⬝ᵥ a (Sum.inr (Sum.inl j)) at h
  rwa [priceOf_update_of_ne a _ (by simp), Function.update_self] at h

/-- Consumer `i`'s optimality at an equilibrium point of `economyE E X' Y'`. -/
theorem consumer_optimal (E : Economy l m n) (X' : Fin m → Set (Fin l → ℝ))
    (Y' : Fin n → Set (Fin l → ℝ)) (a : Player m n → Fin l → ℝ)
    (ha : (economyE E X' Y').IsEquilibriumPoint a) (i : Fin m) (x : Fin l → ℝ)
    (hx : x ∈ (economyE E X' Y').constr (Sum.inl i) a) :
    E.u i x ≤ E.u i (a (Sum.inl i)) := by
  have h := (ha.2 (Sum.inl i)).2 x hx
  change E.u i ((Function.update a (Sum.inl i) x) (Sum.inl i)) ≤ E.u i (a (Sum.inl i)) at h
  rwa [Function.update_self] at h

/-- Profits are nonnegative at an equilibrium point when `0 ∈ Y'_j`. -/
theorem profit_nonneg (E : Economy l m n) (X' : Fin m → Set (Fin l → ℝ))
    (Y' : Fin n → Set (Fin l → ℝ)) (a : Player m n → Fin l → ℝ)
    (ha : (economyE E X' Y').IsEquilibriumPoint a) (j : Fin n) (h0 : (0 : Fin l → ℝ) ∈ Y' j) :
    0 ≤ priceOf a ⬝ᵥ prodOf a j := by
  have := producer_optimal E X' Y' a ha j 0 h0
  rwa [dotProduct_zero] at this

/-- The budget inequality of consumer `i` at an equilibrium point. -/
theorem budget_ineq (E : Economy l m n) (X' : Fin m → Set (Fin l → ℝ))
    (Y' : Fin n → Set (Fin l → ℝ)) (a : Player m n → Fin l → ℝ)
    (ha : (economyE E X' Y').IsEquilibriumPoint a) (i : Fin m) :
    priceOf a ⬝ᵥ a (Sum.inl i) ≤
      priceOf a ⬝ᵥ E.ζ i + max 0 (∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j)) :=
  ((mem_constr_cons_iff E X' Y' a i _).1 (ha.2 (Sum.inl i)).1).2

/-- The unit vector `e_h` lies in the price simplex. -/
theorem single_mem_priceSimplex (h : Fin l) :
    (Pi.single h (1:ℝ) : Fin l → ℝ) ∈ priceSimplex l := by
  refine ⟨?_, ?_⟩
  · intro k
    by_cases hk : k = h
    · subst hk; simp
    · simp [hk]
  · simp

/-- `z^* ≦ 0` at an equilibrium point of `economyE E X' Y'` when `0 ∈ Y'_j` for all `j`
(the argument (1) of §3.2). -/
theorem excess_nonpos (E : Economy l m n) (X' : Fin m → Set (Fin l → ℝ))
    (Y' : Fin n → Set (Fin l → ℝ)) (hIVb : AssumptionIVb E) (a : Player m n → Fin l → ℝ)
    (ha : (economyE E X' Y').IsEquilibriumPoint a) (h0 : ∀ j, (0 : Fin l → ℝ) ∈ Y' j) :
    excessDemand E (consOf a) (prodOf a) ≤ 0 := by
  have hprof : ∀ i, 0 ≤ ∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j) := fun i =>
    Finset.sum_nonneg (fun j _ => mul_nonneg (hIVb.1 i j) (profit_nonneg E X' Y' a ha j (h0 j)))
  have hsum : ∑ i, priceOf a ⬝ᵥ consOf a i ≤
      ∑ i, (priceOf a ⬝ᵥ E.ζ i + ∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j)) := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    have := budget_ineq E X' Y' a ha i
    rwa [max_eq_right (hprof i)] at this
  have hz : priceOf a ⬝ᵥ excessDemand E (consOf a) (prodOf a) ≤ 0 := by
    unfold excessDemand
    rw [dotProduct_sub, dotProduct_sub, dotProduct_sum, dotProduct_sum, dotProduct_sum]
    rw [Finset.sum_add_distrib, Finset.sum_comm] at hsum
    have h2 : ∑ j, ∑ i, E.α i j * (priceOf a ⬝ᵥ prodOf a j) = ∑ j, priceOf a ⬝ᵥ prodOf a j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Finset.sum_mul, hIVb.2 j, one_mul]
    rw [h2] at hsum
    linarith
  intro h
  have hm := market_optimal E X' Y' a ha (Pi.single h 1) (single_mem_priceSimplex h)
  rw [single_dotProduct, one_mul] at hm
  exact le_trans hm hz

/-- The cube of §3.3.3 is the closed ball of radius `c` for the sup norm. -/
theorem cube_eq_closedBall (l : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    cube l c = Metric.closedBall (0 : Fin l → ℝ) c := by
  ext x
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hc]
  constructor
  · intro h i
    rw [Real.norm_eq_abs]
    exact h i
  · intro h i
    rw [← Real.norm_eq_abs]
    exact h i

theorem zero_mem_cube (l : ℕ) {c : ℝ} (hc : 0 ≤ c) : (0 : Fin l → ℝ) ∈ cube l c := by
  intro h
  simp [hc]

theorem isClosed_cube (l : ℕ) {c : ℝ} (hc : 0 ≤ c) : IsClosed (cube l c) := by
  rw [cube_eq_closedBall l hc]
  exact Metric.isClosed_closedBall

theorem isCompact_cube (l : ℕ) {c : ℝ} (hc : 0 ≤ c) : IsCompact (cube l c) := by
  rw [cube_eq_closedBall l hc]
  exact isCompact_closedBall _ _

theorem convex_cube (l : ℕ) {c : ℝ} (hc : 0 ≤ c) : Convex ℝ (cube l c) := by
  rw [cube_eq_closedBall l hc]
  exact convex_closedBall _ _

/-- Points of an open set: moving a little from `x₀ ∈ U` towards any `x` stays in `U`. -/
theorem exists_segment_mem_open {U : Set (Fin l → ℝ)} (hU : IsOpen U) {x₀ : Fin l → ℝ}
    (hx₀ : x₀ ∈ U) (x : Fin l → ℝ) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ t • x + (1 - t) • x₀ ∈ U := by
  have hcont : Continuous (fun t : ℝ => t • x + (1 - t) • x₀) := by fun_prop
  have hx₀' : (fun t : ℝ => t • x + (1 - t) • x₀) 0 ∈ U := by simpa using hx₀
  have hev : ∀ᶠ t in 𝓝 (0:ℝ), t • x + (1 - t) • x₀ ∈ U :=
    hcont.continuousAt.eventually_mem (hU.mem_nhds hx₀')
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  have htpos : 0 < min (ε / 2) (1 / 2) := lt_min (half_pos hε) (by norm_num)
  refine ⟨min (ε / 2) (1 / 2), htpos, lt_of_le_of_lt (min_le_right _ _) (by norm_num), hball ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos htpos]
  exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)

end EtildeAux

end ArrowDebreu.ThmI
open ArrowDebreu.ThmI ArrowDebreu.ThmI.EtildeAux
open ArrowDebreu.Shared

theorem solution {l m n : ℕ} (E : Economy l m n)
    (hE : AssumptionsItoIV E) (c : ℝ) (hc : 0 < c)
    (hX : ∀ i, Xhat E i ⊆ interior (cube l c)) (hY : ∀ j, Yhat E j ⊆ interior (cube l c))
    (a : Player m n → Fin l → ℝ) (ha : (economyEtilde E c).IsEquilibriumPoint a) :
    (economyE E E.X E.Y).IsEquilibriumPoint a := by
  have h0C : (0 : Fin l → ℝ) ∈ cube l c := zero_mem_cube l hc.le
  have ha' : (economyE E (fun i => E.X i ∩ cube l c)
      (fun j => E.Y j ∩ cube l c)).IsEquilibriumPoint a := ha
  have hprof : ∀ k, a k ∈ (economyE E (fun i => E.X i ∩ cube l c)
      (fun j => E.Y j ∩ cube l c)).act k :=
    fun k => Set.mem_univ_pi.1 ha'.1 k
  have hxX : ∀ i, a (Sum.inl i) ∈ E.X i := fun i => (hprof (Sum.inl i)).1
  have hyY : ∀ j, a (Sum.inr (Sum.inl j)) ∈ E.Y j := fun j => (hprof (Sum.inr (Sum.inl j))).1
  have hpP : a (Sum.inr (Sum.inr ())) ∈ priceSimplex l := hprof (Sum.inr (Sum.inr ()))
  have hz : excessDemand E (consOf a) (prodOf a) ≤ 0 :=
    excess_nonpos E _ _ hE.IVb a ha' (fun j => ⟨(hE.Ia j).2.2, h0C⟩)
  have hxint : ∀ i, a (Sum.inl i) ∈ interior (cube l c) :=
    fun i => hX i ⟨hxX i, consOf a, prodOf a, rfl, hxX, hyY, hz⟩
  have hyint : ∀ j, a (Sum.inr (Sum.inl j)) ∈ interior (cube l c) :=
    fun j => hY j ⟨hyY j, consOf a, prodOf a, rfl, hxX, hyY, hz⟩
  refine ⟨?_, ?_⟩
  · refine Set.mem_univ_pi.2 (fun k => ?_)
    rcases k with i | j | u
    · exact hxX i
    · exact hyY j
    · exact hpP
  · intro k
    rcases k with i | j | u
    · -- consumer `i`
      refine ⟨?_, ?_⟩
      · have hm := (ha'.2 (Sum.inl i)).1
        rw [mem_constr_cons_iff] at hm ⊢
        exact ⟨hm.1.1, hm.2⟩
      · intro x hx
        rw [mem_constr_cons_iff] at hx
        change E.u i ((Function.update a (Sum.inl i) x) (Sum.inl i)) ≤ E.u i (a (Sum.inl i))
        rw [Function.update_self]
        by_contra hlt
        rw [not_le] at hlt
        obtain ⟨t, ht0, ht1, htU⟩ := exists_segment_mem_open isOpen_interior (hxint i) x
        have hxt := hE.IIIc i x hx.1 (a (Sum.inl i)) (hxX i) hlt t ht0 ht1
        have hmem : t • x + (1 - t) • a (Sum.inl i) ∈ (economyE E (fun i => E.X i ∩ cube l c)
            (fun j => E.Y j ∩ cube l c)).constr (Sum.inl i) a := by
          rw [mem_constr_cons_iff]
          refine ⟨⟨(hE.II i).2.1 hx.1 (hxX i) ht0.le (by linarith) (by ring),
            interior_subset htU⟩, ?_⟩
          rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
          have h1 := hx.2
          have h2 := budget_ineq E _ _ a ha' i
          have h3 := mul_le_mul_of_nonneg_left h1 ht0.le
          have h4 := mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ 1 - t)
          linarith
        have := consumer_optimal E _ _ a ha' i _ hmem
        exact absurd (lt_of_lt_of_le hxt this) (lt_irrefl _)
    · -- producer `j`
      refine ⟨(ha'.2 (Sum.inr (Sum.inl j))).1.1, ?_⟩
      intro y hy
      change priceOf (Function.update a (Sum.inr (Sum.inl j)) y) ⬝ᵥ
        (Function.update a (Sum.inr (Sum.inl j)) y) (Sum.inr (Sum.inl j)) ≤
        priceOf a ⬝ᵥ a (Sum.inr (Sum.inl j))
      rw [priceOf_update_of_ne a _ (by simp), Function.update_self]
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨t, ht0, ht1, htU⟩ := exists_segment_mem_open isOpen_interior (hyint j) y
      have hmem : t • y + (1 - t) • a (Sum.inr (Sum.inl j)) ∈ E.Y j ∩ cube l c :=
        ⟨(hE.Ia j).2.1 hy (hyY j) ht0.le (by linarith) (by ring), interior_subset htU⟩
      have := producer_optimal E _ _ a ha' j _ hmem
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at this
      have hpos := mul_pos ht0 (sub_pos.2 hlt)
      linarith
    · -- the market participant
      exact ha'.2 (Sum.inr (Sum.inr u))

