-- Prove2me | solution 1 for ArrowDebreu.ThmII.competitive_of_price_floor_slack
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T23:47:57.865501+00:00
-- url     : https://prove2.me/submissions/68dc7c93-1520-4ee5-a300-568575e27e84

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_ThmII_AssumptionsII
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmII_economyEeps
open ArrowDebreu.Shared

open ArrowDebreu.Shared ArrowDebreu.ThmII in
theorem solution {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsIIexceptV E)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / (2 * ((productive E).card : ℝ)))
    (a : Player m n → Fin l → ℝ) (ha : (economyEeps E ε).IsEquilibriumPoint a)
    (hslack : ∀ h ∈ productive E, ε < priceOf a h) :
    IsCompetitiveEquilibrium E (consOf a) (prodOf a) (priceOf a) := by
  obtain ⟨hprof, heq⟩ := ha
  -- profile membership
  have hX : ∀ i, consOf a i ∈ E.X i := fun i => hprof (Sum.inl i) (Set.mem_univ _)
  have hY : ∀ j, prodOf a j ∈ E.Y j := fun j => hprof (Sum.inr (Sum.inl j)) (Set.mem_univ _)
  have hPe : priceOf a ∈ priceSimplexEps E ε := hprof (Sum.inr (Sum.inr ())) (Set.mem_univ _)
  obtain ⟨⟨hp0, hp1⟩, hpe⟩ := hPe
  -- producers maximise
  have hprod : ∀ j, ∀ y' ∈ E.Y j, priceOf a ⬝ᵥ y' ≤ priceOf a ⬝ᵥ prodOf a j := by
    intro j y' hy'
    have h := (heq (Sum.inr (Sum.inl j))).2 y' hy'
    simpa [economyEeps, economyE, priceOf, prodOf, Function.update_of_ne] using h
  have hy0 : ∀ j, 0 ≤ priceOf a ⬝ᵥ prodOf a j := by
    intro j
    have := hprod j 0 (hE.Ia j).2.2
    simpa using this
  -- consumers
  have hcons1 : ∀ i, consOf a i ∈ E.X i ∧ priceOf a ⬝ᵥ consOf a i ≤
      priceOf a ⬝ᵥ E.ζ i + max 0 (∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j)) := by
    intro i
    exact (heq (Sum.inl i)).1
  have hmax : ∀ i, max 0 (∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j)) =
      ∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j) := by
    intro i
    exact max_eq_right (Finset.sum_nonneg fun j _ => mul_nonneg (hE.IVb.1 i j) (hy0 j))
  have hbud : ∀ i, consOf a i ∈ budgetSet E (priceOf a) (prodOf a) i := by
    intro i
    refine ⟨(hcons1 i).1, ?_⟩
    have := (hcons1 i).2
    rw [hmax] at this
    simpa [income] using this
  have hopt : ∀ i, ∀ x' ∈ budgetSet E (priceOf a) (prodOf a) i, E.u i x' ≤ E.u i (consOf a i) := by
    intro i x' hx'
    have h := (heq (Sum.inl i)).2 x' (by
      refine ⟨hx'.1, ?_⟩
      rw [hmax]
      simpa [income] using hx'.2)
    simpa [economyEeps, economyE, consOf, Function.update_of_ne] using h
  -- market participant
  have hmkt : ∀ q ∈ priceSimplexEps E ε,
      q ⬝ᵥ excessDemand E (consOf a) (prodOf a) ≤ priceOf a ⬝ᵥ excessDemand E (consOf a) (prodOf a) := by
    intro q hq
    have h := (heq (Sum.inr (Sum.inr ()))).2 q hq
    have e1 : consOf (Function.update a (Sum.inr (Sum.inr ())) q) = consOf a := by
      funext i; simp [consOf]
    have e2 : prodOf (Function.update a (Sum.inr (Sum.inr ())) q) = prodOf a := by
      funext j; simp [prodOf]
    have e3 : priceOf (Function.update a (Sum.inr (Sum.inr ())) q) = q := by
      simp [priceOf]
    simpa [economyEeps, economyE, e1, e2, e3] using h
  -- local-to-global in the price simplex
  have hglob : ∀ q ∈ priceSimplex l,
      q ⬝ᵥ excessDemand E (consOf a) (prodOf a) ≤ priceOf a ⬝ᵥ excessDemand E (consOf a) (prodOf a) := by
    intro q hq
    obtain ⟨hq0, hq1⟩ := hq
    have h1 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < t := self_mem_nhdsWithin
    have h2 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), t < 1 :=
      nhdsWithin_le_nhds (eventually_lt_nhds one_pos)
    have h3 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
        ∀ h ∈ productive E, ε ≤ priceOf a h + t * (q h - priceOf a h) := by
      rw [Filter.eventually_all_finset]
      intro h hh
      have hc : Continuous (fun t : ℝ => priceOf a h + t * (q h - priceOf a h)) := by fun_prop
      have hlt : ε < priceOf a h + (0:ℝ) * (q h - priceOf a h) := by simpa using hslack h hh
      have := (hc.tendsto 0).eventually (eventually_gt_nhds hlt)
      exact (this.filter_mono nhdsWithin_le_nhds).mono fun t ht => ht.le
    obtain ⟨t, ht0, ht1, ht3⟩ := (h1.and (h2.and h3)).exists
    have hmem : priceOf a + t • (q - priceOf a) ∈ priceSimplexEps E ε := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro h
        have := hp0 h
        have := hq0 h
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        nlinarith
      · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hp1, hq1]
        ring
      · intro h hh
        simpa using ht3 h hh
    have := hmkt _ hmem
    rw [add_dotProduct, smul_dotProduct, sub_dotProduct, smul_eq_mul] at this
    nlinarith
  -- Walras / budget exhaustion
  have hexh : ∀ i, priceOf a ⬝ᵥ consOf a i = income E (priceOf a) (prodOf a) i := by
    intro i
    by_contra hne
    have hle : priceOf a ⬝ᵥ consOf a i ≤ income E (priceOf a) (prodOf a) i := (hbud i).2
    have hlt : priceOf a ⬝ᵥ consOf a i < income E (priceOf a) (prodOf a) i := lt_of_le_of_ne hle hne
    obtain ⟨x', hx'X, hx'u⟩ := hE.IIIb i (consOf a i) (hX i)
    set gap := income E (priceOf a) (prodOf a) i - priceOf a ⬝ᵥ consOf a i with hgap
    have hgap0 : 0 < gap := by rw [hgap]; linarith
    set d := |priceOf a ⬝ᵥ x' - priceOf a ⬝ᵥ consOf a i| with hd
    have hd0 : 0 ≤ d := abs_nonneg _
    set t := min (1/2 : ℝ) (gap / (d + 1)) with ht
    have ht0 : 0 < t := lt_min (by norm_num) (div_pos hgap0 (by linarith))
    have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have htg : t * (d + 1) ≤ gap := by
      have : t ≤ gap / (d + 1) := min_le_right _ _
      rwa [le_div_iff₀ (by linarith)] at this
    have hmem : t • x' + (1 - t) • consOf a i ∈ E.X i :=
      (hE.II i).2.1 hx'X (hX i) ht0.le (sub_nonneg.2 ht1.le) (by ring)
    have hu : E.u i (consOf a i) < E.u i (t • x' + (1 - t) • consOf a i) :=
      hE.IIIc i x' hx'X (consOf a i) (hX i) hx'u t ht0 ht1
    have hbud' : t • x' + (1 - t) • consOf a i ∈ budgetSet E (priceOf a) (prodOf a) i := by
      refine ⟨hmem, ?_⟩
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      have hdd : priceOf a ⬝ᵥ x' - priceOf a ⬝ᵥ consOf a i ≤ d := le_abs_self _
      have : t * (priceOf a ⬝ᵥ x' - priceOf a ⬝ᵥ consOf a i) ≤ t * d := mul_le_mul_of_nonneg_left hdd ht0.le
      nlinarith
    exact absurd (hopt i _ hbud') (not_le.2 hu)
  have hsum_alpha : ∑ i, ∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j) = ∑ j, priceOf a ⬝ᵥ prodOf a j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, hE.IVb.2 j, one_mul]
  have hpz : priceOf a ⬝ᵥ excessDemand E (consOf a) (prodOf a) = 0 := by
    have e : priceOf a ⬝ᵥ excessDemand E (consOf a) (prodOf a) =
        ∑ i, priceOf a ⬝ᵥ consOf a i - ∑ j, priceOf a ⬝ᵥ prodOf a j - ∑ i, priceOf a ⬝ᵥ E.ζ i := by
      simp only [excessDemand, dotProduct_sub, dotProduct_sum]
    rw [e]
    have : ∑ i, priceOf a ⬝ᵥ consOf a i =
        ∑ i, priceOf a ⬝ᵥ E.ζ i + ∑ i, ∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [hexh i]; rfl
    rw [this, hsum_alpha]; ring
  refine ⟨?_, ?_, ⟨hp0, hp1⟩, ?_, hpz⟩
  · intro j
    exact ⟨hY j, hprod j⟩
  · intro i
    exact ⟨hbud i, hopt i⟩
  · intro h
    have hh := hglob (Pi.single h 1) ⟨fun k => by by_cases hk : k = h <;> simp [hk],
      by simp⟩
    rw [hpz] at hh
    simpa using hh
