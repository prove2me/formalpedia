-- Prove2me | solution 1 for ArrowDebreu.ThmII.eqPoint_EtildeEps_is_eqPoint_Eeps
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-18T07:36:13.466921+00:00
-- url     : https://prove2.me/submissions/be52eb0b-f473-427c-8ce2-7dec46adf1c1

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_ThmII_AssumptionsII
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmII_economyEeps
open ArrowDebreu.Shared

set_option autoImplicit false

/-- A point of the interior of `S` can be moved a little towards any `b` while staying in `S`. -/
theorem P2M0566_near_mem {l : ℕ} {S : Set (Fin l → ℝ)} {x : Fin l → ℝ} (hx : x ∈ interior S)
    (b : Fin l → ℝ) : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ t • b + (1 - t) • x ∈ S := by
  have hc : Continuous (fun t : ℝ => t • b + (1 - t) • x) := by fun_prop
  have h3 : ∀ᶠ t in nhds (0:ℝ), t • b + (1 - t) • x ∈ S := by
    have := hc.tendsto 0
    simp only [zero_smul, sub_zero, one_smul, zero_add] at this
    exact this (mem_interior_iff_mem_nhds.1 hx)
  have h1 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < t := self_mem_nhdsWithin
  have h2 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), t < 1 :=
    nhdsWithin_le_nhds (eventually_lt_nhds one_pos)
  obtain ⟨t, ht0, ht1, ht3⟩ := (h1.and (h2.and (h3.filter_mono nhdsWithin_le_nhds))).exists
  exact ⟨t, ht0, ht1, ht3⟩

open ArrowDebreu.Shared ArrowDebreu.ThmII in
theorem solution {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsIIexceptV E)
    (ξ : Fin m → Fin l → ℝ) (hξ : ∀ i, ∀ x ∈ E.X i, ξ i ≤ x)
    (c' : ℝ) (hc' : 0 < c')
    (hX : ∀ i, XhatPrime E ξ i ⊆ interior (cube l c'))
    (hY : ∀ j, YhatPrime E ξ j ⊆ interior (cube l c'))
    (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / (2 * ((productive E).card : ℝ)))
    (a : Player m n → Fin l → ℝ) (ha : (economyEtildeEps E ε c').IsEquilibriumPoint a) :
    (economyEeps E ε).IsEquilibriumPoint a := by
  classical
  obtain ⟨hprof, heq⟩ := ha
  have hXc : ∀ i, consOf a i ∈ E.X i ∩ cube l c' := fun i => hprof (Sum.inl i) (Set.mem_univ _)
  have hYc : ∀ j, prodOf a j ∈ E.Y j ∩ cube l c' :=
    fun j => hprof (Sum.inr (Sum.inl j)) (Set.mem_univ _)
  have hPe : priceOf a ∈ priceSimplexEps E ε := hprof (Sum.inr (Sum.inr ())) (Set.mem_univ _)
  have h0c : (0 : Fin l → ℝ) ∈ cube l c' := by
    intro h
    simp [hc'.le]
  -- producers maximise over the truncated sets
  have hprodC : ∀ j, ∀ y' ∈ E.Y j ∩ cube l c', priceOf a ⬝ᵥ y' ≤ priceOf a ⬝ᵥ prodOf a j := by
    intro j y' hy'
    have h := (heq (Sum.inr (Sum.inl j))).2 y' hy'
    simpa [economyEtildeEps, economyE, priceOf, prodOf, Function.update_of_ne] using h
  have hy0 : ∀ j, 0 ≤ priceOf a ⬝ᵥ prodOf a j := by
    intro j
    have := hprodC j 0 ⟨(hE.Ia j).2.2, h0c⟩
    simpa using this
  have hcons1 : ∀ i, priceOf a ⬝ᵥ consOf a i ≤
      priceOf a ⬝ᵥ E.ζ i + max 0 (∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j)) := by
    intro i
    exact (heq (Sum.inl i)).1.2
  have hmax : ∀ i, max 0 (∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j)) =
      ∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j) := by
    intro i
    exact max_eq_right (Finset.sum_nonneg fun j _ => mul_nonneg (hE.IVb.1 i j) (hy0 j))
  have hbud : ∀ i, priceOf a ⬝ᵥ consOf a i ≤
      priceOf a ⬝ᵥ E.ζ i + ∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j) := by
    intro i
    have := hcons1 i
    rwa [hmax] at this
  have hsum_alpha : ∑ i, ∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j) =
      ∑ j, priceOf a ⬝ᵥ prodOf a j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, hE.IVb.2 j, one_mul]
  have hpz : priceOf a ⬝ᵥ excessDemand E (consOf a) (prodOf a) ≤ 0 := by
    have e : priceOf a ⬝ᵥ excessDemand E (consOf a) (prodOf a) =
        ∑ i, priceOf a ⬝ᵥ consOf a i - ∑ j, priceOf a ⬝ᵥ prodOf a j -
          ∑ i, priceOf a ⬝ᵥ E.ζ i := by
      simp only [excessDemand, dotProduct_sub, dotProduct_sum]
    rw [e]
    have := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hbud i
    rw [Finset.sum_add_distrib, hsum_alpha] at this
    linarith
  -- market participant
  have hmkt : ∀ q ∈ priceSimplexEps E ε,
      q ⬝ᵥ excessDemand E (consOf a) (prodOf a) ≤
        priceOf a ⬝ᵥ excessDemand E (consOf a) (prodOf a) := by
    intro q hq
    have h := (heq (Sum.inr (Sum.inr ()))).2 q hq
    have e1 : consOf (Function.update a (Sum.inr (Sum.inr ())) q) = consOf a := by
      funext i; simp [consOf]
    have e2 : prodOf (Function.update a (Sum.inr (Sum.inr ())) q) = prodOf a := by
      funext j; simp [prodOf]
    have e3 : priceOf (Function.update a (Sum.inr (Sum.inr ())) q) = q := by
      simp [priceOf]
    simpa [economyEtildeEps, economyE, e1, e2, e3] using h
  -- the aggregate bound x - y ≤ ζ'
  set c : ℝ := ((productive E).card : ℝ) with hcdef
  have hP : 0 < c := by
    rw [hcdef]; exact_mod_cast Finset.card_pos.2 hE.VII
  have h2 : 2 * c * ε ≤ 1 := by
    have := (le_div_iff₀ (by positivity)).1 hε'
    linarith
  have hξζ : ∀ i k, ξ i k ≤ E.ζ i k := by
    intro i k
    obtain ⟨x0, hx0, hle, -⟩ := hE.IVa' i
    exact (hξ i x0 hx0 k).trans (hle k)
  have hT : ∀ k, totalEndowment E k = ∑ i, E.ζ i k := by
    intro k; simp [totalEndowment, Finset.sum_apply]
  set S : ℝ := ∑ k ∈ productive E, (totalEndowment E k - ∑ i, ξ i k) with hSdef
  have hS : 0 ≤ S := by
    refine Finset.sum_nonneg fun k _ => ?_
    rw [hT k, sub_nonneg]
    exact Finset.sum_le_sum fun i _ => hξζ i k
  set z := excessDemand E (consOf a) (prodOf a) with hzdef
  have hzk : ∀ k ∈ productive E, ∑ i, ξ i k - totalEndowment E k ≤ z k := by
    intro k hk
    have hyk : (∑ j, prodOf a j) k ≤ 0 :=
      ((mem_productive E k).1 hk _ ⟨prodOf a, fun j => (hYc j).1, rfl⟩).1
    have hxk : ∑ i, ξ i k ≤ (∑ i, consOf a i) k := by
      rw [Finset.sum_apply]
      exact Finset.sum_le_sum fun i _ => hξ i _ (hXc i).1 k
    have : z k = (∑ i, consOf a i) k - (∑ j, prodOf a j) k - totalEndowment E k := rfl
    linarith
  have hsumz : -S ≤ ∑ k ∈ productive E, z k := by
    have := Finset.sum_le_sum hzk
    have e : ∑ k ∈ productive E, (∑ i, ξ i k - totalEndowment E k) = -S := by
      rw [hSdef, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    linarith
  have hbound : ∑ i', consOf a i' - ∑ j, prodOf a j ≤ zetaPrime E ξ := by
    intro h
    let q : Fin l → ℝ := fun k =>
      (if k ∈ productive E then ε else 0) + (1 - c * ε) * (Pi.single h (1:ℝ) : Fin l → ℝ) k
    have hsing : ∀ k, 0 ≤ (Pi.single h (1:ℝ) : Fin l → ℝ) k := by
      intro k; by_cases hk : k = h <;> simp [hk]
    have hq : q ∈ priceSimplexEps E ε := by
      refine ⟨⟨fun k => ?_, ?_⟩, fun k hk => ?_⟩
      · have h1 : 0 ≤ (if k ∈ productive E then ε else 0) := by
          split_ifs <;> linarith
        have h3 := hsing k
        show (0:ℝ) ≤ (if k ∈ productive E then ε else 0) + (1 - c * ε) * (Pi.single h (1:ℝ) : Fin l → ℝ) k
        nlinarith
      · show ∑ k, ((if k ∈ productive E then ε else 0) + (1 - c * ε) * (Pi.single h (1:ℝ) : Fin l → ℝ) k) = 1
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter,
          Finset.sum_const, nsmul_eq_mul, Finset.sum_pi_single']
        simp only [Finset.mem_univ, if_true, mul_one]
        rw [← hcdef]
        ring
      · have h3 := hsing k
        show ε ≤ (if k ∈ productive E then ε else 0) + (1 - c * ε) * (Pi.single h (1:ℝ) : Fin l → ℝ) k
        rw [if_pos hk]
        nlinarith
    have hqz : q ⬝ᵥ z = ε * ∑ k ∈ productive E, z k + (1 - c * ε) * z h := by
      show ∑ k, ((if k ∈ productive E then ε else 0) + (1 - c * ε) * (Pi.single h (1:ℝ) : Fin l → ℝ) k) * z k = _
      simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_mem,
        Finset.univ_inter, Finset.mul_sum, mul_assoc, Pi.single_apply, ite_mul, one_mul,
        mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hle : q ⬝ᵥ z ≤ 0 := (hmkt q hq).trans hpz
    rw [hqz] at hle
    have key : z h * c ≤ S := by
      by_cases hz : z h ≤ 0
      · nlinarith
      · rw [not_le] at hz
        have h4 : c * ε * z h ≤ (1 - c * ε) * z h := by nlinarith
        have h5 : ε * (-S) ≤ ε * ∑ k ∈ productive E, z k := mul_le_mul_of_nonneg_left hsumz hε.le
        have h6 : ε * (z h * c - S) ≤ 0 := by nlinarith
        have := (mul_nonpos_iff.1 h6)
        rcases this with ⟨_, h7⟩ | ⟨h7, _⟩
        · linarith
        · linarith
    have hzh : z h ≤ 1 / c * S := by
      rw [one_div_mul_eq_div, le_div_iff₀ hP]
      exact key
    have e : (∑ i', consOf a i' - ∑ j, prodOf a j) h = z h + totalEndowment E h := by
      rw [hzdef]
      show _ = (∑ i', consOf a i' - ∑ j, prodOf a j - totalEndowment E) h + totalEndowment E h
      simp
    rw [e]
    show z h + totalEndowment E h ≤ totalEndowment E h + 1 / c * S
    linarith
  have hxint : ∀ i, consOf a i ∈ interior (cube l c') := fun i =>
    hX i ⟨(hXc i).1, consOf a, prodOf a, rfl, fun i' => (hXc i').1, fun j => (hYc j).1, hbound⟩
  have hyint : ∀ j, prodOf a j ∈ interior (cube l c') := fun j =>
    hY j ⟨(hYc j).1, consOf a, prodOf a, rfl, fun i => (hXc i).1, fun j' => (hYc j').1, hbound⟩
  refine ⟨?_, ?_⟩
  · intro k _
    rcases k with i | j | u
    · exact (hXc i).1
    · exact (hYc j).1
    · exact hPe
  · intro k
    rcases k with i | j | u
    · refine ⟨⟨(hXc i).1, hcons1 i⟩, ?_⟩
      intro b hb
      have hbX : b ∈ E.X i := hb.1
      have hbB : priceOf a ⬝ᵥ b ≤
          priceOf a ⬝ᵥ E.ζ i + max 0 (∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j)) := hb.2
      show E.u i (Function.update a (Sum.inl i) b (Sum.inl i)) ≤ E.u i (a (Sum.inl i))
      rw [Function.update_self]
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨t, ht0, ht1, htC⟩ := P2M0566_near_mem (hxint i) b
      have hmemX : t • b + (1 - t) • consOf a i ∈ E.X i :=
        (hE.II i).2.1 hbX (hXc i).1 ht0.le (sub_nonneg.2 ht1.le) (by ring)
      have hu : E.u i (consOf a i) < E.u i (t • b + (1 - t) • consOf a i) :=
        hE.IIIc i b hbX (consOf a i) (hXc i).1 hlt t ht0 ht1
      have hB : priceOf a ⬝ᵥ (t • b + (1 - t) • consOf a i) ≤
          priceOf a ⬝ᵥ E.ζ i + max 0 (∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j)) := by
        rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
        have := hcons1 i
        nlinarith
      have h := (heq (Sum.inl i)).2 (t • b + (1 - t) • consOf a i) ⟨⟨hmemX, htC⟩, hB⟩
      have h' : E.u i (t • b + (1 - t) • consOf a i) ≤ E.u i (consOf a i) := by
        simpa [economyEtildeEps, economyE, consOf] using h
      exact absurd h' (not_le.2 hu)
    · refine ⟨(hYc j).1, ?_⟩
      intro y' hy'
      have hy'Y : y' ∈ E.Y j := hy'
      have e : priceOf (Function.update a (Sum.inr (Sum.inl j)) y') = priceOf a := by
        simp [priceOf]
      show priceOf (Function.update a (Sum.inr (Sum.inl j)) y') ⬝ᵥ
          Function.update a (Sum.inr (Sum.inl j)) y' (Sum.inr (Sum.inl j)) ≤
          priceOf a ⬝ᵥ a (Sum.inr (Sum.inl j))
      rw [e, Function.update_self]
      obtain ⟨t, ht0, ht1, htC⟩ := P2M0566_near_mem (hyint j) y'
      have hmemY : t • y' + (1 - t) • prodOf a j ∈ E.Y j :=
        (hE.Ia j).2.1 hy'Y (hYc j).1 ht0.le (sub_nonneg.2 ht1.le) (by ring)
      have h := hprodC j _ ⟨hmemY, htC⟩
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h
      have h' : t * (priceOf a ⬝ᵥ y' - priceOf a ⬝ᵥ prodOf a j) ≤ 0 := by
        nlinarith
      have h'' := (mul_nonpos_iff.1 h')
      show priceOf a ⬝ᵥ y' ≤ priceOf a ⬝ᵥ prodOf a j
      rcases h'' with ⟨_, h7⟩ | ⟨h7, _⟩
      · linarith
      · linarith
    · exact heq (Sum.inr (Sum.inr u))
