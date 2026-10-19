-- Prove2me | solution 1 for ArrowDebreu.ThmII.exists_eps_price_floor_slack
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-18T08:10:55.317015+00:00
-- url     : https://prove2.me/submissions/82c3c1a1-b06f-4fa0-899d-2881b0090067

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_ThmII_AssumptionsII
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmII_economyEeps
import Theorems.Thm_ArrowDebreu_ThmII_EtildeEps_has_equilibrium
import Theorems.Thm_ArrowDebreu_ThmII_eqPoint_EtildeEps_is_eqPoint_Eeps
import Theorems.Thm_ArrowDebreu_ThmII_XhatPrime_YhatPrime_bounded
import Theorems.Thm_ArrowDebreu_ThmII_eqPoint_Eeps_le_zetaPrime
import Theorems.Thm_ArrowDebreu_ThmII_limit_expenditure_minimization
open ArrowDebreu.Shared

set_option autoImplicit false

namespace P2Me423

open ArrowDebreu.Shared ArrowDebreu.ThmII Filter Topology

/-- Facts about an equilibrium point of `E^ε`: membership, profit maximisation, and the
aggregate budget identity (Walras' law) obtained from budget exhaustion. -/
lemma eq_facts {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsIIexceptV E) (ε : ℝ)
    (a : Player m n → Fin l → ℝ) (ha : (economyEeps E ε).IsEquilibriumPoint a) :
    (∀ i, consOf a i ∈ E.X i) ∧ (∀ j, prodOf a j ∈ E.Y j) ∧
    priceOf a ∈ priceSimplexEps E ε ∧
    (∀ j, ∀ y' ∈ E.Y j, priceOf a ⬝ᵥ y' ≤ priceOf a ⬝ᵥ prodOf a j) ∧
    priceOf a ⬝ᵥ ∑ i, consOf a i =
      priceOf a ⬝ᵥ ∑ i, E.ζ i + priceOf a ⬝ᵥ ∑ j, prodOf a j := by
  obtain ⟨hprof, heq⟩ := ha
  have hX : ∀ i, consOf a i ∈ E.X i := fun i => hprof (Sum.inl i) (Set.mem_univ _)
  have hY : ∀ j, prodOf a j ∈ E.Y j := fun j => hprof (Sum.inr (Sum.inl j)) (Set.mem_univ _)
  have hPe : priceOf a ∈ priceSimplexEps E ε := hprof (Sum.inr (Sum.inr ())) (Set.mem_univ _)
  have hprod : ∀ j, ∀ y' ∈ E.Y j, priceOf a ⬝ᵥ y' ≤ priceOf a ⬝ᵥ prodOf a j := by
    intro j y' hy'
    have h := (heq (Sum.inr (Sum.inl j))).2 y' hy'
    simpa [economyEeps, economyE, priceOf, prodOf, Function.update_of_ne] using h
  have hy0 : ∀ j, 0 ≤ priceOf a ⬝ᵥ prodOf a j := by
    intro j
    have := hprod j 0 (hE.Ia j).2.2
    simpa using this
  have hmax : ∀ i, max 0 (∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j)) =
      ∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j) := by
    intro i
    exact max_eq_right (Finset.sum_nonneg fun j _ => mul_nonneg (hE.IVb.1 i j) (hy0 j))
  have hbud : ∀ i, priceOf a ⬝ᵥ consOf a i ≤
      priceOf a ⬝ᵥ E.ζ i + ∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j) := by
    intro i
    have h : consOf a i ∈ E.X i ∧ priceOf a ⬝ᵥ consOf a i ≤
        priceOf a ⬝ᵥ E.ζ i + max 0 (∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j)) :=
      (heq (Sum.inl i)).1
    rw [hmax] at h
    exact h.2
  have hopt : ∀ i, ∀ x' ∈ E.X i, priceOf a ⬝ᵥ x' ≤
      priceOf a ⬝ᵥ E.ζ i + ∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j) →
      E.u i x' ≤ E.u i (consOf a i) := by
    intro i x' hx' hb
    have h := (heq (Sum.inl i)).2 x' (by
      refine ⟨hx', ?_⟩
      rw [hmax]
      exact hb)
    simpa [economyEeps, economyE, consOf, Function.update_of_ne] using h
  have hexh : ∀ i, priceOf a ⬝ᵥ consOf a i =
      priceOf a ⬝ᵥ E.ζ i + ∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j) := by
    intro i
    by_contra hne
    have hlt := lt_of_le_of_ne (hbud i) hne
    obtain ⟨x', hx'X, hx'u⟩ := hE.IIIb i (consOf a i) (hX i)
    set gap := priceOf a ⬝ᵥ E.ζ i + ∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j) -
      priceOf a ⬝ᵥ consOf a i with hgap
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
    have hb' : priceOf a ⬝ᵥ (t • x' + (1 - t) • consOf a i) ≤
        priceOf a ⬝ᵥ E.ζ i + ∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j) := by
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      have hdd : priceOf a ⬝ᵥ x' - priceOf a ⬝ᵥ consOf a i ≤ d := le_abs_self _
      have : t * (priceOf a ⬝ᵥ x' - priceOf a ⬝ᵥ consOf a i) ≤ t * d :=
        mul_le_mul_of_nonneg_left hdd ht0.le
      nlinarith
    exact absurd (hopt i _ hmem hb') (not_le.2 hu)
  have hsum_alpha : ∑ i, ∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j) =
      ∑ j, priceOf a ⬝ᵥ prodOf a j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, hE.IVb.2 j, one_mul]
  refine ⟨hX, hY, hPe, hprod, ?_⟩
  rw [dotProduct_sum, dotProduct_sum, dotProduct_sum, ← hsum_alpha, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => hexh i

/-- Equilibrium points of `E^ε` exist for every admissible `ε` (§5.2: truncation, the existence
theorem for `Ẽ^ε`, and removal of the truncation). -/
lemma exists_eq {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsIIexceptV E)
    (ξ : Fin m → Fin l → ℝ) (hξ : ∀ i, ∀ x ∈ E.X i, ξ i ≤ x)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / (2 * ((productive E).card : ℝ))) :
    ∃ a : Player m n → Fin l → ℝ, (economyEeps E ε).IsEquilibriumPoint a := by
  obtain ⟨hXb, hYb⟩ := XhatPrime_YhatPrime_bounded E hE ξ hξ
  have hS : Bornology.IsBounded ((⋃ i, XhatPrime E ξ i) ∪ ⋃ j, YhatPrime E ξ j) :=
    (Bornology.isBounded_iUnion.2 hXb).union (Bornology.isBounded_iUnion.2 hYb)
  obtain ⟨r, hr⟩ := hS.subset_closedBall (0 : Fin l → ℝ)
  set c' : ℝ := max r 0 + 1 with hc'def
  have hc' : 0 < c' := by positivity
  have hball : Metric.ball (0 : Fin l → ℝ) c' ⊆ interior (cube l c') := by
    apply interior_maximal _ Metric.isOpen_ball
    intro x hx h
    have h1 : ‖x h‖ ≤ ‖x‖ := norm_le_pi_norm x h
    rw [Metric.mem_ball, dist_zero_right] at hx
    rw [Real.norm_eq_abs] at h1
    linarith
  have hsub : ∀ x ∈ (⋃ i, XhatPrime E ξ i) ∪ ⋃ j, YhatPrime E ξ j,
      x ∈ interior (cube l c') := by
    intro x hx
    apply hball
    have := hr hx
    rw [Metric.mem_closedBall, dist_zero_right] at this
    rw [Metric.mem_ball, dist_zero_right]
    have : r ≤ max r 0 := le_max_left _ _
    linarith
  have hX : ∀ i, XhatPrime E ξ i ⊆ interior (cube l c') := fun i x hx =>
    hsub x (Or.inl (Set.mem_iUnion.2 ⟨i, hx⟩))
  have hY : ∀ j, YhatPrime E ξ j ⊆ interior (cube l c') := fun j x hx =>
    hsub x (Or.inr (Set.mem_iUnion.2 ⟨j, hx⟩))
  obtain ⟨a, ha⟩ := EtildeEps_has_equilibrium E hE ξ hξ c' hc' hX hY ε hε hε'
  exact ⟨a, eqPoint_EtildeEps_is_eqPoint_Eeps E hE ξ hξ c' hc' hX hY ε hε hε' a ha⟩

/-- The box of profiles whose consumption and production parts are attainable (in `X̂'_i`, `Ŷ'_j`)
and whose price lies in the simplex. -/
def box {l m n : ℕ} (E : Economy l m n) (ξ : Fin m → Fin l → ℝ) :
    Player m n → Set (Fin l → ℝ) :=
  Sum.elim (XhatPrime E ξ) (Sum.elim (YhatPrime E ξ) (fun _ => priceSimplex l))

lemma box_bounded {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsIIexceptV E)
    (ξ : Fin m → Fin l → ℝ) (hξ : ∀ i, ∀ x ∈ E.X i, ξ i ≤ x) :
    Bornology.IsBounded (Set.univ.pi (box E ξ)) := by
  obtain ⟨hXb, hYb⟩ := XhatPrime_YhatPrime_bounded E hE ξ hξ
  have hP : Bornology.IsBounded (priceSimplex l) := by
    rw [Metric.isBounded_iff_subset_closedBall (0 : Fin l → ℝ)]
    refine ⟨1, fun p hp => ?_⟩
    obtain ⟨hp0, hp1⟩ := hp
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro h
    rw [Real.norm_eq_abs, abs_of_nonneg (hp0 h)]
    rw [← hp1]
    exact Finset.single_le_sum (fun k _ => hp0 k) (Finset.mem_univ h)
  apply Bornology.IsBounded.pi
  intro k
  rcases k with i | j | u
  · exact hXb i
  · exact hYb j
  · exact hP

lemma eq_mem_box {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsIIexceptV E)
    (ξ : Fin m → Fin l → ℝ) (hξ : ∀ i, ∀ x ∈ E.X i, ξ i ≤ x)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / (2 * ((productive E).card : ℝ)))
    (a : Player m n → Fin l → ℝ) (ha : (economyEeps E ε).IsEquilibriumPoint a) :
    a ∈ Set.univ.pi (box E ξ) := by
  obtain ⟨hX, hY, hPe, -, -⟩ := eq_facts E hE ε a ha
  have hz := eqPoint_Eeps_le_zetaPrime E hE ξ hξ ε hε hε' a ha
  intro k _
  rcases k with i | j | u
  · exact ⟨hX i, consOf a, prodOf a, rfl, hX, hY, hz⟩
  · exact ⟨hY j, consOf a, prodOf a, rfl, hX, hY, hz⟩
  · exact hPe.1

lemma cont_price {l m n : ℕ} :
    Continuous (fun a : Player m n → Fin l → ℝ => priceOf a) := continuous_apply _

lemma cont_sumcons {l m n : ℕ} :
    Continuous (fun a : Player m n → Fin l → ℝ => ∑ i, consOf a i) :=
  continuous_finsetSum _ fun i _ => continuous_apply _

lemma cont_sumprod {l m n : ℕ} :
    Continuous (fun a : Player m n → Fin l → ℝ => ∑ j, prodOf a j) :=
  continuous_finsetSum _ fun j _ => continuous_apply _

end P2Me423

open ArrowDebreu.Shared ArrowDebreu.ThmII P2Me423 Filter Topology in
theorem solution {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsII E) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / (2 * ((productive E).card : ℝ)) ∧
      ∃ a : Player m n → Fin l → ℝ, (economyEeps E ε).IsEquilibriumPoint a ∧
        ∀ h ∈ productive E, ε < priceOf a h := by
  have hE0 : AssumptionsIIexceptV E := hE.toAssumptionsIIexceptV
  by_contra hcon
  push_neg at hcon
  choose ξ hξ using fun i => (hE0.II i).2.2
  set c : ℝ := 1 / (2 * ((productive E).card : ℝ)) with hcdef
  have hcard : (0 : ℝ) < ((productive E).card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 hE0.VII
  have hc : 0 < c := by positivity
  set εs : ℕ → ℝ := fun k => c * (1 / ((k : ℝ) + 1)) with hεsdef
  have hεs : ∀ k, 0 < εs k ∧ εs k ≤ c := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    refine ⟨by positivity, ?_⟩
    have : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hk]
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    calc εs k = c * (1 / ((k : ℝ) + 1)) := rfl
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left this hc.le
      _ = c := mul_one c
  have hεs0 : Tendsto εs atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul c
    simpa [hεsdef] using this
  choose as has using fun k => exists_eq E hE0 ξ hξ (εs k) (hεs k).1 (hεs k).2
  have hbind : ∀ k, ∃ h ∈ productive E, priceOf (as k) h = εs k := by
    intro k
    obtain ⟨h, hh, hle⟩ := hcon (εs k) (hεs k).1 (hεs k).2 (as k) (has k)
    obtain ⟨-, -, hPe, -, -⟩ := eq_facts E hE0 (εs k) (as k) (has k)
    exact ⟨h, hh, le_antisymm hle (hPe.2 h hh)⟩
  obtain ⟨a0, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (box_bounded E hE0 ξ hξ)
    (fun k => eq_mem_box E hE0 ξ hξ (εs k) (hεs k).1 (hεs k).2 (as k) (has k))
  have hεs' : ∀ k, 0 < (εs ∘ φ) k ∧ (εs ∘ φ) k ≤ 1 / (2 * ((productive E).card : ℝ)) :=
    fun k => hεs (φ k)
  have hlimE := limit_expenditure_minimization E hE0 (εs ∘ φ) hεs'
    (hεs0.comp hφ.tendsto_atTop) (as ∘ φ) (fun k => has (φ k)) a0 hlim (fun k => hbind (φ k))
  have hF : ∀ k, (as ∘ φ) k ∈ {a : Player m n → Fin l → ℝ | priceOf a ∈ priceSimplex l ∧
      priceOf a ⬝ᵥ ∑ i, consOf a i =
        priceOf a ⬝ᵥ ∑ i, E.ζ i + priceOf a ⬝ᵥ ∑ j, prodOf a j ∧
      ∀ j, ∀ y' ∈ E.Y j, priceOf a ⬝ᵥ y' ≤ priceOf a ⬝ᵥ prodOf a j} := by
    intro k
    obtain ⟨-, -, hPe, hprod, hW⟩ := eq_facts E hE0 (εs (φ k)) (as (φ k)) (has (φ k))
    exact ⟨hPe.1, hW, hprod⟩
  have hclosed : IsClosed {a : Player m n → Fin l → ℝ | priceOf a ∈ priceSimplex l ∧
      priceOf a ⬝ᵥ ∑ i, consOf a i =
        priceOf a ⬝ᵥ ∑ i, E.ζ i + priceOf a ⬝ᵥ ∑ j, prodOf a j ∧
      ∀ j, ∀ y' ∈ E.Y j, priceOf a ⬝ᵥ y' ≤ priceOf a ⬝ᵥ prodOf a j} := by
    have hPc : IsClosed (priceSimplex l) := by
      have : priceSimplex l = {p : Fin l → ℝ | 0 ≤ p} ∩ {p | ∑ h, p h = 1} := rfl
      rw [this]
      exact (isClosed_le continuous_const continuous_id).inter
        (isClosed_eq (continuous_finsetSum _ fun h _ => continuous_apply h) continuous_const)
    refine (hPc.preimage cont_price).inter (IsClosed.inter ?_ ?_)
    · exact isClosed_eq (cont_price.dotProduct cont_sumcons)
        ((cont_price.dotProduct continuous_const).add
          (cont_price.dotProduct cont_sumprod))
    · have e : {a : Player m n → Fin l → ℝ |
          ∀ j, ∀ y' ∈ E.Y j, priceOf a ⬝ᵥ y' ≤ priceOf a ⬝ᵥ prodOf a j} =
          ⋂ j, ⋂ y' ∈ E.Y j, {a | priceOf a ⬝ᵥ y' ≤ priceOf a ⬝ᵥ prodOf a j} := by
        ext a; simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      have hc2 : IsClosed (⋂ j, ⋂ y' ∈ E.Y j,
          {a : Player m n → Fin l → ℝ | priceOf a ⬝ᵥ y' ≤ priceOf a ⬝ᵥ prodOf a j}) :=
        isClosed_iInter fun j => isClosed_iInter fun y' => isClosed_iInter fun _ =>
          isClosed_le (cont_price.dotProduct continuous_const)
            (cont_price.dotProduct (continuous_apply _))
      rw [← e] at hc2
      exact hc2
  obtain ⟨⟨hp0, hp1⟩, hW0, hprod0⟩ :=
    hclosed.mem_of_tendsto hlim (Eventually.of_forall hF)
  -- Assumption V
  obtain ⟨x, ⟨xx, hxx, rfl⟩, y, ⟨yy, hyy, rfl⟩, hlt⟩ := hE.V
  set p := priceOf a0 with hpdef
  have h1 : p ⬝ᵥ ∑ i, consOf a0 i ≤ p ⬝ᵥ ∑ i, xx i := by
    rw [dotProduct_sum, dotProduct_sum]
    exact Finset.sum_le_sum fun i _ => (hlimE i).2 (xx i) (hxx i)
  have h2 : p ⬝ᵥ ∑ j, yy j ≤ p ⬝ᵥ ∑ j, prodOf a0 j := by
    rw [dotProduct_sum, dotProduct_sum]
    exact Finset.sum_le_sum fun j _ => hprod0 j (yy j) (hyy j)
  have hne : ∃ h, p h ≠ 0 := by
    by_contra hall
    push_neg at hall
    have : ∑ h, p h = 0 := Finset.sum_eq_zero fun h _ => hall h
    rw [hp1] at this
    exact one_ne_zero this
  obtain ⟨h0, hh0⟩ := hne
  have hpos : 0 < p ⬝ᵥ (∑ j, yy j + ∑ i, E.ζ i - ∑ i, xx i) := by
    unfold dotProduct
    apply Finset.sum_pos'
    · intro h _
      apply mul_nonneg (hp0 h)
      have := hlt h
      simp only [totalEndowment] at this
      simp only [Pi.sub_apply, Pi.add_apply]
      linarith
    · refine ⟨h0, Finset.mem_univ _, mul_pos (lt_of_le_of_ne (hp0 h0) (Ne.symm hh0)) ?_⟩
      have := hlt h0
      simp only [totalEndowment] at this
      simp only [Pi.sub_apply, Pi.add_apply]
      linarith
  rw [dotProduct_sub, dotProduct_add] at hpos
  linarith
