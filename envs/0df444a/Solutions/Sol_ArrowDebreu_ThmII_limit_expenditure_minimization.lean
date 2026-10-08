-- Prove2me | solution 1 for ArrowDebreu.ThmII.limit_expenditure_minimization
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T16:09:49.943977+00:00
-- url     : https://prove2.me/submissions/1ff722ef-c351-49a4-97ed-98027d36f18d

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_ThmII_AssumptionsII
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmII_economyEeps
open ArrowDebreu.Shared

open Filter Topology

namespace AD8d48

open ArrowDebreu.Shared Filter Topology ArrowDebreu.ThmII in
theorem quasi {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsIIexceptV E)
    (εs : ℕ → ℝ)
    (as : ℕ → Player m n → Fin l → ℝ)
    (has : ∀ k, (economyEeps E (εs k)).IsEquilibriumPoint (as k))
    (a0 : Player m n → Fin l → ℝ) (hlim : Tendsto as atTop (𝓝 a0)) :
    ∀ i, ∀ x ∈ E.X i, E.u i (consOf a0 i) < E.u i x →
      priceOf a0 ⬝ᵥ consOf a0 i ≤ priceOf a0 ⬝ᵥ x := by
  intro i x hx hux
  have hcons : Tendsto (fun k => as k (Sum.inl i)) atTop (𝓝 (a0 (Sum.inl i))) :=
    ((continuous_apply (Sum.inl i)).tendsto a0).comp hlim
  have hmemk : ∀ k, as k (Sum.inl i) ∈ E.X i := fun k => (has k).1 (Sum.inl i) (Set.mem_univ _)
  have hx0 : a0 (Sum.inl i) ∈ E.X i :=
    (hE.II i).1.mem_of_tendsto hcons (Eventually.of_forall hmemk)
  have hu : Tendsto (fun k => E.u i (as k (Sum.inl i))) atTop (𝓝 (E.u i (a0 (Sum.inl i)))) :=
    ((hE.IIIa i) _ hx0).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hcons, Eventually.of_forall hmemk⟩)
  have hux' : E.u i (a0 (Sum.inl i)) < E.u i x := hux
  have hev : ∀ᶠ k in atTop, E.u i (as k (Sum.inl i)) < E.u i x :=
    hu.eventually (Iio_mem_nhds hux')
  have hle : ∀ᶠ k in atTop, (fun a : Player m n → Fin l → ℝ => priceOf a ⬝ᵥ consOf a i) (as k) ≤
      (fun a : Player m n → Fin l → ℝ => priceOf a ⬝ᵥ x) (as k) := by
    filter_upwards [hev] with k hk
    obtain ⟨hmem, hmax⟩ := (has k).2 (Sum.inl i)
    have hmem' : as k (Sum.inl i) ∈ E.X i ∧ priceOf (as k) ⬝ᵥ as k (Sum.inl i) ≤
        priceOf (as k) ⬝ᵥ E.ζ i +
          max 0 (∑ j, E.α i j * (priceOf (as k) ⬝ᵥ prodOf (as k) j)) := hmem
    show priceOf (as k) ⬝ᵥ as k (Sum.inl i) ≤ priceOf (as k) ⬝ᵥ x
    by_contra hcon
    push Not at hcon
    have hxin : x ∈ (economyEeps E (εs k)).constr (Sum.inl i) (as k) := by
      show x ∈ E.X i ∧ priceOf (as k) ⬝ᵥ x ≤
        priceOf (as k) ⬝ᵥ E.ζ i + max 0 (∑ j, E.α i j * (priceOf (as k) ⬝ᵥ prodOf (as k) j))
      exact ⟨hx, le_trans hcon.le hmem'.2⟩
    have h1 := hmax x hxin
    have h2 : E.u i (Function.update (as k) (Sum.inl i) x (Sum.inl i)) ≤
        E.u i (as k (Sum.inl i)) := h1
    simp only [Function.update_self] at h2
    linarith
  have hc1 : Continuous (fun a : Player m n → Fin l → ℝ => priceOf a ⬝ᵥ consOf a i) :=
    Continuous.dotProduct (continuous_apply _) (continuous_apply _)
  have hc2 : Continuous (fun a : Player m n → Fin l → ℝ => priceOf a ⬝ᵥ x) :=
    Continuous.dotProduct (continuous_apply _) continuous_const
  exact le_of_tendsto_of_tendsto ((hc1.tendsto a0).comp hlim) ((hc2.tendsto a0).comp hlim) hle

open ArrowDebreu.Shared Filter Topology ArrowDebreu.ThmII in
theorem price_tendsto {l m n : ℕ} (as : ℕ → Player m n → Fin l → ℝ)
    (a0 : Player m n → Fin l → ℝ) (hlim : Tendsto as atTop (𝓝 a0)) (h : Fin l) :
    Tendsto (fun k => priceOf (as k) h) atTop (𝓝 (priceOf a0 h)) :=
  by
    have hc : Continuous (fun a : Player m n → Fin l → ℝ => priceOf a h) :=
      (continuous_apply h).comp (continuous_apply _)
    exact (hc.tendsto a0).comp hlim

open ArrowDebreu.Shared Filter Topology ArrowDebreu.ThmII in
theorem price_nonneg {l m n : ℕ} (E : Economy l m n)
    (εs : ℕ → ℝ)
    (as : ℕ → Player m n → Fin l → ℝ)
    (has : ∀ k, (economyEeps E (εs k)).IsEquilibriumPoint (as k))
    (a0 : Player m n → Fin l → ℝ) (hlim : Tendsto as atTop (𝓝 a0)) (h : Fin l) :
    0 ≤ priceOf a0 h := by
  have hk : ∀ k, 0 ≤ priceOf (as k) h := by
    intro k
    have hp : as k (Sum.inr (Sum.inr ())) ∈ priceSimplexEps E (εs k) :=
      (has k).1 (Sum.inr (Sum.inr ())) (Set.mem_univ _)
    exact hp.1.1 h
  exact ge_of_tendsto (price_tendsto as a0 hlim h) (Eventually.of_forall hk)

open ArrowDebreu.Shared Filter Topology ArrowDebreu.ThmII in
theorem prod_mem {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsIIexceptV E)
    (εs : ℕ → ℝ)
    (as : ℕ → Player m n → Fin l → ℝ)
    (has : ∀ k, (economyEeps E (εs k)).IsEquilibriumPoint (as k))
    (a0 : Player m n → Fin l → ℝ) (hlim : Tendsto as atTop (𝓝 a0)) (j : Fin n) :
    prodOf a0 j ∈ E.Y j := by
  have hc : Tendsto (fun k => as k (Sum.inr (Sum.inl j))) atTop
      (𝓝 (a0 (Sum.inr (Sum.inl j)))) :=
    ((continuous_apply (Sum.inr (Sum.inl j))).tendsto a0).comp hlim
  have hm : ∀ k, as k (Sum.inr (Sum.inl j)) ∈ E.Y j := fun k =>
    (has k).1 (Sum.inr (Sum.inl j)) (Set.mem_univ _)
  exact (hE.Ia j).1.mem_of_tendsto hc (Eventually.of_forall hm)

open ArrowDebreu.Shared Filter Topology ArrowDebreu.ThmII in
theorem profit_max {l m n : ℕ} (E : Economy l m n)
    (εs : ℕ → ℝ)
    (as : ℕ → Player m n → Fin l → ℝ)
    (has : ∀ k, (economyEeps E (εs k)).IsEquilibriumPoint (as k))
    (a0 : Player m n → Fin l → ℝ) (hlim : Tendsto as atTop (𝓝 a0)) (j : Fin n)
    (y : Fin l → ℝ) (hy : y ∈ E.Y j) :
    priceOf a0 ⬝ᵥ y ≤ priceOf a0 ⬝ᵥ prodOf a0 j := by
  have hk : ∀ k, priceOf (as k) ⬝ᵥ y ≤ priceOf (as k) ⬝ᵥ prodOf (as k) j := by
    intro k
    obtain ⟨_, hmax⟩ := (has k).2 (Sum.inr (Sum.inl j))
    have h2 : priceOf (Function.update (as k) (Sum.inr (Sum.inl j)) y) ⬝ᵥ
        Function.update (as k) (Sum.inr (Sum.inl j)) y (Sum.inr (Sum.inl j)) ≤
        priceOf (as k) ⬝ᵥ as k (Sum.inr (Sum.inl j)) := hmax y hy
    have hp : priceOf (Function.update (as k) (Sum.inr (Sum.inl j)) y) = priceOf (as k) := by
      unfold priceOf
      rw [Function.update_of_ne (by simp)]
    rw [hp, Function.update_self] at h2
    exact h2
  have hc1 : Continuous (fun a : Player m n → Fin l → ℝ => priceOf a ⬝ᵥ y) :=
    Continuous.dotProduct (continuous_apply _) continuous_const
  have hc2 : Continuous (fun a : Player m n → Fin l → ℝ => priceOf a ⬝ᵥ prodOf a j) :=
    Continuous.dotProduct (continuous_apply _) (continuous_apply _)
  exact le_of_tendsto_of_tendsto ((hc1.tendsto a0).comp hlim) ((hc2.tendsto a0).comp hlim)
    (Eventually.of_forall hk)

open ArrowDebreu.Shared Filter Topology ArrowDebreu.ThmII in
theorem zero_productive {l m n : ℕ} (E : Economy l m n)
    (εs : ℕ → ℝ)
    (hεs0 : Tendsto εs atTop (𝓝 0))
    (as : ℕ → Player m n → Fin l → ℝ)
    (a0 : Player m n → Fin l → ℝ) (hlim : Tendsto as atTop (𝓝 a0))
    (hbind : ∀ k, ∃ h ∈ productive E, priceOf (as k) h = εs k) :
    ∃ h ∈ productive E, priceOf a0 h = 0 := by
  by_contra H
  push Not at H
  have hev : ∀ h ∈ productive E, ∀ᶠ k in atTop, priceOf (as k) h - εs k ≠ 0 := by
    intro h hh
    have ht : Tendsto (fun k => priceOf (as k) h - εs k) atTop (𝓝 (priceOf a0 h - 0)) :=
      (price_tendsto as a0 hlim h).sub hεs0
    exact ht.eventually_ne (by rw [sub_zero]; exact H h hh)
  rw [← Filter.eventually_all_finset] at hev
  obtain ⟨k, hk⟩ := hev.exists
  obtain ⟨h, hh, he⟩ := hbind k
  exact hk h hh (by rw [he, sub_self])

open ArrowDebreu.Shared Filter Topology ArrowDebreu.ThmII in
theorem zero_desired {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsIIexceptV E)
    (εs : ℕ → ℝ)
    (hεs0 : Tendsto εs atTop (𝓝 0))
    (as : ℕ → Player m n → Fin l → ℝ)
    (has : ∀ k, (economyEeps E (εs k)).IsEquilibriumPoint (as k))
    (a0 : Player m n → Fin l → ℝ) (hlim : Tendsto as atTop (𝓝 a0))
    (hbind : ∀ k, ∃ h ∈ productive E, priceOf (as k) h = εs k) :
    ∃ h ∈ desired E, priceOf a0 h = 0 := by
  obtain ⟨h, hh, hp0⟩ := zero_productive E εs hεs0 as a0 hlim hbind
  have hY0 : (∑ j, prodOf a0 j) ∈ aggProd E :=
    ⟨prodOf a0, fun j => prod_mem E hE εs as has a0 hlim j, rfl⟩
  obtain ⟨_, y', hy', hge, h'', hD, hlt⟩ := ((mem_productive E h).1 hh _ hY0)
  obtain ⟨yv, hyv, rfl⟩ := hy'
  set p := priceOf a0 with hpdef
  have hle : p ⬝ᵥ (∑ j, yv j) ≤ p ⬝ᵥ (∑ j, prodOf a0 j) := by
    rw [dotProduct_sum, dotProduct_sum]
    exact Finset.sum_le_sum fun j _ => profit_max E εs as has a0 hlim j (yv j) (hyv j)
  set d : Fin l → ℝ := (∑ j, yv j) - ∑ j, prodOf a0 j with hd
  have hd0 : p ⬝ᵥ d ≤ 0 := by
    rw [hd, dotProduct_sub]; linarith
  have hnn : ∀ h' ∈ (Finset.univ : Finset (Fin l)), 0 ≤ p h' * d h' := by
    intro h' _
    by_cases hh' : h' = h
    · subst hh'; rw [hp0, zero_mul]
    · apply mul_nonneg (price_nonneg E εs as has a0 hlim h')
      have := hge h' hh'
      simp only [hd, Pi.sub_apply]
      linarith
  have hsum : ∑ h', p h' * d h' = 0 :=
    le_antisymm (by simpa [dotProduct] using hd0) (Finset.sum_nonneg hnn)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum h'' (Finset.mem_univ _)
  have hdpos : 0 < d h'' := by simp only [hd, Pi.sub_apply]; linarith
  refine ⟨h'', hD, ?_⟩
  rcases mul_eq_zero.1 hz with h1 | h1
  · exact h1
  · linarith

end AD8d48

open ArrowDebreu.Shared Filter Topology ArrowDebreu.ThmII in
theorem solution {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsIIexceptV E)
    (εs : ℕ → ℝ) (hεs : ∀ k, 0 < εs k ∧ εs k ≤ 1 / (2 * ((productive E).card : ℝ)))
    (hεs0 : Tendsto εs atTop (𝓝 0))
    (as : ℕ → Player m n → Fin l → ℝ)
    (has : ∀ k, (economyEeps E (εs k)).IsEquilibriumPoint (as k))
    (a0 : Player m n → Fin l → ℝ) (hlim : Tendsto as atTop (𝓝 a0))
    (hbind : ∀ k, ∃ h ∈ productive E, priceOf (as k) h = εs k) :
    ∀ i, consOf a0 i ∈ E.X i ∧ ∀ x ∈ E.X i, priceOf a0 ⬝ᵥ consOf a0 i ≤ priceOf a0 ⬝ᵥ x := by
  intro i
  have hcons : Tendsto (fun k => as k (Sum.inl i)) atTop (𝓝 (a0 (Sum.inl i))) :=
    ((continuous_apply (Sum.inl i)).tendsto a0).comp hlim
  have hmemk : ∀ k, as k (Sum.inl i) ∈ E.X i := fun k => (has k).1 (Sum.inl i) (Set.mem_univ _)
  have hx0 : consOf a0 i ∈ E.X i :=
    (hE.II i).1.mem_of_tendsto hcons (Eventually.of_forall hmemk)
  refine ⟨hx0, ?_⟩
  intro x hx
  obtain ⟨h, hD, hp0⟩ := AD8d48.zero_desired E hE εs hεs0 as has a0 hlim hbind
  obtain ⟨lam, _, hx2, hu2⟩ := (mem_desired E h).1 hD i _ hx0
  set x2 := consOf a0 i + lam • unitVec h with hx2def
  set p := priceOf a0 with hpdef
  have hpx2 : p ⬝ᵥ x2 = p ⬝ᵥ consOf a0 i := by
    rw [hx2def, dotProduct_add, dotProduct_smul, unitVec, dotProduct_single, hp0]
    simp
  by_contra hcon
  push Not at hcon
  let g : ℝ → Fin l → ℝ := fun t => t • x + (1 - t) • x2
  have hgc : Continuous g := by
    continuity
  have hg0 : g 0 = x2 := by simp [g]
  have hgmem : ∀ t ∈ Set.Icc (0:ℝ) 1, g t ∈ E.X i := by
    intro t ht
    exact (hE.II i).2.1 hx hx2 ht.1 (by linarith [ht.2]) (by ring)
  let ts : ℕ → ℝ := fun k => 1 / ((k:ℝ) + 2)
  have hts0 : Tendsto ts atTop (𝓝 0) := by
    have : Tendsto (fun k : ℕ => ((k:ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    exact this.inv_tendsto_atTop.congr (fun k => by simp [ts])
  have htsI : ∀ k, ts k ∈ Set.Icc (0:ℝ) 1 := by
    intro k
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    constructor
    · positivity
    · rw [div_le_one (by linarith)]; linarith
  have htspos : ∀ k, 0 < ts k := fun k => by
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    simp only [ts]; positivity
  have hgts : Tendsto (fun k => g (ts k)) atTop (𝓝 x2) := by
    rw [← hg0]; exact (hgc.tendsto 0).comp hts0
  have hu : Tendsto (fun k => E.u i (g (ts k))) atTop (𝓝 (E.u i x2)) :=
    ((hE.IIIa i) _ hx2).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hgts, Eventually.of_forall fun k => hgmem _ (htsI k)⟩)
  obtain ⟨k, hk⟩ := (hu.eventually (Ioi_mem_nhds hu2)).exists
  have hq := AD8d48.quasi E hE εs as has a0 hlim i (g (ts k)) (hgmem _ (htsI k)) hk
  have hexp : p ⬝ᵥ g (ts k) = ts k * (p ⬝ᵥ x) + (1 - ts k) * (p ⬝ᵥ x2) := by
    simp only [g, dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [hexp, hpx2] at hq
  have := htspos k
  nlinarith
