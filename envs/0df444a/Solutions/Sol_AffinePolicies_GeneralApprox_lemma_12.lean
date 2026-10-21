-- Prove2me | solution 1 for AffinePolicies.GeneralApprox.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:45:11.879064+00:00
-- url     : https://prove2.me/submissions/006347a1-3497-4879-a869-f5fd04b5097b

import Mathlib
import Definitions.Def_AffinePolicies_GeneralApprox_Setting

set_option autoImplicit false
open Matrix Filter Topology
open AffinePolicies.SqrtBound AffinePolicies.GeneralApprox

lemma apg_mu_pos {m : ℕ} (U : Set (Fin m → ℝ)) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (hUfull : (interior U).Nonempty) (μ : Fin m → ℝ)
    (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j)) : ∀ j, 0 < μ j := by
  intro j
  obtain ⟨b0, hb0⟩ := hUfull
  have hU : U ∈ 𝓝 b0 := mem_interior_iff_mem_nhds.1 hb0
  have hcont : Continuous (fun t : ℝ => b0 + t • (Pi.single j (1 : ℝ) : Fin m → ℝ)) := by
    fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), b0 + t • (Pi.single j (1 : ℝ) : Fin m → ℝ) ∈ U :=
    hcont.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨t, ht, htpos⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))).exists
  have h1 := (hμ j).2 ⟨_, ht, rfl⟩
  have h2 : 0 ≤ b0 j := hUnn b0 (interior_subset hb0) j
  simp at h1
  have : (0 : ℝ) < t := htpos
  linarith

lemma apg_alg {m : ℕ} (U : Set (Fin m → ℝ)) (μ : Fin m → ℝ) (K : ℕ) (u : ℕ → Fin m → ℝ)
    (hu0 : ∀ i, 1 ≤ i → i ≤ K → ∀ j, 0 ≤ u i j) :
    ∀ k ≤ K, ∀ j, (j ∉ J1 μ u k → μ j ≤ bvec μ u k j) ∧
      bvec μ u k j ≤ ∑ i ∈ Finset.Icc 1 k, u i j := by
  intro k
  induction k with
  | zero => intro _ j; simp [J1, bvec, algState]
  | succ k ih =>
    intro hk j
    have ih' := ih (by omega) j
    have hu : 0 ≤ u (k + 1) j := hu0 (k + 1) (by omega) hk j
    have hb : bvec μ u (k + 1) j =
        if j ∈ J1 μ u k then bvec μ u k j + u (k + 1) j else bvec μ u k j := rfl
    have hJ : J1 μ u (k + 1) = (J1 μ u k).filter (fun j =>
        (if j ∈ J1 μ u k then bvec μ u k j + u (k + 1) j else bvec μ u k j) < μ j) := rfl
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
    constructor
    · intro hj
      rw [hJ, Finset.mem_filter] at hj
      rw [hb]
      by_cases hjk : j ∈ J1 μ u k
      · simp only [hjk, true_and, if_true] at hj ⊢
        exact not_lt.mp hj
      · simp only [hjk, if_false]
        exact ih'.1 hjk
    · rw [hb]
      by_cases hjk : j ∈ J1 μ u k
      · simp only [hjk, if_true]
        linarith [ih'.2]
      · simp only [hjk, if_false]
        linarith [ih'.2]

theorem solution {m : ℕ} (U : Set (Fin m → ℝ))
    (hUnn : ∀ b ∈ U, 0 ≤ b) (hUfull : (interior U).Nonempty)
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j))
    (bstar : Fin m → Fin m → ℝ) (hbstar : ∀ j, bstar j ∈ U ∧ bstar j j = μ j)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hrun : AffinePolicies.SqrtBound.IsRun U μ K u) :
    ∀ b ∈ U, ∃ b' ∈ U0 bstar u K, b ≤ b' := by
  intro b hb
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    exact ⟨(2 : ℝ) • betaSum u K, subset_convexHull ℝ _ (Or.inr rfl), fun i => i.elim0⟩
  have hμpos := apg_mu_pos U hUnn hUfull μ hμ
  have hsqpos : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  obtain ⟨hiter, hnoloop⟩ := hrun
  have hu0 : ∀ i, 1 ≤ i → i ≤ K → ∀ j, 0 ≤ u i j := by
    intro i hi1 hiK j
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    exact hUnn _ (hiter i' (by omega)).2.1 j
  have halg := apg_alg U μ K u hu0 K le_rfl
  have hbJ : ∑ j ∈ J1 μ u K, b j / μ j ≤ Real.sqrt m := by
    unfold LoopCond at hnoloop
    push Not at hnoloop
    exact hnoloop b hb
  have hβ : ∀ i, betaSum u K i = ∑ k ∈ Finset.Icc 1 K, u k i := by
    intro i; simp [betaSum, Finset.sum_apply]
  have hβ0 : ∀ i, 0 ≤ betaSum u K i := by
    intro i; rw [hβ]
    exact Finset.sum_nonneg (fun k hk => hu0 k (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2 i)
  have hbμ : ∀ j, b j ≤ μ j := fun j => (hμ j).2 ⟨b, hb, rfl⟩
  have hJ2 : ∀ j, j ∉ J1 μ u K → μ j ≤ betaSum u K j := fun j hj => by
    rw [hβ]; exact le_trans ((halg j).1 hj) (halg j).2
  -- weights
  set w : Fin m → ℝ := fun j => if j ∈ J1 μ u K then b j / (2 * Real.sqrt m * μ j) else 0 with hw
  have hbnn : ∀ j, 0 ≤ b j := fun j => hUnn b hb j
  have hbsnn : ∀ j i, 0 ≤ bstar j i := fun j i => hUnn _ (hbstar j).1 i
  have hw0 : ∀ j, 0 ≤ w j := by
    intro j
    simp only [hw]
    split_ifs
    · have := hbnn j
      have := hμpos j
      positivity
    · exact le_rfl
  have hwsum : ∑ j, w j ≤ 1 / 2 := by
    have : ∑ j, w j = (∑ j ∈ J1 μ u K, b j / μ j) / (2 * Real.sqrt m) := by
      simp only [hw]
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_div]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have := (hμpos j).ne'
      field_simp
    rw [this, div_le_iff₀ (by positivity)]
    linarith
  -- the point b'
  let ω : Option (Fin m) → ℝ := fun o => match o with
    | none => 1 - ∑ j, w j
    | some j => w j
  let z : Option (Fin m) → (Fin m → ℝ) := fun o => match o with
    | none => (2 : ℝ) • betaSum u K
    | some j => (2 * Real.sqrt m) • bstar j
  have hω0 : ∀ o, 0 ≤ ω o := by
    intro o
    cases o with
    | none => show 0 ≤ 1 - ∑ j, w j; linarith
    | some j => exact hw0 j
  have hω1 : ∑ o, ω o = 1 := by
    rw [Fintype.sum_option]
    show (1 - ∑ j, w j) + ∑ j, w j = 1
    ring
  have hzmem : ∀ o, z o ∈ U0 bstar u K := by
    intro o
    cases o with
    | none => exact subset_convexHull ℝ _ (Or.inr rfl)
    | some j => exact subset_convexHull ℝ _ (Or.inl ⟨j, rfl⟩)
  have hmem : ∑ o, ω o • z o ∈ U0 bstar u K :=
    (convex_convexHull ℝ _).sum_mem (fun o _ => hω0 o) (by simpa using hω1) (fun o _ => hzmem o)
  refine ⟨_, hmem, fun i => ?_⟩
  have hcoord : (∑ o, ω o • z o) i = (1 - ∑ j, w j) * (2 * betaSum u K i) +
      ∑ j, w j * ((2 * Real.sqrt m) * bstar j i) := by
    rw [Fintype.sum_option]
    simp [ω, z, Finset.sum_apply]
  rw [hcoord]
  have hA : 0 ≤ (1 - ∑ j, w j) * (2 * betaSum u K i) := by
    have := hβ0 i
    have : 0 ≤ 1 - ∑ j, w j := by linarith
    positivity
  have hS : ∀ j, 0 ≤ w j * ((2 * Real.sqrt m) * bstar j i) := fun j => by
    have := hbsnn j i
    have := hw0 j
    positivity
  by_cases hi : i ∈ J1 μ u K
  · have h1 : w i * ((2 * Real.sqrt m) * bstar i i) ≤ ∑ j, w j * ((2 * Real.sqrt m) * bstar j i) :=
      Finset.single_le_sum (f := fun j => w j * ((2 * Real.sqrt m) * bstar j i))
        (fun j _ => hS j) (Finset.mem_univ i)
    have h2 : w i * ((2 * Real.sqrt m) * bstar i i) = b i := by
      simp only [hw, hi, if_true, (hbstar i).2]
      have := (hμpos i).ne'
      field_simp
    linarith
  · have h1 := hJ2 i hi
    have h2 := hbμ i
    have h3 : 0 ≤ ∑ j, w j * ((2 * Real.sqrt m) * bstar j i) := Finset.sum_nonneg (fun j _ => hS j)
    have h4 : betaSum u K i ≤ (1 - ∑ j, w j) * (2 * betaSum u K i) := by
      have := hβ0 i
      nlinarith
    linarith
