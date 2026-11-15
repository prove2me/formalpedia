-- Prove2me | Definitions.Def_RPLib_S4_SwanHerb
-- name    : RPLib_S4_SwanHerb
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:17:13.0232+00:00
-- url     : https://prove2.me/theorems/519e4d6f-c319-4e8e-8f3e-2db1dab7624c
-- title:
--   Ramification functions on a finite group, lower and upper numbering, and the Herbrand function
-- statement:
--   A ramification function on a finite group $G$ is a map $i : G \to \mathbb{N} \cup \{\infty\}$ with $i(\sigma) = \infty$ exactly for $\sigma = 1$, $i \ge 1$, $i(\sigma^{-1}) = i(\sigma)$ and $i(\sigma\tau) \ge \min(i(\sigma), i(\tau))$ (the model is $i(\sigma) = v_L(\sigma\pi - \pi)$ for a totally ramified extension of local fields with Galois group $G$). The lower ramification groups $G_u = \{\sigma : i(\sigma) \ge u + 1\}$ are normal and decreasing, and the Herbrand function is $$\varphi(m) = \frac{1}{|G|}\sum_{\sigma \in G} \min(i(\sigma), m + 1) - 1 = \sum_{u = 1}^{m} \frac{|G_u|}{|G_0|}.$$ The file proves that $\varphi$ is strictly increasing with $\varphi(0) = 0$, and defines the upper numbering $G^v = G_{\psi(v)}$ for $v \in \mathbb{Q}$, where $\psi(v)$ is the least $m$ with $v \le \varphi(m)$, with its basic properties (normality, monotonicity, restriction to subgroups).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Local Fields, GTM 67, Springer (1979), doi:10.1007/978-1-4757-5673-9, Chapter IV, Sections 1 and 3

import Mathlib

/-!
# S4-Swan (K2), part 1: ramification functions, lower and upper numbering, the Herbrand function

A *ramification function* on a group `G` (the inertia group of a totally ramified finite Galois extension of
discretely valued fields, so `G = G_0`) is `i : G → ℕ∞` with `i σ = ⊤ ↔ σ = 1`, `1 ≤ i σ`, the ultrametric
inequality `min (i σ) (i τ) ≤ i (σ τ)`, and invariance under inversion and conjugation (Serre, *Local Fields*
IV §1: `i_G(σ) = v_L(σ x - x)` for a generator `x` of the valuation ring).

* lower numbering `G_u = {σ | u + 1 ≤ i σ}` (`lower`), normal subgroups, `G_0 = G`;
* the Herbrand function, defined by Serre's sum formula (IV §3)
  `φ(m) = (1/|G|) ∑_σ min (i σ, m + 1) - 1` on `ℕ`; `φ(m+1) = φ(m) + |G_{m+1}|/|G|`, strictly monotone, unbounded;
* upper numbering `G^v = G_{ψ(v)}` with `ψ(v) = min {m | v ≤ φ m}` (`upper`), and
  `σ ∈ G^v ↔ v ≤ φ(i σ - 1)` for `σ ≠ 1` (`mem_upper`).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace Swan

noncomputable section

/-- A ramification function on a group (the totally ramified case `G = G_0`). -/
structure RamFn (G : Type*) [Group G] where
  /-- `i σ = v_L(σ π - π)`. -/
  i : G → ℕ∞
  i_eq_top : ∀ σ, i σ = ⊤ ↔ σ = 1
  one_le : ∀ σ, 1 ≤ i σ
  le_mul : ∀ σ τ, min (i σ) (i τ) ≤ i (σ * τ)
  i_inv : ∀ σ, i σ⁻¹ = i σ
  i_conj : ∀ σ τ, i (τ * σ * τ⁻¹) = i σ

namespace RamFn

variable {G : Type*} [Group G] (R : RamFn G)

theorem i_one : R.i 1 = ⊤ := (R.i_eq_top 1).2 rfl

theorem i_ne_top {σ : G} (h : σ ≠ 1) : R.i σ ≠ ⊤ := fun h' => h ((R.i_eq_top σ).1 h')

theorem exists_i_eq {σ : G} (h : σ ≠ 1) : ∃ n : ℕ, 1 ≤ n ∧ R.i σ = n := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (R.i_ne_top h)
  refine ⟨n, ?_, hn.symm⟩
  have h1 := R.one_le σ
  rw [← hn] at h1
  exact_mod_cast h1

/-- Ultrametric equality: `i (σ τ) = i τ` when `i τ < i σ`. -/
theorem i_mul_of_lt {σ τ : G} (h : R.i τ < R.i σ) : R.i (σ * τ) = R.i τ := by
  apply le_antisymm
  · have h1 := R.le_mul σ⁻¹ (σ * τ)
    rw [R.i_inv, inv_mul_cancel_left] at h1
    by_contra hc
    exact absurd h1 (not_le.2 (lt_min h (not_le.1 hc)))
  · calc R.i τ = min (R.i σ) (R.i τ) := (min_eq_right h.le).symm
      _ ≤ _ := R.le_mul σ τ

/-- If `σ` has maximal `i` on `σ τ`, then `i (σ τ) = min (i τ) (i σ)` (Serre IV §3, proof of Lemma 5). -/
theorem i_mul_eq_min {σ τ : G} (hmax : R.i (σ * τ) ≤ R.i σ) :
    R.i (σ * τ) = min (R.i τ) (R.i σ) := by
  rcases lt_or_ge (R.i τ) (R.i σ) with h | h
  · rw [R.i_mul_of_lt h, min_eq_left h.le]
  · rw [min_eq_right h]
    exact le_antisymm hmax (le_trans (le_min le_rfl h) (R.le_mul σ τ))

/-- Lower numbering ramification groups `G_u = {σ | u + 1 ≤ i σ}`. -/
def lower (u : ℕ) : Subgroup G where
  carrier := {σ | ((u + 1 : ℕ) : ℕ∞) ≤ R.i σ}
  one_mem' := by
    show ((u + 1 : ℕ) : ℕ∞) ≤ R.i 1
    rw [R.i_one]; exact le_top
  mul_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (R.le_mul a b)
  inv_mem' := fun {a} ha => by
    show ((u + 1 : ℕ) : ℕ∞) ≤ R.i a⁻¹
    rw [R.i_inv]; exact ha

theorem mem_lower {u : ℕ} {σ : G} : σ ∈ R.lower u ↔ ((u + 1 : ℕ) : ℕ∞) ≤ R.i σ := Iff.rfl

instance lower_normal (u : ℕ) : (R.lower u).Normal where
  conj_mem := fun σ hσ τ => by
    show ((u + 1 : ℕ) : ℕ∞) ≤ R.i (τ * σ * τ⁻¹)
    rw [R.i_conj]; exact hσ

theorem lower_zero : R.lower 0 = ⊤ := by
  ext σ
  simp only [Subgroup.mem_top, iff_true, mem_lower, zero_add, Nat.cast_one]
  exact R.one_le σ

theorem lower_antitone : Antitone R.lower := fun u v h σ hσ => by
  show ((u + 1 : ℕ) : ℕ∞) ≤ R.i σ
  exact le_trans (Nat.cast_le.2 (Nat.succ_le_succ h)) hσ

/-- The lower index `j σ = i σ - 1` (`σ ∈ G_u ↔ u ≤ j σ` for `σ ≠ 1`). -/
def jdx (σ : G) : ℕ := (R.i σ).toNat - 1

theorem mem_lower_iff {σ : G} (h : σ ≠ 1) (u : ℕ) : σ ∈ R.lower u ↔ u ≤ R.jdx σ := by
  obtain ⟨n, hn1, hn⟩ := R.exists_i_eq h
  rw [mem_lower, jdx, hn, ENat.toNat_coe, Nat.cast_le]
  omega

/-- The restriction of a ramification function to a subgroup. -/
def restrict (H : Subgroup G) : RamFn H where
  i := fun τ => R.i τ
  i_eq_top := fun τ => by
    rw [R.i_eq_top]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  one_le := fun τ => R.one_le τ
  le_mul := fun σ τ => R.le_mul σ τ
  i_inv := fun τ => R.i_inv τ
  i_conj := fun σ τ => R.i_conj σ τ

theorem restrict_i (H : Subgroup G) (τ : H) : (R.restrict H).i τ = R.i τ := rfl

/-! ## The Herbrand function -/

variable [Fintype G]

/-- `w σ m = min (i σ) (m + 1)` as a natural number. -/
def w (σ : G) (m : ℕ) : ℕ := (min (R.i σ) ((m + 1 : ℕ) : ℕ∞)).toNat

theorem w_one (m : ℕ) : R.w 1 m = m + 1 := by
  rw [w, R.i_one, min_eq_right le_top, ENat.toNat_coe]

theorem w_of_eq {σ : G} {n : ℕ} (h : R.i σ = n) (m : ℕ) : R.w σ m = min n (m + 1) := by
  rw [w, h]
  rcases le_total n (m + 1) with hh | hh
  · rw [min_eq_left (Nat.cast_le.2 hh), min_eq_left hh, ENat.toNat_coe]
  · rw [min_eq_right (Nat.cast_le.2 hh), min_eq_right hh, ENat.toNat_coe]

theorem w_zero (σ : G) : R.w σ 0 = 1 := by
  by_cases h : σ = 1
  · rw [h, R.w_one]
  · obtain ⟨n, hn1, hn⟩ := R.exists_i_eq h
    rw [R.w_of_eq hn]; omega

theorem w_succ_of_mem {σ : G} {m : ℕ} (h : σ ∈ R.lower (m + 1)) : R.w σ (m + 1) = R.w σ m + 1 := by
  by_cases h1 : σ = 1
  · rw [h1, R.w_one, R.w_one]
  · obtain ⟨n, hn1, hn⟩ := R.exists_i_eq h1
    rw [mem_lower, hn, Nat.cast_le] at h
    rw [R.w_of_eq hn, R.w_of_eq hn]; omega

theorem w_succ_of_not_mem {σ : G} {m : ℕ} (h : σ ∉ R.lower (m + 1)) : R.w σ (m + 1) = R.w σ m := by
  by_cases h1 : σ = 1
  · exact absurd (h1 ▸ (R.lower (m + 1)).one_mem) h
  · obtain ⟨n, hn1, hn⟩ := R.exists_i_eq h1
    rw [mem_lower, hn, Nat.cast_le] at h
    rw [R.w_of_eq hn, R.w_of_eq hn]; omega

/-- The Herbrand function `φ(m) = (1/|G|) ∑_σ min (i σ, m + 1) - 1` (Serre IV §3). -/
def phi (m : ℕ) : ℚ := (∑ σ : G, (R.w σ m : ℚ)) / Nat.card G - 1

theorem cardG_pos : (0 : ℚ) < Nat.card G := by exact_mod_cast Nat.card_pos

theorem phi_zero : R.phi 0 = 0 := by
  have h : (∑ σ : G, (R.w σ 0 : ℚ)) = Nat.card G := by
    simp [R.w_zero, Nat.card_eq_fintype_card]
  rw [phi, h, div_self ((cardG_pos (G := G))).ne', sub_self]

theorem phi_succ (m : ℕ) : R.phi (m + 1) = R.phi m + Nat.card (R.lower (m + 1)) / Nat.card G := by
  classical
  have h : (∑ σ : G, (R.w σ (m + 1) : ℚ)) =
      (∑ σ : G, (R.w σ m : ℚ)) + ∑ σ : G, (if σ ∈ R.lower (m + 1) then (1 : ℚ) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    by_cases hσ : σ ∈ R.lower (m + 1)
    · rw [R.w_succ_of_mem hσ, if_pos hσ]; push_cast; ring
    · rw [R.w_succ_of_not_mem hσ, if_neg hσ, add_zero]
  have hc : (∑ σ : G, (if σ ∈ R.lower (m + 1) then (1 : ℚ) else 0)) = Nat.card (R.lower (m + 1)) := by
    rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [phi, phi, h, hc, add_div]; ring

theorem phi_lt_succ (m : ℕ) : R.phi m < R.phi (m + 1) := by
  rw [R.phi_succ]
  have : (0 : ℚ) < Nat.card (R.lower (m + 1)) := by exact_mod_cast Nat.card_pos
  linarith [div_pos this (cardG_pos (G := G))]

theorem phi_strictMono : StrictMono R.phi := strictMono_nat_of_lt_succ R.phi_lt_succ

theorem phi_le_iff {a b : ℕ} : R.phi a ≤ R.phi b ↔ a ≤ b := R.phi_strictMono.le_iff_le

theorem phi_ge (m : ℕ) : (m : ℚ) / Nat.card G ≤ R.phi m := by
  induction m with
  | zero => rw [R.phi_zero]; simp
  | succ m ih =>
    rw [R.phi_succ]
    have h1 : (1 : ℚ) ≤ Nat.card (R.lower (m + 1)) := by exact_mod_cast Nat.card_pos
    have h2 : (1 : ℚ) / Nat.card G ≤ Nat.card (R.lower (m + 1)) / Nat.card G :=
      div_le_div_of_nonneg_right h1 (cardG_pos (G := G)).le
    have h3 : ((m + 1 : ℕ) : ℚ) / Nat.card G = (m : ℚ) / Nat.card G + 1 / Nat.card G := by
      push_cast; ring
    linarith

/-- `φ` is the lower-numbering sum `φ(m) = ∑_{1 ≤ u ≤ m} |G_u| / |G|`. -/
theorem phi_eq_sum (m : ℕ) :
    R.phi m = ∑ u ∈ Finset.range m, (Nat.card (R.lower (u + 1)) : ℚ) / Nat.card G := by
  induction m with
  | zero => rw [R.phi_zero, Finset.sum_range_zero]
  | succ m ih => rw [R.phi_succ, ih, Finset.sum_range_succ]

theorem exists_le_phi (v : ℚ) : ∃ m : ℕ, v ≤ R.phi m := by
  obtain ⟨m, hm⟩ := exists_nat_gt (v * Nat.card G)
  refine ⟨m, le_trans ?_ (R.phi_ge m)⟩
  rw [le_div_iff₀ (cardG_pos (G := G))]; exact hm.le

/-! ## Upper numbering -/

/-- `ψ(v) = min {m | v ≤ φ m}`. -/
def upperIdx (v : ℚ) : ℕ := Nat.find (R.exists_le_phi v)

/-- Upper numbering ramification groups `G^v = G_{ψ(v)}`. -/
def upper (v : ℚ) : Subgroup G := R.lower (R.upperIdx v)

instance upper_normal (v : ℚ) : (R.upper v).Normal := R.lower_normal _

theorem upperIdx_le_iff (v : ℚ) (n : ℕ) : R.upperIdx v ≤ n ↔ v ≤ R.phi n := by
  rw [upperIdx, Nat.find_le_iff]
  constructor
  · rintro ⟨m, hm, hv⟩; exact le_trans hv (R.phi_le_iff.2 hm)
  · intro h; exact ⟨n, le_rfl, h⟩

/-- `σ ∈ G^v ↔ v ≤ φ(i σ - 1)` for `σ ≠ 1`. -/
theorem mem_upper {σ : G} (h : σ ≠ 1) (v : ℚ) : σ ∈ R.upper v ↔ v ≤ R.phi (R.jdx σ) := by
  rw [upper, R.mem_lower_iff h, R.upperIdx_le_iff]

theorem upper_antitone : Antitone R.upper := fun v v' hv σ hσ => by
  by_cases h : σ = 1
  · rw [h]; exact Subgroup.one_mem _
  · rw [R.mem_upper h] at hσ ⊢; exact le_trans hv hσ

theorem upper_eq_top {v : ℚ} (hv : v ≤ 0) : R.upper v = ⊤ := by
  have : R.upperIdx v = 0 := by
    rw [← Nat.le_zero, R.upperIdx_le_iff, R.phi_zero]; exact hv
  rw [upper, this, R.lower_zero]

end RamFn

end

end Swan
end RamanujanPetersson


