-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_Structure
-- name    : BCFGJPSSV26_Greedy_Structure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:53.114524+00:00
-- url     : https://prove2.me/theorems/d7f8a44e-869b-47e7-892e-d27c7a270ec0
-- title:
--   BCFGJPSSV26.Greedy.Structure — The structure lemma
-- statement:
--   This is module `BCFGJPSSV26.Greedy.Structure` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   [BCFGJPSSV26a, Lemma E.7]: during a sequence of type 2, two candidates
--   `i₁, i₂` are either close (`d(i₁, i₂) ≤ δ θ`) or far (`d(i₁, i₂) ≥ θ / γ`). The hypotheses: the
--   current profile `D` is below the profile `D₀` at the start of the sequence, after which no
--   facility was `(1, 0)`-openable (maximality of the preceding sequence of type 1, at the same
--   time `θ`), `f > n η`, and all client–facility distances are at least `1`.
--
--   The proof is the paper's: with `N_a` the active clients within `εθ` of
--   `i_a` (disjoint when `δθ < d(i₁, i₂)`), it shows `lhs1 θ D i₁ ≥ candSum θ D i₁ + n η` in the case
--   `|N₁| ≤ |N₂|` (`BCFGJPSSV26.Greedy.structure_aux`), contradicting `lhs1 θ D i₁ < f`; the other
--   case is symmetric.
--
--   **Contents.** The module is published as a whole: 5 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_Structure`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Structure.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Valid

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.Structure` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The structure lemma

[BCFGJPSSV26a, Lemma E.7]: during a sequence of type 2, two candidates
`i₁, i₂` are either close (`d(i₁, i₂) ≤ δ θ`) or far (`d(i₁, i₂) ≥ θ / γ`). The hypotheses: the
current profile `D` is below the profile `D₀` at the start of the sequence, after which no
facility was `(1, 0)`-openable (maximality of the preceding sequence of type 1, at the same
time `θ`), `f > n η`, and all client–facility distances are at least `1`.

The proof is the paper's: with `N_a` the active clients within `εθ` of
`i_a` (disjoint when `δθ < d(i₁, i₂)`), it shows `lhs1 θ D i₁ ≥ candSum θ D i₁ + n η` in the case
`|N₁| ≤ |N₂|` (`BCFGJPSSV26.Greedy.structure_aux`), contradicting `lhs1 θ D i₁ < f`; the other
case is symmetric.
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

variable {n m : ℕ} {P : Par}

/-- The active clients within `εθ` of `i`, for the profile `D`. -/
def nearSet (P : Par) (X : Space n m) (θ : ℚ) (D : Fin n → ℚ) (i : Fin m) : Finset (Fin n) :=
  univ.filter fun j ↦ θ < (1 - P.δ) * D j ∧ X.d j i ≤ P.ε * θ

/-- If the second bid is positive, the difference of two bids is at least the difference of
their unclamped values. -/
private theorem bid_sub_bid_ge {x y x' y' : ℚ} (h : 0 < bid x' y') :
    (x - γ * y) - (x' - γ * y') ≤ bid x y - bid x' y' := by
  have h1 : bid x' y' = x' - γ * y' := by
    unfold bid at h ⊢
    rcases le_total (x' - γ * y') 0 with h' | h'
    · rw [max_eq_right h'] at h
      exact absurd h (lt_irrefl 0)
    · exact max_eq_left h'
  have h2 : x - γ * y ≤ bid x y := le_max_left _ _
  linarith

/-- **Per-client bound** of the structure lemma, for `δθ < d(i₁, i₂) < θ / γ`: the difference
`Q_j - P_j` of the terms of client `j` in `lhs1 θ D i₁` and in `candSum θ D i₁` is at least
`n η - ε²θ` on `N₁`, at least `ε²θ` (and `ε²θ + n η` if `P_j > 0`) on `N₂`, and at least
`n η` (if `P_j > 0`) or `0` elsewhere. -/
private theorem structure_client (hP : P.Good n) (X : Space n m) (hd1 : ∀ j i, 1 ≤ X.d j i)
    {θ : ℚ} (hθ : 0 < θ) (D : Fin n → ℚ) {i₁ i₂ : Fin m}
    (hlo : P.δ * θ < X.dF i₁ i₂) (hhi : X.dF i₁ i₂ < θ / γ) (j : Fin n) :
    ((if j ∈ nearSet P X θ D i₂ then P.ε ^ 2 * θ else 0) -
        (if j ∈ nearSet P X θ D i₁ then P.ε ^ 2 * θ else 0)) +
      (if j ∈ nearSet P X θ D i₁ ∨ 0 < bid (cval P θ D j) ((1 - P.δ / 2) * X.d j i₁)
        then n * P.η else 0) ≤
    bid (mval P θ D j) ((1 - P.δ) * X.d j i₁) -
      bid (cval P θ D j) ((1 - P.δ / 2) * X.d j i₁) := by
  have hδ := hP.δ_pos
  have hδ1 := hP.δ_le
  have hε := hP.ε_pos
  have hε1 := hP.ε_le
  have hη := hP.η_nonneg
  have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  have hnη : 0 ≤ (n : ℚ) * P.η := mul_nonneg hn hη
  have hγ : γ = 153 / 125 := rfl
  have he1 := hd1 j i₁
  have hγδ := hP.nη_le_γδ
  have hQ0 := bid_nonneg (mval P θ D j) ((1 - P.δ) * X.d j i₁)
  have hP0 := bid_nonneg (cval P θ D j) ((1 - P.δ / 2) * X.d j i₁)
  -- the general bound when the candidacy term is positive
  have hgen : 0 < bid (cval P θ D j) ((1 - P.δ / 2) * X.d j i₁) →
      mval P θ D j - cval P θ D j + γ * P.δ / 2 * X.d j i₁ ≤
        bid (mval P θ D j) ((1 - P.δ) * X.d j i₁) -
          bid (cval P θ D j) ((1 - P.δ / 2) * X.d j i₁) := fun h ↦ by
    have := bid_sub_bid_ge (x := mval P θ D j) (y := (1 - P.δ) * X.d j i₁) h
    linarith
  have hγδe : γ * P.δ / 2 * 1 ≤ γ * P.δ / 2 * X.d j i₁ :=
    mul_le_mul_of_nonneg_left he1 (by rw [hγ]; positivity)
  rcases lt_or_ge θ ((1 - P.δ) * D j) with hact | hina
  · -- active client
    have hmv : mval P θ D j = θ := min_eq_left hact.le
    have hcv : cval P θ D j = (1 + P.ε ^ 2) * θ := if_pos hact
    have hmem : ∀ i, j ∈ nearSet P X θ D i ↔ X.d j i ≤ P.ε * θ := fun i ↦ by
      simp [nearSet, hact]
    simp only [hmv, hcv] at hgen hQ0 hP0 ⊢
    by_cases h₁ : X.d j i₁ ≤ P.ε * θ
    · -- `j ∈ N₁`, so `j ∉ N₂`
      have h₂ : ¬ X.d j i₂ ≤ P.ε * θ := fun h₂ ↦ by
        have := X.dF_le j i₁ i₂
        have := mul_le_mul_of_nonneg_right hP.two_ε_le hθ.le
        linarith
      have hpos : 0 < bid ((1 + P.ε ^ 2) * θ) ((1 - P.δ / 2) * X.d j i₁) := by
        have hb : (1 + P.ε ^ 2) * θ - γ * ((1 - P.δ / 2) * X.d j i₁) ≤
            bid ((1 + P.ε ^ 2) * θ) ((1 - P.δ / 2) * X.d j i₁) := le_max_left _ _
        have h3 : γ * ((1 - P.δ / 2) * X.d j i₁) ≤ γ * (P.ε * θ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by rw [hγ]; norm_num)
          linarith [mul_nonneg hδ.le (X.d_nonneg j i₁)]
        have h4 := mul_lt_mul_of_pos_right hP.γε_lt_one hθ
        have h5 : 0 ≤ P.ε ^ 2 * θ := by positivity
        linarith
      rw [if_neg (by rwa [hmem]), if_pos (by rwa [hmem]),
        if_pos (.inl (by rwa [hmem]))]
      have := hgen hpos
      linarith
    · by_cases h₂ : X.d j i₂ ≤ P.ε * θ
      · -- `j ∈ N₂`: `j` is far from `i₁`, but not too far
        rw [if_pos (by rwa [hmem]), if_neg (by rwa [hmem])]
        have ht1 := X.dF_le j i₁ i₂
        have ht2 := X.d_le_d_add_dF j i₁ i₂
        rw [X.dF_comm] at ht2
        have hγd : X.dF i₁ i₂ * γ < θ := (lt_div_iff₀ (by rw [hγ]; norm_num)).1 hhi
        have hγ0 : (0 : ℚ) ≤ γ := by rw [hγ]; norm_num
        have hγδ0 : (0 : ℚ) ≤ γ * P.δ / 2 := by positivity
        have hi1 := hP.structure_ineq₁
        split_ifs with h
        · have hpos : 0 < bid ((1 + P.ε ^ 2) * θ) ((1 - P.δ / 2) * X.d j i₁) := by
            rcases h with h | h
            · exact absurd ((hmem i₁).1 h) h₁
            · exact h
          have hg := hgen hpos
          have he' : (P.δ - P.ε) * θ ≤ X.d j i₁ := by linarith
          rcases le_or_gt 1 θ with hθ1 | hθ1
          · have k1 := mul_le_mul_of_nonneg_left he' hγδ0
            have k2 := mul_le_mul_of_nonneg_right hi1 hθ.le
            have k3 := mul_le_mul_of_nonneg_left hθ1 hnη
            linarith
          · have k1 : P.ε ^ 2 * θ ≤ P.ε ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left hθ1.le (sq_nonneg _)
            have k2 : γ * P.δ / 2 * (P.δ - P.ε) ≤ γ * P.δ / 2 * 1 :=
              mul_le_mul_of_nonneg_left (by linarith) hγδ0
            linarith
        · push Not at h
          have hQ : θ - γ * ((1 - P.δ) * X.d j i₁) ≤ bid θ ((1 - P.δ) * X.d j i₁) :=
            le_max_left _ _
          have k0 : γ * X.d j i₁ ≤ γ * (P.ε * θ) + γ * X.dF i₁ i₂ := by
            have := mul_le_mul_of_nonneg_left (ht2.trans (add_le_add_left h₂ _)) hγ0
            linarith
          have k1 : (1 - P.δ) * (γ * X.d j i₁) ≤ (1 - P.δ) * (γ * (P.ε * θ) + θ) :=
            mul_le_mul_of_nonneg_left (by linarith) hP.one_sub_δ_pos.le
          have k2 := mul_le_mul_of_nonneg_right hP.γε_lt.le hθ.le
          have k3 : 0 ≤ P.δ * (γ * (P.ε * θ)) := by positivity
          have hε2 : P.ε ^ 2 ≤ P.δ / 2 := by nlinarith
          have k4 := mul_le_mul_of_nonneg_right hε2 hθ.le
          linarith [h.2]
      · -- neither: `j` is far from `i₁`
        rw [if_neg (by rwa [hmem]), if_neg (by rwa [hmem])]
        have hγδ0 : (0 : ℚ) ≤ γ * P.δ / 2 := by rw [hγ]; positivity
        have hi2 := hP.structure_ineq₂
        split_ifs with h
        · have hpos : 0 < bid ((1 + P.ε ^ 2) * θ) ((1 - P.δ / 2) * X.d j i₁) := by
            rcases h with h | h
            · exact absurd ((hmem i₁).1 h) h₁
            · exact h
          have hg := hgen hpos
          have he' : P.ε * θ ≤ X.d j i₁ := (not_le.1 h₁).le
          rcases le_or_gt 1 θ with hθ1 | hθ1
          · have k1 := mul_le_mul_of_nonneg_left he' hγδ0
            have k2 := mul_le_mul_of_nonneg_right hi2 hθ.le
            have k3 := mul_le_mul_of_nonneg_left hθ1 hnη
            linarith
          · have k1 : P.ε ^ 2 * θ ≤ P.ε ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left hθ1.le (sq_nonneg _)
            have k2 : γ * P.δ / 2 * P.ε ≤ γ * P.δ / 2 * 1 :=
              mul_le_mul_of_nonneg_left hP.ε_le_one hγδ0
            linarith
        · push Not at h
          linarith [h.2]
  · -- inactive client
    have hmv : mval P θ D j = (1 - P.δ) * D j := min_eq_right hina
    have hcv : cval P θ D j = (1 - P.δ) * D j := if_neg (not_lt.2 hina)
    have hmem : ∀ i, j ∉ nearSet P X θ D i := fun i ↦ by
      simp [nearSet, not_lt.2 hina]
    simp only [hmv, hcv] at hgen hQ0 hP0 ⊢
    rw [if_neg (hmem i₂), if_neg (hmem i₁), sub_zero, zero_add]
    split_ifs with h
    · rcases h with h | h
      · exact absurd h (hmem i₁)
      · have := hgen h
        linarith
    · push Not at h
      linarith [h.2]

/-- **The structure lemma, one case**: if `δ θ < d(i₁, i₂) < θ / γ`, `|N₁| ≤ |N₂|` and `i₁` is a
candidate, then `lhs1 θ D i₁ ≥ f`. -/
theorem structure_aux (hP : P.Good n) (X : Space n m) (hd1 : ∀ j i, 1 ≤ X.d j i) {f θ : ℚ}
    (hθ : 0 < θ) (hf : n * P.η < f) {D : Fin n → ℚ} (_hD0 : ∀ j, 0 ≤ D j) {i₁ i₂ : Fin m}
    (hlo : P.δ * θ < X.dF i₁ i₂) (hhi : X.dF i₁ i₂ < θ / γ)
    (hcard : (nearSet P X θ D i₁).card ≤ (nearSet P X θ D i₂).card)
    (h₁ : Cand P X.d f P.η θ D i₁) : f ≤ lhs1 P X.d θ D i₁ := by
  have hsum := sum_le_sum fun j (_ : j ∈ univ) ↦ structure_client hP X hd1 hθ D hlo hhi j
  rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib, sum_ite_mem_eq, sum_ite_mem_eq,
    sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul] at hsum
  change _ ≤ lhs1 P X.d θ D i₁ - candSum P X.d θ D i₁ at hsum
  unfold Cand at h₁
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, j₀ ∈ nearSet P X θ D i₁ ∨
      0 < bid (cval P θ D j₀) ((1 - P.δ / 2) * X.d j₀ i₁) := by
    by_contra hne
    push Not at hne
    have : candSum P X.d θ D i₁ ≤ 0 := sum_nonpos fun j _ ↦ (hne j).2
    linarith
  have hnη : 0 ≤ (n : ℚ) * P.η := mul_nonneg (Nat.cast_nonneg n) hP.η_nonneg
  have hb := single_le_sum (s := univ) (fun j _ ↦ ?_) (mem_univ j₀) (f := fun j ↦
    if j ∈ nearSet P X θ D i₁ ∨ 0 < bid (cval P θ D j) ((1 - P.δ / 2) * X.d j i₁)
      then (n : ℚ) * P.η else 0)
  · rw [if_pos hj₀] at hb
    have hcd : ((nearSet P X θ D i₁).card : ℚ) * (P.ε ^ 2 * θ) ≤
        (nearSet P X θ D i₂).card * (P.ε ^ 2 * θ) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    linarith
  · split_ifs
    · exact hnη
    · exact le_rfl

/-- **The structure lemma** ([BCFGJPSSV26a, Lemma E.7]). -/
theorem structure_lemma (hP : P.Good n) (X : Space n m) (hd1 : ∀ j i, 1 ≤ X.d j i) {f θ : ℚ}
    (hθ : 0 < θ) (hf : n * P.η < f) {D D₀ : Fin n → ℚ} (hD0 : ∀ j, 0 ≤ D j) (hD : D ≤ D₀)
    (hmax : ∀ i, ¬ Open1 P X.d f 0 θ D₀ i) {i₁ i₂ : Fin m} (h₁ : Cand P X.d f P.η θ D i₁)
    (h₂ : Cand P X.d f P.η θ D i₂) : X.dF i₁ i₂ ≤ P.δ * θ ∨ θ / γ ≤ X.dF i₁ i₂ := by
  by_contra hc
  push Not at hc
  obtain ⟨hlo, hhi⟩ := hc
  have hmax' : ∀ i, lhs1 P X.d θ D i < f := fun i ↦ by
    have h := hmax i
    unfold Open1 at h
    rw [mul_zero, sub_zero, not_le] at h
    exact (lhs1_mono hP hD).trans_lt h
  rcases le_total (nearSet P X θ D i₁).card (nearSet P X θ D i₂).card with hcard | hcard
  · exact absurd (structure_aux hP X hd1 hθ hf hD0 hlo hhi hcard h₁) (not_le.2 (hmax' i₁))
  · rw [X.dF_comm] at hlo hhi
    exact absurd (structure_aux hP X hd1 hθ hf hD0 hlo hhi hcard h₂) (not_le.2 (hmax' i₂))

end BCFGJPSSV26.Greedy


