-- Prove2me | Definitions.Def_MeasureTheory_ScalingDichotomy
-- name    : MeasureTheory_ScalingDichotomy
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/b0cf9124-68a9-5d8f-917e-11d665a56e8f
-- title:
--   Scaling slices and a zero-or-infinite measure dichotomy
-- statement:
--   For a type $G$, a subset $D \subseteq G$, a function $f : G \to \mathbb{R}$, a real $r$ and $k \in \mathbb{Z}$, `zpowSlice D f r k` is defined as $D \cap f^{-1}\bigl([r^k, r^{k+1})\bigr)$, the part of $D$ on which $f$ lies in the half-open interval between consecutive integral powers of $r$ (the powers are `zpow`, so negative $k$ are allowed). Four lemmas record the elementary properties of these slices, each with the minimal assumptions: `iUnion_zpowSlice` says that if $r > 1$ and $f > 0$ on $D$ then $\bigcup_{k \in \mathbb{Z}} \mathrm{zpowSlice}\,D\,f\,r\,k = D$; `pairwise_disjoint_zpowSlice` says that for $r > 1$ the slices are pairwise disjoint (no positivity needed); `measurableSet_zpowSlice` says that for a measurable space $G$, a measurable set $D$ and a measurable $f$ each slice is measurable; and `preimage_mul_zpowSlice_succ` says that if $G$ merely carries a multiplication, $r > 1$, and $z \in G$ satisfies the global scaling law $f(zg) = r f(g)$ for all $g \in G$ together with $(g \mapsto zg)^{-1}(D) = D$, then $(g \mapsto zg)^{-1}\bigl(\mathrm{zpowSlice}\,D\,f\,r\,(k+1)\bigr) = \mathrm{zpowSlice}\,D\,f\,r\,k$; the scaling law is assumed on all of $G$, not only on $D$.
--
--   The main statement `measure_eq_zero_or_top_of_mul_preimage_eq` assumes $G$ a group with a measurable space structure for which multiplication is measurable, $\mu$ a left-invariant measure on $G$, $f : G \to \mathbb{R}$ measurable, $r > 1$, an element $z$ with $f(zg) = r f(g)$ for all $g$, and a measurable set $D$ with $f > 0$ on $D$ and $(g \mapsto zg)^{-1}(D) = D$; the conclusion is the dichotomy $\mu(D) = 0$ or $\mu(D) = \infty$. All the slices have a common measure by left invariance, and $\mu(D)$ is the sum over $\mathbb{Z}$ of that constant.
--
--   **Relation to Mathlib.** Built directly on `Mathlib.MeasureTheory.Group.Measure` (left-invariant measures, `measure_preimage_mul`); the slices and the dichotomy itself are the project's own, with no use of Haar uniqueness, regularity, unimodularity or σ-finiteness.
--
--   **Where it is used.** The statement is the measure-theoretic mechanism showing that a subset of a group stable under an unboundedly scaling direction cannot have finite positive invariant measure — for instance a region in an adelic group stable under an archimedean central element, with $f$ an absolute value of the determinant at one infinite place. No other module of the development currently imports it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_MeasureTheory_ScalingDichotomy.lean

import Mathlib.MeasureTheory.Group.Measure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.ScalingDichotomy

section Slices

variable {G : Type*}

def zpowSlice (D : Set G) (f : G → ℝ) (r : ℝ) (k : ℤ) : Set G :=
  D ∩ f ⁻¹' Ico (r ^ k) (r ^ (k + 1))

theorem iUnion_zpowSlice {D : Set G} {f : G → ℝ} {r : ℝ} (hr : 1 < r) (hpos : ∀ g ∈ D, 0 < f g) :
    ⋃ k : ℤ, zpowSlice D f r k = D := by
  ext g
  simp only [mem_iUnion, zpowSlice, mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨k, hk, -⟩
    exact hk
  · intro hg
    obtain ⟨k, hk⟩ := exists_mem_Ico_zpow (hpos g hg) hr
    exact ⟨k, hg, hk⟩

theorem pairwise_disjoint_zpowSlice (D : Set G) (f : G → ℝ) {r : ℝ} (hr : 1 < r) :
    Pairwise (Function.onFun Disjoint (zpowSlice D f r)) := by
  intro k l hkl
  rw [Function.onFun, Set.disjoint_left]
  rintro g ⟨-, hk1, hk2⟩ ⟨-, hl1, hl2⟩
  rcases lt_or_gt_of_ne hkl with h | h
  · have : r ^ (k + 1) ≤ r ^ l := (zpow_right_strictMono₀ hr).monotone (by omega)
    exact absurd (hk2.trans_le (this.trans hl1)) (lt_irrefl _)
  · have : r ^ (l + 1) ≤ r ^ k := (zpow_right_strictMono₀ hr).monotone (by omega)
    exact absurd (hl2.trans_le (this.trans hk1)) (lt_irrefl _)

theorem measurableSet_zpowSlice [MeasurableSpace G] {D : Set G} (hD : MeasurableSet D) {f : G → ℝ} (hf : Measurable f)
    (r : ℝ) (k : ℤ) : MeasurableSet (zpowSlice D f r k) :=
  hD.inter (hf measurableSet_Ico)

theorem preimage_mul_zpowSlice_succ [Mul G] {D : Set G} {f : G → ℝ} {r : ℝ} (hr : 1 < r) {z : G}
    (hfz : ∀ g, f (z * g) = r * f g) (hzD : (fun g => z * g) ⁻¹' D = D) (k : ℤ) :
    (fun g => z * g) ⁻¹' zpowSlice D f r (k + 1) = zpowSlice D f r k := by
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
  ext g
  have hD : z * g ∈ D ↔ g ∈ D := by
    rw [← mem_preimage, hzD]
  simp only [zpowSlice, mem_preimage, mem_inter_iff, mem_Ico, hD, hfz]
  rw [zpow_add_one₀ hr0.ne' (k + 1), zpow_add_one₀ hr0.ne' k]
  constructor
  · rintro ⟨hg, h1, h2⟩
    refine ⟨hg, ?_, ?_⟩
    · rw [mul_comm] at h1
      exact le_of_mul_le_mul_left h1 hr0
    · rw [show r ^ k * r * r = r * (r ^ k * r) from by ring] at h2
      exact lt_of_mul_lt_mul_left h2 hr0.le
  · rintro ⟨hg, h1, h2⟩
    refine ⟨hg, ?_, ?_⟩
    · calc r ^ k * r = r * r ^ k := mul_comm _ _
        _ ≤ r * f g := mul_le_mul_of_nonneg_left h1 hr0.le
    · calc r * f g < r * (r ^ k * r) := mul_lt_mul_of_pos_left h2 hr0
        _ = r ^ k * r * r := by ring

end Slices

section Dichotomy

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem measure_eq_zero_or_top_of_mul_preimage_eq (μ : Measure G) [μ.IsMulLeftInvariant]
    {z : G} {f : G → ℝ} (hf : Measurable f) {r : ℝ} (hr : 1 < r)
    (hfz : ∀ g, f (z * g) = r * f g) {D : Set G} (hpos : ∀ g ∈ D, 0 < f g)
    (hD : MeasurableSet D) (hzD : (fun g => z * g) ⁻¹' D = D) :
    μ D = 0 ∨ μ D = ⊤ := by

  have hstep : ∀ k : ℤ, μ (zpowSlice D f r k) = μ (zpowSlice D f r (k + 1)) := fun k => by
    rw [← preimage_mul_zpowSlice_succ hr hfz hzD k, measure_preimage_mul]
  have hconst : ∀ k : ℤ, μ (zpowSlice D f r k) = μ (zpowSlice D f r 0) := fun k => by
    induction k using Int.induction_on with
    | zero => rfl
    | succ n ih => rw [← hstep, ih]
    | pred n ih =>
      rw [hstep, show -(n : ℤ) - 1 + 1 = -n from by ring, ih]

  have hsum : μ D = ∑' k : ℤ, μ (zpowSlice D f r k) := by
    conv_lhs => rw [← iUnion_zpowSlice hr hpos (D := D) (f := f)]
    exact measure_iUnion (pairwise_disjoint_zpowSlice D f hr)
      (measurableSet_zpowSlice hD hf r)
  rw [hsum]
  simp_rw [hconst]
  rcases eq_or_ne (μ (zpowSlice D f r 0)) 0 with h0 | h0
  · left
    simp [h0]
  · right
    exact ENNReal.tsum_const_eq_top_of_ne_zero h0

end Dichotomy

end MeasureTheory.ScalingDichotomy


