-- Prove2me | Definitions.Def_TightClock_hardPrior
-- name    : TightClock_hardPrior
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:57:15.001851+00:00
-- url     : https://prove2.me/theorems/70a8a5c2-dd1d-4d4b-96bd-df2d0efb981b
-- title:
--   The value law $D$ of the hard instance
-- statement:
--   The prior $D$ of the instance: value $y_j=M^{-j}$ with probability $p_j$ of (6.2), for $j=0,\dots,L$. All bidders draw from it independently.
--
--   **Formalization Note** The values $y_j$ are distinct because $M>1$, so each support point carries exactly one $p_j$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, p.35 (PDF p.38), eq. (6.2)

import Mathlib
import Definitions.Def_TightClock_FinitePrior
import Definitions.Def_TightClock_y
import Definitions.Def_TightClock_tierProb

set_option autoImplicit false

namespace TightClock

private theorem rho_pos (q L : ℕ) (hq : 8 ≤ q) (hL : 1 ≤ L) : 0 < rho q L := by
  have h1 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have h2 : (0 : ℝ) < (M q L : ℝ) := by
    have : 0 < M q L := Nat.mul_pos (by omega) (pow_pos (by omega) 4)
    exact_mod_cast this
  unfold rho a
  positivity

private theorem one_lt_M (q L : ℕ) (hq : 8 ≤ q) (hL : 1 ≤ L) : (1 : ℝ) < (M q L : ℝ) := by
  have h : 1 < M q L := by
    have h1 : 1 ≤ L := hL
    have h2 : 8 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
    unfold M
    nlinarith
  exact_mod_cast h

private theorem rho_lt_one (q L : ℕ) (hq : 8 ≤ q) (hL : 1 ≤ L) : rho q L < 1 := by
  have h1 : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have h2 := one_lt_M q L hq hL
  have h3 : a q < 1 := by
    unfold a
    rw [div_lt_one (by linarith)]
    exact h1
  have h4 : 0 < a q := by unfold a; positivity
  unfold rho
  rw [div_lt_one (by linarith)]
  linarith

private theorem y_injective (q L : ℕ) (hq : 8 ≤ q) (hL : 1 ≤ L) : Function.Injective (y q L) := by
  have h := one_lt_M q L hq hL
  have h0 : (0 : ℝ) < (M q L : ℝ)⁻¹ := by positivity
  have h1 : (M q L : ℝ)⁻¹ ≠ 1 := by
    intro he
    have := inv_lt_one_of_one_lt₀ h
    linarith
  intro i j hij
  exact pow_right_injective₀ h0 h1 hij

private theorem tierProb_pos (q L j : ℕ) (hq : 8 ≤ q) (hL : 1 ≤ L) : 0 < tierProb q L j := by
  have h0 := rho_pos q L hq hL
  have h1 := rho_lt_one q L hq hL
  unfold tierProb
  split_ifs
  · positivity
  · have : 0 < 1 - rho q L := by linarith
    positivity

private theorem tierProb_sum (q L : ℕ) :
    ∑ j ∈ Finset.range (L + 1), tierProb q L j = 1 := by
  rw [Finset.sum_range_succ']
  have h : ∀ j ∈ Finset.range L, tierProb q L (j + 1) = (1 - rho q L) * (rho q L) ^ (L - 1 - j) := by
    intro j hj
    have hj' : j < L := Finset.mem_range.mp hj
    unfold tierProb
    rw [if_neg (by omega)]
    congr 2
    omega
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, Finset.sum_range_reflect (fun j => (rho q L) ^ j) L,
    mul_neg_geom_sum]
  simp [tierProb]

private theorem weight_at (q L j : ℕ) (hq : 8 ≤ q) (hL : 1 ≤ L) (hj : j ∈ Finset.range (L + 1)) :
    (∑ k ∈ Finset.range (L + 1), if y q L j = y q L k then tierProb q L k else 0)
      = tierProb q L j := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    rw [if_neg]
    intro he
    exact hk (y_injective q L hq hL he).symm
  · intro hn
    exact absurd hj hn

/-- The law `D` of one bidder's value: value `y_j` with probability `p_j` of (6.2). Afshinmehr et al.,
manuscript (STOC 2027 submission), §6.2, p.35 (PDF 38): "Let D denote the resulting distribution of bidder
values."

**Formalization Note** The `y_j` are distinct, since `M > 1`, so the weight at a support point is one `p_j`.
The verification file records its grid witness `δ = M⁻ᴸ`. -/
noncomputable def hardPrior (q L : ℕ) (hq : 8 ≤ q) (hL : 1 ≤ L) : FinitePrior where
  support := (Finset.range (L + 1)).image (y q L)
  weight := fun x => ∑ k ∈ Finset.range (L + 1), if x = y q L k then tierProb q L k else 0
  nonneg := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    unfold y
    positivity
  weight_pos := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    rw [weight_at q L j hq hL hj]
    exact tierProb_pos q L j hq hL
  weight_sum := by
    rw [Finset.sum_image (fun i _ j _ hij => y_injective q L hq hL hij)]
    rw [Finset.sum_congr rfl (fun j hj => weight_at q L j hq hL hj)]
    exact tierProb_sum q L

end TightClock


