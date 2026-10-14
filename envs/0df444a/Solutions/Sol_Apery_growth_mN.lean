-- Prove2me | solution 1 for Apery.growth_mN
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T14:22:39.499793+00:00
-- url     : https://prove2.me/submissions/d949aa6c-b0f8-4087-887a-5dcf740cb755

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# Growth of the normaliser $m_K$ (Proposition 5.2) — reduction to the four prime ranges and PNT

This file proves the platform theorem `Apery.growth_mN`:

$$\forall \varepsilon>0,\quad \log m_K \le (A_{\mathrm{eff}}+\varepsilon)\,K^2
\quad\text{for all large } n,\qquad K=40n,\ A_{\mathrm{eff}} = 136/100,$$

from the imported children

* `Apery.small_range_le` — the small primes $p \le K/400$ (PNT-free);
* `Apery.low_order` — the lower-order terms are $o(K^2)$ (PNT-free);
* `Apery.theta_eventually_close` — the prime number theorem in $\varepsilon$-form;
* `Apery.range_tail`, `Apery.range_inner`, `Apery.range_outer` — the exact table (5.18) and
  the outer table over $K/400 < p \le K/20$, $K/20 < p \le K/3$, $K/3 < p \le 2h$.

Everything else is proved here: the splitting $\log m_K = \sum_{k\le 2h} c(k)(-L_k)$, the
four-range decomposition of that sum, and the numerical assembly with the source's constants
$-6843153/128000000$, $322437603634266857629/7535670527041937280000$, $129101/96000$,
$22.2/1600$. A faithful port of mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0,
`Apery/Growth/Assembly1.lean` (`log_mN`, `sum_split4`) and `Apery/Growth.lean`.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceNorm
import Definitions.Def_Zeta5_SourcePrimeSum
import Theorems.Thm_Apery_small_range_le
import Theorems.Thm_Apery_low_order
import Theorems.Thm_Apery_theta_eventually_close
import Theorems.Thm_Apery_range_tail
import Theorems.Thm_Apery_range_inner
import Theorems.Thm_Apery_range_outer

set_option autoImplicit false

section Port0
/-!
# Growth of the normaliser — reduction to the four prime-range estimates and PNT

This file proves the platform theorem `Apery.growth_mN`:

`∀ ε > 0, ∀ᶠ n, log (mN n) ≤ (A_eff + ε) K²`,   `K = 40 n`, `A_eff = 136/100`,

from the children

* `Apery.small_range_le` (the small primes `p ≤ K/400`, PNT-free);
* `Apery.low_order` (the lower-order terms are `o(K²)`, PNT-free);
* `Apery.theta_eventually_close` (the prime number theorem in `ε`-form);
* `Apery.range_tail`, `Apery.range_inner`, `Apery.range_outer` (the exact table and the
  outer table over `K/400 < p ≤ K/20`, `K/20 < p ≤ K/3`, `K/3 < p ≤ 2h`).

The splitting `log m_K = ∑_{k ≤ 2h} c(k) (-L_k)` and the four-range decomposition of the sum
are proved here; the numerics are the source's constants
`-6843153/128000000`, `322437603634266857629/7535670527041937280000`, `129101/96000` and
`22.2/1600`. Ported from mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0,
`Apery/Growth/Assembly1.lean` (`log_mN`, `sum_split4`) and `Apery/Growth.lean`.
-/

open Finset Filter

namespace Apery

/-- `log m_K = ∑_{k ≤ 2h} c(k) (-L_k)`. -/
lemma log_mN (n : ℕ) : Real.log (mN n : ℝ) =
    ∑ k ∈ Icc 1 (2 * (37 * n)), cPrime k * (-(Lp n k : ℝ)) := by
  unfold mN
  push_cast
  rw [Real.log_prod (fun p hp => by
    have := (Finset.mem_filter.mp hp).2.pos
    exact zpow_ne_zero _ (by exact_mod_cast this.ne'))]
  simp only [Real.log_zpow]
  rw [Finset.sum_filter]
  have e : range (2 * (37 * n) + 1) = insert 0 (Icc 1 (2 * (37 * n))) := by
    ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [e, Finset.sum_insert (by simp)]
  simp only [Nat.not_prime_zero, if_false, zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold cPrime
  split_ifs <;> push_cast <;> ring

/-- Splitting `(0, N]` at `a ≤ b ≤ c`. -/
lemma sum_split4 (F : ℕ → ℝ) {a b c N : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (hcN : c ≤ N) :
    ∑ k ∈ Icc 1 N, F k = ∑ k ∈ Ioc 0 a, F k + ∑ k ∈ Ioc a b, F k + ∑ k ∈ Ioc b c, F k +
      ∑ k ∈ Ioc c N, F k := by
  have e : Icc 1 N = Ioc 0 N := by ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [e, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) (hab.trans (hbc.trans hcN)),
    ← Finset.sum_Ioc_consecutive _ hab (hbc.trans hcN), ← Finset.sum_Ioc_consecutive _ hbc hcN]
  ring

/-- **Growth of the normaliser**, from the four range estimates and the prime number theorem. -/
theorem growth_mN :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, Real.log (mN n) ≤ ((Aeff : ℝ) + ε) * Kr n ^ 2 := by
  intro ε hε
  have hδ : (0 : ℝ) < 1 / 10000 := by norm_num
  have hKr : Tendsto Kr atTop atTop :=
    (tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num : (0 : ℝ) < 40)
  have hy10 : Tendsto (fun n : ℕ => ((n / 10 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (Nat.tendsto_div_const_atTop (by norm_num))
  have Eθ := hy10.eventually (theta_eventually_close hδ)
  filter_upwards [range_tail (1 / 10000) hδ, range_inner (1 / 10000) hδ,
    range_outer (1 / 10000) hδ, Eθ, low_order hδ,
    eventually_ge_atTop 10400] with n h2 h3 h4 hθ hlow hn
  have hK0 : 0 < Kr n ^ 2 := by
    simp only [Kr]
    have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    positivity
  have hK : Kr n ^ 2 = 1600 * (n : ℝ) ^ 2 := by simp only [Kr]; ring
  rw [log_mN, sum_split4 _ (a := n / 10) (b := 2 * n) (c := 40 * n / 3) (N := 2 * (37 * n))
    (by omega) (by omega) (by omega)]
  have r1 := small_range_le n (by omega)
  -- the `θ` term of the small range
  have hθ1 : Chebyshev.theta ((n / 10 : ℕ) : ℝ) ≤ (1 + 1 / 10000) * (n / 10 : ℝ) := by
    have h10 : ((n / 10 : ℕ) : ℝ) ≤ (n : ℝ) / 10 := by
      rw [le_div_iff₀ (by norm_num)]; exact_mod_cast (Nat.div_mul_le_self n 10)
    have := (abs_le.mp hθ).2
    nlinarith [mul_le_mul_of_nonneg_left h10 (by norm_num : (0 : ℝ) ≤ 1 + 1 / 10000)]
  have i1 : 6 * (37 * (n : ℝ)) * Chebyshev.theta ((n / 10 : ℕ) : ℝ) ≤
      22.2 * (1 + 1 / 10000) / 1600 * Kr n ^ 2 := by
    have hmain : 6 * (37 * (n : ℝ)) * ((1 + 1 / 10000) * (n / 10)) =
        22.2 * (1 + 1 / 10000) / 1600 * Kr n ^ 2 := by rw [hK]; ring
    rw [← hmain]
    exact mul_le_mul_of_nonneg_left hθ1 (by positivity)
  -- absorb the lower-order terms of the small range
  have hlow' : 6 * (37 * (n : ℝ)) * ((Real.sqrt (200 * n) + 1) * Real.log (200 * n)) + 3700 * n ≤
      (1 / 10000) * Kr n ^ 2 := by
    have : (3700 : ℝ) * n ≤ 3 * 10 ^ 9 * n := by
      nlinarith [show (0 : ℝ) ≤ n by positivity]
    linarith
  have rs : ∑ k ∈ Ioc 0 (n / 10), cPrime k * (-(Lp n k : ℝ)) ≤
      22.2 * (1 + 1 / 10000) / 1600 * Kr n ^ 2 + (1 / 10000) * Kr n ^ 2 := by
    have hX : 6 * (37 * (n : ℝ)) * (Chebyshev.theta ((n / 10 : ℕ) : ℝ) +
        (Real.sqrt (200 * n) + 1) * Real.log (200 * n)) + (37 * (n : ℝ)) * 100 =
        6 * (37 * (n : ℝ)) * Chebyshev.theta ((n / 10 : ℕ) : ℝ) +
          (6 * (37 * (n : ℝ)) * ((Real.sqrt (200 * n) + 1) * Real.log (200 * n)) +
            3700 * (n : ℝ)) := by
      ring
    rw [hX] at r1
    linarith only [r1, i1, hlow']
  have hA : (Aeff : ℝ) = 136 / 100 := by unfold Aeff; norm_num
  have hcoef : 22.2 * (1 + 1 / 10000) / 1600 + 1 / 10000 + (-6843153 / 128000000 + 1 / 10000) +
      (322437603634266857629 / 7535670527041937280000 + 1 / 10000) +
      (129101 / 96000 + 1 / 10000) ≤ (136 / 100 : ℝ) - 1 / 1000 := by
    norm_num
  have hfin := mul_le_mul_of_nonneg_right hcoef hK0.le
  have hεK : (0 : ℝ) ≤ ε * Kr n ^ 2 := mul_nonneg hε.le hK0.le
  rw [hA]
  nlinarith only [hfin, rs, h2, h3, h4, hεK]

end Apery
end Port0


open Filter in
/-- The platform target `Apery.growth_mN`, restated at top level as `solution`. -/
theorem solution :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      Real.log (Apery.mN n) ≤ ((Apery.Aeff : ℝ) + ε) * Apery.Kr n ^ 2 :=
  Apery.growth_mN
