-- Prove2me | Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveIntervals
-- name    : ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveIntervals
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:08:57.695197+00:00
-- url     : https://prove2.me/theorems/06ea1ef0-3a16-4885-86f0-d3c2e97b769c
-- title:
--   The extremal three-interval instance $[0,1],[1,1+u_1],[1+u_1,1+u_1+u_2]$ (chain (17))
-- statement:
--   Let $u_1\in(0,1)$ be the root of $\Phi$ (`uOne`, with $1/2<u_1<3/5$) and $u_2=u_1^2(1+u_1)$.
--
--   - `extremalInstance`: the interval-selection instance with $N=2$, i.e. three intervals $[\ell_j,r_j]$:
--    $$[0,1],\quad [1,1+u_1],\quad [1+u_1,\;1+u_1+u_2],$$
--    with probabilities
--    $$\Bigl(u_2,\;\frac{u_2}{u_1}-u_2,\;1-\frac{u_2}{u_1}\Bigr).$$
--    The intervals are consecutive ($\ell_{j+1}=r_j$, $\ell_0=0$) and have lengths $1,u_1,u_2$. After scaling all endpoints by $1/u_2$ this is the extremal chain (17) with $d_0=1/u_2$, $d_1=u_1/u_2$, $d_2=1$. The fields requiring $0\le\ell_j\le r_j$, nonnegative probabilities and total mass $1$ are proved from $0<u_1<3/5$ and the identity $u_2/u_1=u_1(1+u_1)$.
--
--   The file also proves the identity $u_1^2(1+u_1)/u_1=u_1(1+u_1)$.
--
--   This instance attains the optimal adaptivity gap $\xi^\star$ among nonincreasing consecutive intervals with the equalizing distribution (Lemma 4), and so serves as the tightness example for the randomized ratio.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/ConsecutiveIntervals.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_EqualizingDistribution

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

theorem uTwo_div_uOne : uOne ^ 2 * (1 + uOne) / uOne = uOne * (1 + uOne) := by
  have := uOne_pos
  field_simp

/-- The three intervals `[0, 1]`, `[1, 1 + u₁]`, `[1 + u₁, 1 + u₁ + u₂]` with the
probabilities `(u₂, u₂/u₁ - u₂, 1 - u₂/u₁)`: the extremal chain (17)
`d_0 = 1/u₂`, `d_1 = u₁/u₂`, `d_2 = 1`, with all endpoints scaled by `u₂`. -/
def extremalInstance : IntervalInstance 2 where
  left := ![0, 1, 1 + uOne]
  right := ![1, 1 + uOne, 1 + uOne + uOne ^ 2 * (1 + uOne)]
  prob := ![uOne ^ 2 * (1 + uOne), uOne ^ 2 * (1 + uOne) / uOne - uOne ^ 2 * (1 + uOne),
    1 - uOne ^ 2 * (1 + uOne) / uOne]
  left_nonneg i := by
    have := uOne_pos
    fin_cases i
    · simp
    · simp
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      linarith
  left_le_right i := by
    have := uOne_pos
    fin_cases i
    · simp
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      linarith
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      nlinarith
  prob_nonneg i := by
    have h0 := uOne_pos
    have hb := uOne_bounds
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      positivity
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, uTwo_div_uOne]
      nlinarith
    · simp only [Fin.reduceFinMk, Matrix.cons_val, uTwo_div_uOne]
      nlinarith
  prob_sum := by
    simp [Fin.sum_univ_succ]

end ConsistentSubmodular.Chains

end


