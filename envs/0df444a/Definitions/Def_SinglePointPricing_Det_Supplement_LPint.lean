-- Prove2me | Definitions.Def_SinglePointPricing_Det_Supplement_LPint
-- name    : SinglePointPricing_Det_Supplement_LPint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T17:30:59.724216+00:00
-- url     : https://prove2.me/theorems/77b4170c-ab85-4b09-8344-e3cd3a131f12
-- title:
--   (LP-int) (corrected: indexing and terminal oracle) — interval-information linear program
-- statement:
--   Fix $0<q_l<q_h<1$, $\alpha\in[0,1]$, $w>0$ and $N\ge1$. Use the proof's grid $A=(a_0,\ldots,a_{2N+1})$, with positive strictly increasing entries and $a_N<w=a_{N+1}$. Set $q_i=q_l$ for $i\le N$ and $q_i=q_h$ otherwise. The row normalizers are
--   $$
--   d_i=\begin{cases}
--   \lim_{r\uparrow a_{i+1}}\operatorname{opt}(F_\alpha(\cdot\mid r,(w,q_l))),&0\le i\le N,\\
--   \operatorname{opt}(F_\alpha(\cdot\mid a_{i+1},(w,q_h))),&N<i<2N+1,\\
--   w\widetilde v_\alpha/\Gamma_\alpha^{-1}(q_h),&i=2N+1.
--   \end{cases}
--   $$
--   The program is
--   $$
--   \underline L_{\alpha,q_l,q_h,A}=\sup\left\{c:p_j\ge0,\ \sum_{j=0}^{2N+1}p_j\le1,\quad c\le\frac{\sum_{j=0}^{2N+1}a_j\overline F_\alpha(a_j\mid a_i,(w,q_i))p_j}{d_i}\quad(0\le i\le2N+1)\right\}.
--   $$
--   This is the factor-revealing LP of (F-2), with a genuine supremum of explicit linear constraints. Theorem 4 asserts its attainment and relation to the interval-information maximin ratio. The underlying interval class is also imported.
--
--   **Formalization Note** Main-text indexing is inconsistent and omits the top point; the index ranges follow (F-2), pp. App-40–41. The main-text grid $a_1,\ldots,a_{2n}$, $n>1$, is this grid with $N=n-1\ge1$. The terminal oracle uses the same saturated high-branch convention as the point-information LP, including the infinite endpoint at $\alpha=0$ and the empty high-parameter regime at $\overline r_\alpha<w$.
-- source:
--   Allouah, Bahamou & Besbes, Optimal Pricing with a Single Point, arXiv:2103.05611v2, (LP-int), p. 30; (F-2), pp. App-40–41

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Supplement_LP
import Definitions.Def_SinglePointPricing_Det_Supplement_Interval

namespace SinglePointPricing.Det.Supplement

noncomputable section

/-- (LP-int)/(F-2): low rows use `ql`, high rows use `qh`. -/
def rowQuantile (ql qh : ℝ) (N i : ℕ) : ℝ := if i ≤ N then ql else qh

/-- Low rows use left limits, high rows the next endpoint value; the final
row uses the saturated high-branch oracle, including `α=0`. -/
def lpIntNorm (α w ql qh : ℝ) (a : ℕ → ℝ) (N i : ℕ) : ℝ :=
  if i ≤ N then leftOracle α w ql (a (i + 1))
  else if i < 2 * N + 1 then optFun (Fbar α w qh (a (i + 1)))
  else topOracle α w qh

/-- The proof's zero-based form (F-2) of the interval LP: `2N+2` points/rows. -/
def LPintFeasible (α w ql qh : ℝ) (a : ℕ → ℝ) (N : ℕ)
    (p : ℕ → ℝ) (c : ℝ) : Prop :=
  (∀ j < 2 * N + 2, 0 ≤ p j) ∧
  (∑ j ∈ Finset.range (2 * N + 2), p j) ≤ 1 ∧
  ∀ i < 2 * N + 2, c ≤
    (∑ j ∈ Finset.range (2 * N + 2),
      a j * Fbar α w (rowQuantile ql qh N i) (a i) (a j) * p j) /
      lpIntNorm α w ql qh a N i

/-- Value of (LP-int), not a surrogate maximin problem. -/
def LPintVal (α w ql qh : ℝ) (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  sSup {c : ℝ | ∃ p : ℕ → ℝ, LPintFeasible α w ql qh a N p c}

end
end SinglePointPricing.Det.Supplement


