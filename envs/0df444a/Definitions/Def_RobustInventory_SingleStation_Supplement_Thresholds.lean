-- Prove2me | Definitions.Def_RobustInventory_SingleStation_Supplement_Thresholds
-- name    : RobustInventory_SingleStation_Supplement_Thresholds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:22:19.69371+00:00
-- url     : https://prove2.me/theorems/e38b7a43-4452-4e69-b298-cd839137dd8f
-- title:
--   Lemma 3.1(c), (15)–(16): ordering times $t_j$, lengths $L_j$, indices $I_j$ and thresholds $S_j$, $s_j$
-- statement:
--   This file defines the quantities in the closed-form thresholds of Lemma 3.1(c), for the single-station model with initial stock $x_0$, horizon $T$, unit ordering cost $c$, holding cost $h$ and shortage cost $p$, and a demand sequence $w$.
--
--   For an order sequence $u$, the **ordering times** $t_1<\dots<t_J$ are exactly the periods $k<T$ with $u_k>0$; by convention $t_{J+1}=T$. Put
--   $$L_j=t_{j+1}-t_j,\qquad I_j=\Big\lfloor\frac{pL_j-c\,\mathbf 1_{\{j=J\}}}{h+p}\Big\rfloor .$$
--   The thresholds (15) and (16) are
--   $$S_j=\sum_{i=0}^{I_j}w_{t_j+i},\qquad s_1=x_0-\sum_{i=0}^{t_1-1}w_i,\qquad s_j=-\sum_{i=I_{j-1}+1}^{L_{j-1}-1}w_{t_{j-1}+i}\quad(j\ge2).$$
--   The file also defines the stock before ordering in period $k$, $x_k=x_0+\sum_{i<k}(u_i-w_i)$.
--
--   The same formulas are used at the nominal demand in Lemma 3.1(c) and at the modified demand in Theorem 3.2(c).
--
--   **Formalization Note** The index $j$ runs over $1,\dots,J$, and $J=0$ is allowed. Empty sums are zero. On ordering times one has $L_j\ge1$, so the numerator in $I_j$ is positive (as $p>c$) and the natural-number floor is the integer floor.
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), pp. 154–155 (PDF 5–6), Lemma 3.1(c), Eqs. (15)–(16), and the conventions of its proof

import Definitions.Def_RobustInventory_SingleStation_Model

namespace RobustInventory.SingleStation.Supplement

open Finset

/-- `t 1 < t 2 < … < t J` are exactly the periods `k < T` with `u_k > 0`, and `t (J + 1) = T`
(the convention of the proof of Lemma 3.1(c), p. 155). Indices `j` run over `1, …, J`; the other
values of `t` are never used. -/
def IsOrderingTimes (T : ℕ) (u : ℕ → ℝ) (J : ℕ) (t : ℕ → ℕ) : Prop :=
  t (J + 1) = T ∧
    (∀ j ∈ Finset.Icc 1 J, t j < t (j + 1)) ∧
    ∀ k, (k < T ∧ 0 < u k) ↔ ∃ j ∈ Finset.Icc 1 J, t j = k

/-- `L_j = t_{j+1} - t_j`; on ordering times this difference is positive for `1 ≤ j ≤ J`. -/
def intervalLength (t : ℕ → ℕ) (j : ℕ) : ℕ := t (j + 1) - t j

/-- `I_j = ⌊(p L_j - c 1_{j = J}) / (h + p)⌋`. On ordering times and for `1 ≤ j ≤ J` the
numerator is positive (`L_j ≥ 1`, `p > c`), so the natural floor is the integer floor. -/
noncomputable def floorIndex (M : Model) (J : ℕ) (t : ℕ → ℕ) (j : ℕ) : ℕ :=
  ⌊(M.p * (intervalLength t j : ℝ) - (if j = J then M.c else 0)) / (M.h + M.p)⌋₊

/-- (15): `S_j = ∑_{i=0}^{I_j} w_{t_j + i}`, for the demand sequence `w`. -/
noncomputable def upperThreshold (M : Model) (w : ℕ → ℝ) (J : ℕ) (t : ℕ → ℕ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (floorIndex M J t j + 1), w (t j + i)

/-- (16): `s_1 = x₀ - ∑_{i=0}^{t_1 - 1} w_i` and, for `j ≥ 2`,
`s_j = -∑_{i = I_{j-1} + 1}^{L_{j-1} - 1} w_{t_{j-1} + i}` (empty sums are zero). -/
noncomputable def lowerThreshold (M : Model) (w : ℕ → ℝ) (J : ℕ) (t : ℕ → ℕ) (j : ℕ) : ℝ :=
  if j = 1 then M.x0 - ∑ i ∈ Finset.range (t 1), w i
  else -∑ i ∈ Finset.Ico (floorIndex M J t (j - 1) + 1) (intervalLength t (j - 1)),
    w (t (j - 1) + i)

/-- The stock `x_k = x₀ + ∑_{i<k} (u_i - w_i)` at the beginning of period `k`, before ordering. -/
def stockBefore (M : Model) (w u : ℕ → ℝ) (k : ℕ) : ℝ :=
  M.x0 + ∑ i ∈ Finset.range k, (u i - w i)

end RobustInventory.SingleStation.Supplement


