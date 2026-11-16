-- Prove2me | Definitions.Def_GoldProxGap_Supplement_treeM
-- name    : GoldProxGap_Supplement_treeM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:45:42.266232+00:00
-- url     : https://prove2.me/theorems/18d32796-f666-4813-a196-736afd0eb48b
-- title:
--   The tree-function counts $C_h$ and $M_h(d)$ (Lemmas 6.6 and 6.9)
-- statement:
--   For $h\ge2$ put $t_h=2^h-1$. A **height-$h$ tree function** on a binary vector space is a Boolean function computed by a decision tree of height $h$ whose two subtrees use independent linear functionals (Definition 6.3); $C_h$ is the number of them with a prescribed essential dual space, and $M_h(d)$ is the number of those on a $d$-dimensional space that avoid a fixed subspace $W$ of codimension $h+1$ (Definition 6.8). Lemmas 6.6 and 6.9 compute them by the recurrences
--
--   $$
--   C_2=56,\qquad C_h=(2^{t_h}-1)\begin{bmatrix}2t_{h-1}\\ t_{h-1}\end{bmatrix}_2 2^{t_{h-1}^2}\,C_{h-1}^2\quad(h\ge3),
--   $$
--
--   $$
--   M_2(d)=28\bigl(6\cdot2^{d-3}-5\bigr),\qquad M_h(d)=(2^{h+1}-1)\,M_{h-1}(d-1)\,2^{t_{h-1}^2}\begin{bmatrix}d-1-t_{h-1}\\ t_{h-1}\end{bmatrix}_2 C_{h-1}\quad(h\ge3),
--   $$
--
--   where $\begin{bmatrix}a\\ b\end{bmatrix}_2$ is the Gaussian binomial coefficient at $q=2$. This module defines $t_h$, $C_h$ and $M_h(d)$ by these recurrences.
--
--   $M_h(d)$ is the number of agreement sets in the rate-$1/2$ decision-tree construction (Theorem 6.10); its order of growth $\Theta_h(2^{d(2^h-h-1)})$ is what makes that construction give polynomially many exceptional challenges of degree $2^h-h-1$.
--
--   **Formalization Note** The recurrence of Lemma 6.9 is taken as the definition of $M_h(d)$ (Lemma 6.9 proves that it counts the $W$-avoiding tree functions). The values are real numbers, with the published real-valued Gaussian binomial `HScattered.Hyperplanes.gaussBinom 2`. Outside the paper's range ($h\le1$, or $h=2$ with $d<3$, where $d-3$ truncates to $0$) the value is a placeholder that no statement uses: every statement assumes $h\ge3$ and $d\ge t_h$, so each recursive call has $d-1\ge 2t_{h-1}$.
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9ced…), Definition 6.3 (p.53), Lemma 6.6 (p.54), Definition 6.8 and Lemma 6.9 (p.55)

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_gaussBinom

namespace GoldProxGap.Supplement

/-!
# The tree-function counts `C_h` and `M_h(d)` (Lemmas 6.6 and 6.9)

Dao, Kominers, Thaler, Zheng, *Counterexamples to Beyond-Johnson Proximity Gaps over Binary
Fields*, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9ced…), §6.2–6.3,
Lemma 6.6 (p.54) and Lemma 6.9 (p.55).

**Formalization Note.**
* `treeDim h = t_h = 2^h − 1` (Definition 6.3, p.53).
* `treeC h` is the number `C_h` of height-`h` tree functions with a prescribed essential dual
  space, given by Lemma 6.6: `C₂ = 56`,
  `C_h = (2^{t_h} − 1)·[2t_{h−1} t_{h−1}]₂·2^{t_{h−1}²}·C_{h−1}²` for `h ≥ 3`.
* `treeM h d` is the number `M_h(d)` of Lemma 6.9, given by the recurrence printed there:
  `M₂(d) = 28(6·2^{d−3} − 5)`,
  `M_h(d) = (2^{h+1} − 1)·M_{h−1}(d − 1)·2^{t_{h−1}²}·[d − 1 − t_{h−1} t_{h−1}]₂·C_{h−1}` for
  `h ≥ 3`. Lemma 6.9 states that this recurrence counts the `W`-avoiding height-`h` tree
  functions (Definition 6.8) on a binary space of dimension `d ≥ t_h`; the recurrence itself is
  taken as the definition here.
* `[a b]₂` is the published real-valued Gaussian binomial `HScattered.Hyperplanes.gaussBinom 2`.
* The paper defines these numbers only for `h ≥ 2` and `d ≥ t_h`. For `h ≤ 1` the value is `0`,
  and for `h = 2`, `d < 3` the natural-number exponent `d − 3` truncates to `0`; these values are
  never used (every statement assumes `h ≥ 3` and `d ≥ t_h`, whence `d − 1 ≥ 2t_{h−1} ≥ 3` in each
  recursive call).
-/

/-- `t_h = 2^h − 1`, the essential dimension of a height-`h` tree function (Definition 6.3). -/
def treeDim (h : ℕ) : ℕ := 2 ^ h - 1

/-- Lemma 6.6: `C₂ = 56` and `C_h = (2^{t_h} − 1)·[2t_{h−1} t_{h−1}]₂·2^{t_{h−1}²}·C_{h−1}²`
for `h ≥ 3` (value `0` for `h ≤ 1`, outside the paper's range). -/
noncomputable def treeC : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 56
  | (k + 3) => ((2 : ℝ) ^ treeDim (k + 3) - 1) *
      HScattered.Hyperplanes.gaussBinom 2 (2 * treeDim (k + 2)) (treeDim (k + 2)) *
      (2 : ℝ) ^ (treeDim (k + 2) ^ 2) * treeC (k + 2) ^ 2

/-- Lemma 6.9: `M₂(d) = 28(6·2^{d−3} − 5)` and
`M_h(d) = (2^{h+1} − 1)·M_{h−1}(d − 1)·2^{t_{h−1}²}·[d − 1 − t_{h−1} t_{h−1}]₂·C_{h−1}` for `h ≥ 3`
(value `0` for `h ≤ 1`, outside the paper's range). -/
noncomputable def treeM : ℕ → ℕ → ℝ
  | 0, _ => 0
  | 1, _ => 0
  | 2, d => 28 * (6 * (2 : ℝ) ^ (d - 3) - 5)
  | (k + 3), d => ((2 : ℝ) ^ (k + 4) - 1) * treeM (k + 2) (d - 1) *
      (2 : ℝ) ^ (treeDim (k + 2) ^ 2) *
      HScattered.Hyperplanes.gaussBinom 2 (d - 1 - treeDim (k + 2)) (treeDim (k + 2)) *
      treeC (k + 2)

end GoldProxGap.Supplement


