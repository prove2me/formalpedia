-- Prove2me | Definitions.Def_RecoveringBandits_IsAlg2Run
-- name    : RecoveringBandits_IsAlg2Run
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:56:47.830028+00:00
-- url     : https://prove2.me/theorems/bfbb632a-6ee4-4a2e-8ae5-208c84c9e06c
-- title:
--   Outputs of Algorithm 2 (Offline Purely Periodic Planning)
-- statement:
--   A policy $\pi$ is an **output of Algorithm 2** when there are
--
--   1. an optimal solution $x^*$ of problem (3) with the property of Lemma 2 (line 5);
--   2. a maximizer $a^*\ge1$ of $\frac{aK}{(a+1)(K+a)}$ (line 2);
--
--   and $\pi$ is an output of R-S$(x,K,a^*)$ (line 9), where $x_i=\min\{y\ge x^*_i:\ 1/y\in\{d^{(k)}_i\}_{k\ge1}\cup\{+\infty\}\}$ (line 7): $x_i=0$ if $x^*_i=0$, and otherwise $x_i=1/d^{(k)}_i$ for the largest $k$ with $1/d^{(k)}_i\ge x^*_i$.
--
--   **Formalization Note** Lines 3–4 compute objects that are definitions here. Every choice the algorithm leaves open (the optimal $x^*$, the maximizer $a^*$, every choice inside R-S) is left free. The lift of line 7 is defined as an infimum; under the property of Lemma 2 its set is finite and nonempty.
-- source:
--   Simchi-Levi–Zheng–Zhu, Offline Planning and Online Learning under Recovering Rewards, arXiv:2106.14813v2, Algorithm 2, pp.14–15; §4.3, p.14

import Mathlib
import Definitions.Def_RecoveringBandits_UB
import Definitions.Def_RecoveringBandits_Lemma2Prop
import Definitions.Def_RecoveringBandits_IsRSRun

namespace RecoveringBandits

/-- **Line 7 of Algorithm 2** (arXiv:2106.14813v2, Algorithm 2, line 7, p.14; §4.3, p.14):
`x_i ← min {y ≥ x*_i : 1/y ∈ {d^{(k)}_i}_{k ≥ 1} ∪ {+∞}}`. For `x*_i = 0` this is `0`
(`1/0 = +∞`); for `x*_i ∈ (0, 1/d^{(1)}_i]` it is `1/d^{(k)}_i` for the largest `k ≥ 1` with
`1/d^{(k)}_i ≥ x*_i`.

**Formalization Note.** For `0 < v ≤ 1/d^{(1)}_i` the set below is finite and nonempty (the
supporting points increase strictly), so `sInf` is its minimum. It is applied only to an `x*`
with the property of Lemma 2, so `v > 1/d^{(1)}_i` (where the set is empty) never occurs. -/
noncomputable def lift (r : ℕ → ℝ) (v : ℝ) : ℝ :=
  if v = 0 then 0 else sInf {y : ℝ | v ≤ y ∧ ∃ k : ℕ, 1 ≤ k ∧ y = 1 / (supp r k : ℝ)}

/-- **`π` is an output of Algorithm 2** (Offline Purely Periodic Planning,
arXiv:2106.14813v2, Algorithm 2, pp.14–15): there are an optimal solution `x*` of (3) with the
property of Lemma 2 (line 5), a maximizer `a* ≥ 1` of `a·K / ((a+1)(K+a))` (line 2), and `π` is
an output of R-S(x, K, a*) (line 9), where `x` is the lift of `x*` by line 7.

**Formalization Note.** Lines 3–4 (initializing the supporting points and `F_i`) compute objects
that are definitions here (`supp`, `F`). The algorithm's choices (which optimal `x*`, which
maximizer `a*`, and every choice inside R-S) are left free: the relation holds for every output
of every run. -/
def IsAlg2Run {N : ℕ} (R : Fin N → ℕ → ℝ) (K : ℕ) (π : PPP N) : Prop :=
  ∃ xstar : Fin N → ℝ, IsOpt3 R K xstar ∧ Lemma2Prop R xstar ∧
    ∃ a : ℕ, 1 ≤ a ∧
      (∀ b : ℕ, 1 ≤ b →
        (b : ℝ) * K / (((b : ℝ) + 1) * ((K : ℝ) + b)) ≤
          (a : ℝ) * K / (((a : ℝ) + 1) * ((K : ℝ) + a))) ∧
      IsRSRun R K a (fun i => lift (R i) (xstar i)) π

end RecoveringBandits


