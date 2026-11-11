-- Prove2me | Definitions.Def_AdaptiveDynMIS_Main_BernoulliSample
-- name    : AdaptiveDynMIS_Main_BernoulliSample
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:54:54.148881+00:00
-- url     : https://prove2.me/theorems/0acf1d00-541b-445e-bb77-8ea6f4dc5cf1
-- title:
--   Algorithm 1, BernoulliSample: output-sensitive independent sampling of an indexed set by geometric skipping
-- statement:
--   An **indexed set** is a set $S$ with an arbitrary order, supporting $\mathrm{size}(S)$ and $\mathrm{select}(S,i)$, the $i$-th element ($1\le i\le \mathrm{size}(S)$). For $p\in(0,1]$, $\mathrm{Geo}(p)$ is a geometric random variable counting the failures before the next success:
--   $$\Pr[\mathrm{Geo}(p)=k]=(1-p)^k p,\qquad k=0,1,2,\dots$$
--
--   **Algorithm 1** ($\mathrm{BernoulliSample}(S,p)$): set $T\leftarrow\emptyset$, $i\leftarrow 0$; while $i<\mathrm{size}(S)$, draw $g\leftarrow\mathrm{Geo}(p)$, set $i\leftarrow i+g+1$, and if $i\le\mathrm{size}(S)$ add $\mathrm{select}(S,i)$ to $T$; return $T$.
--
--   Here the algorithm reads its geometric values from a sequence $g_0,g_1,\dots$ (the $j$-th draw uses $g_{j}$), and the run returns the set $T$, the number of geometric draws and the number of $\mathrm{select}$ calls. Under `geoSeqMeasure p` the values $g_j$ are independent with law $\mathrm{Geo}(p)$.
--
--   This procedure is the paper's sampling primitive: its cost depends on the number of selected elements, not on $|S|$.
--
--   **Formalization Note.** An indexed set is a duplicate-free list in its current order, with $\mathrm{select}(S,i)$ the entry at position $i-1$. The loop is run with $|S|+1$ iterations of fuel, which is never exhausted because $i$ grows by at least one per iteration. $\mathrm{Geo}(p)$ is Mathlib's `geometricMeasure`, with the real parameter clamped to $[0,1]$ (the identity for $p\in(0,1]$).
-- source:
--   Chen, Fan, Zhang, Faster Dynamic Maximal Independent Set against Adaptive Adversaries, arXiv:2611.05932 (PDF sha256 a65b11d9…ec4a), p. 20, §3, Algorithm 1

import Mathlib

namespace AdaptiveDynMIS.Main

open MeasureTheory ProbabilityTheory

/-! # Algorithm 1, BernoulliSample, on a sequence of geometric values

Chen, Fan, Zhang, *Faster Dynamic Maximal Independent Set against Adaptive Adversaries*,
arXiv:2611.05932 (PDF sha256 a65b11d9…ec4a), §3 "Output-sensitive independent sampling" and
Algorithm 1, p. 20 (PDF 22).

**Formalization Note.** An indexed set is a duplicate-free list `S` in its current order;
`size(S)` is `S.length` and `select(S, i)` is the `i`-th entry `S[i-1]` (1-based). `Geo(p)` is a
primitive: the algorithm reads its successive geometric values from a sequence `g : ℕ → ℕ`
(`g j` is the value of the `(j+1)`-st draw), and these values are i.i.d. `Geo(p)` under
`geoSeqMeasure p`. The run returns the selected set `T`, the number of geometric draws and the
number of `select` calls. -/

/-- The loop of Algorithm 1 from position `i`, with the next geometric value `g j`, and `fuel` bounding
the number of iterations. It returns `(T, draws, selects)`: the elements selected from here on, the
index of the next unused geometric value, and the number of `select` calls made from here on. Each
iteration: while `i < size(S)`, draw `g ← Geo(p)`, set `i ← i + g + 1`, and if `i ≤ size(S)`, add
`select(S, i)` to `T`. -/
def sampleLoop {α : Type*} [DecidableEq α] (S : List α) (g : ℕ → ℕ) :
    ℕ → ℕ → ℕ → Finset α × ℕ × ℕ
  | 0, _, j => (∅, j, 0)
  | fuel + 1, i, j =>
      if i < S.length then
        if h : i + g j + 1 ≤ S.length then
          let r := sampleLoop S g fuel (i + g j + 1) (j + 1)
          (insert (S[i + g j]'(by omega)) r.1, r.2.1, r.2.2 + 1)
        else sampleLoop S g fuel (i + g j + 1) (j + 1)
      else (∅, j, 0)

/-- `BernoulliSample(S, p)` (Algorithm 1) run on the geometric values `g`, starting with `T = ∅`,
`i = 0`: the returned set `T`, the number of geometric draws and the number of `select` calls. The
position grows by at least one per iteration, so `size(S) + 1` iterations of fuel are never
exhausted. -/
def bernoulliSample {α : Type*} [DecidableEq α] (S : List α) (g : ℕ → ℕ) : Finset α × ℕ × ℕ :=
  sampleLoop S g (S.length + 1) 0 0

/-- A real parameter clamped to the unit interval (the identity on `[0, 1]`). -/
noncomputable def toUnit (p : ℝ) : unitInterval :=
  Set.projIcc 0 1 zero_le_one p

/-- The law of the geometric values: i.i.d. `Geo(p)`, `Pr[g j = k] = (1 - p)^k p` for `p ∈ (0, 1]`
(Mathlib's `geometricMeasure`). -/
noncomputable def geoSeqMeasure (p : ℝ) : Measure (ℕ → ℕ) :=
  Measure.infinitePi fun _ : ℕ => geometricMeasure (toUnit p)

end AdaptiveDynMIS.Main


