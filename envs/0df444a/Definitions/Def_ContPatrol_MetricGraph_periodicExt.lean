-- Prove2me | Definitions.Def_ContPatrol_MetricGraph_periodicExt
-- name    : ContPatrol_MetricGraph_periodicExt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:12:55.639153+00:00
-- url     : https://prove2.me/theorems/af5ce802-f932-4058-bc70-7e925a339114
-- title:
--   Definition 4: randomized periodic extension; $k$ separated visits
-- statement:
--   Let $S:[0,L]\to Q$ be a **closed unit speed path**: $L>0$, $S(0)=S(L)$ and $d(S(t),S(t'))\le|t-t'|$ on $[0,L]$.
--
--   1. For $\Delta\in[0,L]$, the periodic patrol $S_\Delta(t)=S((t+\Delta)\bmod L)$, $t\ge0$, starts at $S(\Delta)$ and has period $L$.
--   2. The **randomized periodic extension** $\tilde S$ of $S$ is the mixture of the patrols $S_\Delta$ with $\Delta$ uniform on $[0,L]$.
--   3. $S$ **visits every point $k$ times separated by at least $\alpha$ (mod $L$)** if $\alpha\le L$ and every point $x$ satisfies $S(t_i)=x$ for some $t_1,\dots,t_k\in[0,L)$ with
--   $$t_j-t_i\ge\alpha\quad\text{and}\quad L-(t_j-t_i)\ge\alpha\qquad(i<j).$$
--
--   These are the objects of Theorem 2, the paper's general lower bound $V\ge k\alpha/L$.
--
--   **Formalization Note** Separation is read cyclically: the gap from the last visit of one period to the first visit of the next counts too; for $k=1$ that gap is $L$, hence $\alpha\le L$.
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, Definition 4, p.8; Theorem 2, p.9

import Mathlib
import Definitions.Def_ContPatrol_MetricGraph_dist

namespace ContPatrol

namespace MetricGraph

open MeasureTheory

variable {V E : Type}

/-- **Closed unit speed paths.** Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*,
arXiv:2008.07369v2, §3, p.5 ("we shall call a path satisfying the 1–Lipschitz condition (1) a unit
speed path") and Definition 4, p.8 ("S : [0, L] → Q is a closed unit speed path").

`G.IsClosedUnitSpeedPath S L`: `L > 0`, `S 0 = S L`, and `S` is 1-Lipschitz on `[0, L]`.

**Formalization Note.** `S` is a function on all of `ℝ`; only its values on `[0, L]` matter. -/
def IsClosedUnitSpeedPath (G : MetricGraph V E) (S : ℝ → G.Point) (L : ℝ) : Prop :=
  0 < L ∧ S 0 = S L ∧
    ∀ t ∈ Set.Icc (0 : ℝ) L, ∀ t' ∈ Set.Icc (0 : ℝ) L, G.dist (S t) (S t') ≤ |t - t'|

/-- **Randomized periodic extension (Definition 4), the pure patrols S_Δ.**
Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, Definition 4,
p.8: "If S : [0, L] → Q is a closed unit speed path, we can extend it to various patrols
S∆ : [0, ∞) → Q of period L by the definition S∆(t) = S((t + ∆) mod L), for all t ≥ 0."

`periodicExt S L Δ t = S((t + Δ) mod L)`, with `x mod L = L · fract(x / L) ∈ [0, L)` for `L > 0`.

**Formalization Note.** Defined for all real `t`; patrols are only constrained for `t ≥ 0`. -/
noncomputable def periodicExt {G : MetricGraph V E} (S : ℝ → G.Point) (L : ℝ) (Δ t : ℝ) : G.Point :=
  S (L * Int.fract ((t + Δ) / L))

/-- **The randomization of Definition 4**: "∆ chosen uniformly in the interval (or circle)
[0, L]" (p.8). The law of `Δ` is Lebesgue measure on `[0, L]` divided by `L`. Together with
`periodicExt S L` (indexed by `Δ`) it is the randomized periodic extension `S̃` of `S`. -/
noncomputable def shiftLaw (L : ℝ) : Measure ℝ :=
  (ENNReal.ofReal L)⁻¹ • (volume : Measure ℝ).restrict (Set.Icc 0 L)

/-- **k separated visits to every point (hypothesis of Theorem 2).**
Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, Theorem 2,
p.9: "S : [0, L] → Q is a closed unit speed tour that visits every point of Q at k times which
are separated by at least α (mod L)."

`G.VisitsSeparated S L α k`: `α ≤ L`, and every point `x` is visited at `k` times
`t_1, …, t_k ∈ [0, L)` any two of which are at least `α` apart around the circle of length `L`
(for `i < j`: `t_j − t_i ≥ α` and `L − (t_j − t_i) ≥ α`).

**Formalization Note.** "Separated by at least α (mod L)" is read cyclically: the gap from the
last visit to the first visit of the next period counts too. For `k = 1` that gap is `L`, hence
the clause `α ≤ L` (for `k ≥ 2` it follows from the others). The non-cyclic reading would make
Theorem 2(i) false (a circle of length `L = 1` with `α = 2` and `k = 1` would give a guarantee
`kα/L = 2 > 1`). -/
def VisitsSeparated (G : MetricGraph V E) (S : ℝ → G.Point) (L α : ℝ) (k : ℕ) : Prop :=
  α ≤ L ∧ ∀ x : G.Point, ∃ ts : Fin k → ℝ, (∀ i, ts i ∈ Set.Ico 0 L ∧ S (ts i) = x) ∧
    ∀ i j, i < j → α ≤ ts j - ts i ∧ α ≤ L - (ts j - ts i)

end MetricGraph

end ContPatrol


