-- Prove2me | Definitions.Def_MartingaleHT_InfiniteServer_Toolkit
-- name    : MartingaleHT_InfiniteServer_Toolkit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:43.789983+00:00
-- url     : https://prove2.me/theorems/21a1d251-a2f6-474f-9a0d-a201e217692c
-- title:
--   Martingales, predictable quadratic variation, unit-jump counting paths, the integral representation (63), and stochastic boundedness in ℝ and Dᵏ
-- statement:
--   This module collects the general notions used by Pang, Talreja and Whitt (2007).
--
--   1. **Martingale with respect to a filtration.** For a nondecreasing family $(\mathcal G_t)_{t\ge0}$ of sub-$\sigma$-algebras, $X$ is a martingale if each $X(t)$ is $\mathcal G_t$-measurable and integrable and $E[X(t)\mid\mathcal G_s]=X(s)$ a.s. for $s\le t$.
--   2. **Predictable quadratic variation** (pp. 208–209). $V$ is the predictable quadratic variation $\langle M\rangle$ of the square-integrable martingale $M$ if $E[M(t)^2]<\infty$ for all $t$, $V$ is adapted with continuous, nondecreasing, nonnegative paths and $E[V(t)]<\infty$, and $M^2-V$ is a martingale.
--   3. **Unit-jump counting path** (§3.3). A path $x$ with $x(0)=0$, values in $\mathbb N$, nondecreasing and right-continuous, all of whose jumps have size $1$.
--   4. **Integral representation** (63). $x$ solves $x(t)=b+y(t)+\int_0^th(x(s))\,ds$, $t\ge0$, in $D$ if $x$ is right-continuous with left limits and the equation holds for every $t\ge0$.
--   5. **Stochastic boundedness in $\mathbb R$** (Definition 5.3). Real random variables $Y_n$, $n\ge1$, are stochastically bounded if for every $\varepsilon>0$ there is a constant $c$ with
--   $$
--   P(|Y_n|>c)\le\varepsilon\qquad\text{for all } n\ge1 .
--   $$
--   6. **Stochastic boundedness in $D^k$** (Definition 5.4). Processes $X_n$ with values in $\mathbb R^k$ are stochastically bounded in $D^k$ if, for every $T>0$, the random variables $\|X_n\|_T=\sup_{0\le t\le T}|X_n(t)|$ are stochastically bounded in $\mathbb R$.
--
--   These notions carry the martingale route to the fluid limit (Lemmas 5.5, 5.8, 5.9) and the continuous-mapping argument (Theorem 4.1).
--
--   **Formalization Note** The paper takes "predictable" to mean left-continuous paths (p. 208); for the processes in $D$ used here this is continuity, which is what item 2 requires; Mathlib has no Doob–Meyer theorem, so $\langle M\rangle$ is a property, not an operator. Stochastic boundedness in $\mathbb R$ is tightness on $\mathbb R$ written with the constant chosen after $\varepsilon$ and before $n$. The norm on $\mathbb R^k$ is $\ell^1$ and $\|X_n\|_T$ is computed in $[0,\infty]$, so a path with infinite supremum exceeds every bound; all norms on $\mathbb R^k$ give the same notion.
-- source:
--   Pang, Talreja & Whitt, Martingale Proofs of Many-Server Heavy-Traffic Limits for Markovian Queues, arXiv:0712.4211v1 (reprint of Probab. Surveys 4 (2007) 193–267), pp. 208–209, §3.2 (PQV); p. 210, §3.3 (counting processes); p. 225, (63); p. 235, Definitions 5.3–5.4 and Definition 5.1 (p. 233)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MartingaleHT.InfiniteServer

open BellWilliams2001.ThresholdPolicy

/-!
Pang, Talreja & Whitt (2007), §3.1–3.2 (pp. 206–210), §4.1 (p. 225) and §5.2 (p. 235):
martingales with respect to a family of σ-algebras, predictable quadratic variation, unit-jump
counting processes, the integral representation (63), and stochastic boundedness.

Conventions. Martingale time is `ℝ≥0`; path time is `ℝ` with conditions for `t ≥ 0` only.
Sequences are indexed by `n ≥ 1`; the value at `n = 0` is never used.
-/

/-- `X` is a **martingale with respect to the filtration `𝓖`** on `(Ω, P)`: `𝓖` is a
nondecreasing family of sub-σ-algebras of the ambient σ-algebra, each `X(t)` is
`𝓖(t)`-measurable and integrable, and `E[X(t) | 𝓖(s)] = X(s)` almost surely for `s ≤ t`. -/
def IsMartingaleWrt {Ω : Type*} [mΩ : MeasurableSpace Ω] (𝓖 : ℝ≥0 → MeasurableSpace Ω)
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  Monotone 𝓖 ∧ (∀ t, 𝓖 t ≤ mΩ) ∧ (∀ t, StronglyMeasurable[𝓖 t] (X t)) ∧
  (∀ t, Integrable (X t) P) ∧ ∀ s t : ℝ≥0, s ≤ t → P[X t | 𝓖 s] =ᵐ[P] X s

/-- `V` is the **predictable quadratic variation** of the **square-integrable martingale** `M`
with respect to `𝓖` (pp. 208–209): `M` is a `𝓖`-martingale with `E[M(t)²] < ∞` for all `t`;
`V` is adapted to `𝓖`, has continuous (the paper's "predictable", p. 208, for processes in `D`),
nondecreasing, nonnegative paths and `E[V(t)] < ∞`; and `M² − V` is a `𝓖`-martingale. -/
def IsPQV {Ω : Type*} [MeasurableSpace Ω] (𝓖 : ℝ≥0 → MeasurableSpace Ω) (P : Measure Ω)
    (M V : ℝ≥0 → Ω → ℝ) : Prop :=
  IsMartingaleWrt 𝓖 P M ∧ (∀ t, MemLp (M t) 2 P) ∧
  (∀ t, StronglyMeasurable[𝓖 t] (V t)) ∧ (∀ ω, Continuous (fun t => V t ω)) ∧
  (∀ ω, Monotone (fun t => V t ω)) ∧ (∀ t ω, 0 ≤ V t ω) ∧ (∀ t, Integrable (V t) P) ∧
  IsMartingaleWrt 𝓖 P (fun t ω => M t ω ^ 2 - V t ω)

/-- The path `x` is a **non-explosive unit-jump counting path** (§3.3, p. 210): it starts at
`0`, takes values in `ℕ` (so it is finite at every finite time), is nondecreasing and
right-continuous, and every jump has size at most `1` (on a left neighbourhood of each `t > 0`
the path is within `1` of its value at `t`). A counting process is unit-jump and non-explosive
when almost every path is such a path. -/
def IsUnitJumpCountingPath (x : ℝ≥0 → ℝ) : Prop :=
  x 0 = 0 ∧ (∀ t, ∃ m : ℕ, x t = m) ∧ Monotone x ∧
    (∀ t, ContinuousWithinAt x (Set.Ici t) t) ∧
    ∀ t, 0 < t → ∀ᶠ s in 𝓝[<] t, x t - x s ≤ 1

/-- `x` is a **solution in `D` of the integral representation** (63) (p. 225),
`x(t) = b + y(t) + ∫₀ᵗ h(x(s)) ds` for `t ≥ 0`: `x` is right-continuous with left limits on
`[0, ∞)` and the equation holds at every `t ≥ 0`. -/
def SolvesIntegralRep (h : ℝ → ℝ) (b : ℝ) (y x : ℝ → ℝ) : Prop :=
  IsCadlag x ∧ ∀ t : ℝ, 0 ≤ t → x t = b + y t + ∫ s in (0 : ℝ)..t, h (x s)

/-- **Stochastic boundedness in `ℝ`** (Definition 5.3, p. 235, with Definition 5.1): the real
random variables `Y n`, `n ≥ 1`, are tight, i.e. for every `ε > 0` there is a constant `c` with
`P(|Yₙ| > c) ≤ ε` for every `n ≥ 1`. The constant is chosen after `ε` and before `n`. -/
def IsSBReal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : ℕ → Ω → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → P {ω | c < |Y n ω|} ≤ ENNReal.ofReal ε

/-- **Stochastic boundedness in `Dᵏ`** (Definition 5.4, p. 235): for every `T > 0` the
real random variables `‖Xₙ‖_T = sup_{0 ≤ t ≤ T} |Xₙ(t)|`, `n ≥ 1`, are stochastically bounded in
`ℝ`. The norm on `ℝᵏ` is `ℓ¹` and the supremum is taken in `[0, ∞]` (`supDist (Xₙ ω) 0 T`), so a
path with infinite supremum counts as exceeding every bound. -/
def IsSBD {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ}
    (X : ℕ → Ω → ℝ → Fin k → ℝ) : Prop :=
  ∀ T : ℝ, 0 < T → ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n →
    P {ω | ENNReal.ofReal c < supDist (X n ω) 0 T} ≤ ENNReal.ofReal ε

end MartingaleHT.InfiniteServer


