-- Prove2me | Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
-- name    : BellWilliams2001_ThresholdPolicy_Paths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T06:37:05.531417+00:00
-- url     : https://prove2.me/theorems/ce24ede6-67ae-4339-9f8a-cf776363ec89
-- title:
--   Skorokhod paths, renewal counting, the uniform norm on [0,t], u.o.c. convergence in probability, and coupling-form weak convergence
-- statement:
--   This module fixes the path-space notation of Bell and Williams (Section 1.1) used by every statement of the mission. Time is real, and every path is only evaluated at times $t\ge 0$.
--
--   1. **Skorokhod paths.** A function $x:[0,\infty)\to\mathbb R$ belongs to $\mathbf D$ if it is right continuous on $[0,\infty)$ and has finite left limits on $(0,\infty)$.
--   2. **Partial sums.** For a sequence $x(1),x(2),\dots$, $X(0)=0$ and $X(n)=\sum_{i=1}^n x(i)$; the paper's index base $i\ge1$ is kept.
--   3. **Counting process.** For partial sums $X$ and $t\in\mathbb R$,
--   $$N(t)=\sup\{n\ge 0: X(n)\le t\}\in\mathbb N\cup\{\infty\},$$
--   the renewal process of (3), (5) and (179); it takes the value $\infty$ when infinitely many partial sums are at most $t$.
--   4. **Uniform norm.** For $\mathbb R^m$-valued paths, $\|f-g\|_t=\sup_{0\le s\le t}|f(s)-g(s)|$ with $|x|=\sum_i|x_i|$, as in (1), taken in $[0,\infty]$.
--   5. **u.o.c. convergence in probability.** Processes $Z^n$ on $(\Omega,\mathcal F,\mathbf P)$ converge to a deterministic path $z$ if $\mathbf P(\|Z^n-z\|_t\ge\varepsilon)\to0$ for every $\varepsilon>0$ and $t\ge0$ (p. 613).
--   6. **Coupling form of weak convergence.** $Z^n\Rightarrow Z$ is encoded as: on some probability space there are processes $Y^n$, $Y$ with Skorokhod paths, $Y^n$ having the law of $Z^n$ for all large $n$ and $Y$ the law of $Z$ (laws of the paths on $[0,\infty)$ under the product $\sigma$-algebra, which is the Borel $\sigma$-algebra of $\mathbf D^m$, p. 612), with $\|Y^n-Y\|_t\to0$ almost surely for every $t\ge0$.
--
--   These objects are the vocabulary of Theorems 5.2, 7.1, 7.2, Lemmas 8.1 and 9.3 and Proposition B.1.
--
--   **Formalization Note** Item 6 is equivalent to weak convergence in $\mathbf D^m$ with the $J_1$ topology when the limit has continuous paths: the Skorokhod representation theorem gives one direction, and almost sure u.o.c. convergence implies almost sure $J_1$ convergence, hence weak convergence, in the other. Suprema are taken in $[0,\infty]$ and the counting process in $\mathbb N\cup\{\infty\}$, so no junk value arises on unbounded inputs.
-- source:
--   Bell and Williams, Dynamic scheduling of a system with two parallel servers in heavy traffic with resource pooling, Ann. Appl. Probab. 11 (2001), pp. 612–613, Section 1.1, (1); p. 613, (2)–(3); p. 614, (5); p. 644, (178)–(179)

import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal

namespace BellWilliams2001.ThresholdPolicy

/-!
Bell and Williams (2001), Section 1.1 (p. 612–613) and Section 2.1 (p. 613–614): path-space
notation shared by every statement of the mission. Time is real; every path is only ever
evaluated at times `t ≥ 0`, and every condition below quantifies over `t ≥ 0` only.
-/

/-- A path `x : [0,∞) → ℝ` is a **Skorokhod path** (a member of `D`, p. 612): it is right
continuous on `[0,∞)` and has finite left limits on `(0,∞)`. Values at negative times are
ignored. -/
def IsCadlag (x : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt x (Set.Ici t) t) ∧
  (∀ t : ℝ, 0 < t → ∃ l : ℝ, Tendsto x (𝓝[<] t) (𝓝 l))

/-- Partial sums with the paper's index base: `partialSum x n = ∑_{i=1}^{n} x i`, so
`partialSum x 0 = 0` ((2), (4), p. 613; (178), p. 644). The value `x 0` is never used. -/
def partialSum (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, x i

/-- The counting process of a sequence of partial sums,
`N(t) = sup{n ≥ 0 : X(n) ≤ t}` ((3), (5), p. 613–614; (179), p. 644), computed in `ℕ∞`:
it equals `⊤` when infinitely many partial sums are `≤ t`, never a junk value. -/
noncomputable def renewalCount (X : ℕ → ℝ) (t : ℝ) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : X n ≤ t), (n : ℕ∞)

/-- `‖f − g‖_t = sup_{s ∈ [0,t]} |f(s) − g(s)|` ((1), p. 612) for `ℝ^m`-valued paths, with the
paper's norm `|x| = ∑ᵢ |xᵢ|`. The supremum is taken in `[0,∞]`, so it is never a junk value. -/
noncomputable def supDist {m : ℕ} (f g : ℝ → Fin m → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ (s : ℝ) (_ : s ∈ Set.Icc 0 t), ENNReal.ofReal (∑ i, |f s i - g s i|)

/-- **Uniform convergence on compact time intervals in probability** (p. 613): processes
`Z n` defined on `(Ω, P)` converge u.o.c. in probability to the deterministic path `z` if
`P(‖Z n − z‖_t ≥ ε) → 0` as `n → ∞` for every `ε > 0` and every `t ≥ 0`. -/
def UocInProb {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {m : ℕ}
    (Z : ℕ → Ω → ℝ → Fin m → ℝ) (z : ℝ → Fin m → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => P {ω | ENNReal.ofReal ε ≤ supDist (Z n ω) z t}) atTop (𝓝 0)

/-- **Convergence in distribution to a process with continuous paths, in coupling form.**
Processes `Z n` on `(Ω, P)` and `Zlim` on `(Ω', P')`, all `ℝ^m`-valued with time `t ≥ 0`, are
related by: there are a probability space `(Ω'', P'')` and processes `Y n`, `Ylim` on it such that
`Y n` has the law of `Z n` for all large `n` and `Ylim` has the law of `Zlim` (laws of the paths restricted to
`[0,∞)`, on the product σ-algebra, which is the Borel σ-algebra of `D^m`, p. 612), every path of
every `Y n` is a Skorokhod path, and almost surely `Y n → Ylim` uniformly on compact time
intervals. When `Zlim` has continuous paths and the `Z n` have Skorokhod paths this is equivalent
to `Z n ⟹ Zlim` in `D^m` with the `J₁` topology (Skorokhod representation in one direction; a.s.
u.o.c. convergence implies a.s. `J₁` convergence, hence weak convergence, in the other). Only the laws of the `Z n` for large `n` matter, as for weak convergence. -/
def CouplingConverges {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') {m : ℕ}
    (Z : ℕ → Ω → ℝ → Fin m → ℝ) (Zlim : Ω' → ℝ → Fin m → ℝ) : Prop :=
  ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (P'' : Measure Ω'')
    (Y : ℕ → Ω'' → ℝ → Fin m → ℝ) (Ylim : Ω'' → ℝ → Fin m → ℝ),
    IsProbabilityMeasure P'' ∧
    (∀ᶠ n in atTop, ProbabilityTheory.IdentDistrib (fun ω (t : NNReal) => Y n ω t)
      (fun ω (t : NNReal) => Z n ω t) P'' P) ∧
    ProbabilityTheory.IdentDistrib (fun ω (t : NNReal) => Ylim ω t)
      (fun ω (t : NNReal) => Zlim ω t) P'' P' ∧
    (∀ n ω (i : Fin m), IsCadlag (fun t => Y n ω t i)) ∧
    ∀ᵐ ω ∂P'', ∀ t : ℝ, 0 ≤ t → Tendsto (fun n => supDist (Y n ω) (Ylim ω) t) atTop (𝓝 0)

end BellWilliams2001.ThresholdPolicy


