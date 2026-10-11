-- Prove2me | Definitions.Def_KPZBallistic_Defs
-- name    : KPZBallistic_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T09:27:43.45509+00:00
-- url     : https://prove2.me/theorems/4d63d8b2-ff40-4065-a038-7fd9190fd107
-- title:
--   One-dimensional ballistic deposition and random deposition driven by Poisson clocks
-- statement:
--   Model layer for one-dimensional ballistic deposition and random deposition driven by Poisson clocks.
--
--   1. **Clocks.** On a probability space $(\Omega,P)$, the data $\tau_{x,k}$, $(x,k)\in\mathbb Z\times\mathbb N$, are the inter-arrival times of the clock of column $x$. The predicate `IsPoissonClocks P τ` says they are measurable, mutually independent, and each $\mathrm{Exp}(1)$-distributed. The $n$-th ring of column $x$ ($n=0,1,2,\dots$) is at time $T_{x,n}=\tau_{x,0}+\dots+\tau_{x,n}$ (`arrivalTime`).
--   2. **Random deposition.** `rdHeight τ t x` $=N_t(x)=\#\{n: T_{x,n}\le t\}$, the number of rings of the clock of $x$ in $[0,t]$.
--   3. **Ballistic deposition update.** `bdStep f x` replaces the height $f(x)$ by $\max\{f(x)+1,f(x-1),f(x+1)\}$ and leaves the other columns unchanged.
--   4. **Finite substrate.** `boxHeight τ L t` $=\xi^{Q_L}_t$ is the height profile obtained from the flat profile $0$ by applying `bdStep` at every ring $(T_{x,n},x)$ with $|x|\le L$ and $T_{x,n}\le t$, in increasing order of time (ties, a null event, broken by column). Columns outside $Q_L=[-L,L]$ stay at $0$.
--   5. **Infinite substrate.** `bdHeight τ t x` $=\xi_t(x)=\sup_{L}\xi^{Q_L}_t(x)\in\mathbb N\cup\{\infty\}$, the monotone limit of the finite-substrate heights. `bdNextHeight τ t x` $=\eta_t(x)=\max\{\xi_t(x)+1,\xi_t(x-1),\xi_t(x+1)\}$ is the next-arrival height, and `bdHeightReal τ t x` is $\xi_t(x)$ as a real number (with value $0$ where $\xi_t(x)=\infty$).
--
--   This is the nearest-neighbour lattice ballistic deposition model of Penrose (2008, Section 2) in dimension $d=1$, started from a flat surface, and the model (1) of Sudijono (2026) with $d=1$.
--
--   **Formalization Note** When the finite-box ring set is infinite (a null event) it is replaced by the empty set; `bdHeightReal` maps $\infty$ to $0$. Both conventions only affect null events.
-- source:
--   M. D. Penrose, Growth and roughness of the interface for ballistic deposition, J. Stat. Phys. 131 (2008), https://arxiv.org/abs/math/0608540, Section 2, pp. 3-4 (lattice ballistic deposition, NN model, d = 1); T. Sudijono, A Linear Variance Bound for Ballistic Deposition (2026), https://arxiv.org/abs/2609.24056, eq. (1); I. Corwin, The Kardar-Parisi-Zhang equation and universality class, Random Matrices Theory Appl. 1 (2012), https://arxiv.org/abs/1106.1596, Section 1.1.1, p. 3

import Mathlib

/-!
# Ballistic deposition and random deposition on `ℤ`

Model layer for the KPZ-universality mission on one-dimensional ballistic deposition.

Each column `x : ℤ` carries a rate-one Poisson clock, encoded by its i.i.d. `Exp(1)`
inter-arrival times `τ x k`.  The `n`-th ring (`n = 0, 1, 2, …`) of column `x` happens at time
`arrivalTime τ x n = τ x 0 + ⋯ + τ x n`.

* **Random deposition**: the height of column `x` at time `t` is the number of rings of the
  clock of `x` in `[0, t]`.
* **Ballistic deposition** (nearest-neighbour model, flat initial surface): when the clock of
  column `x` rings, the height of `x` is updated to
  `max (f x + 1) (max (f (x - 1)) (f (x + 1)))`.
  On the finite substrate `Q_L = [-L, L]` only the clocks in `Q_L` are used and columns
  outside `Q_L` stay at height `0`; the rings in `[0, t]` are processed in increasing time
  order.  The height on the infinite substrate `ℤ` is the (monotone) limit `L → ∞`, i.e. the
  supremum over `L`, taken in `ℕ∞`.
-/

open MeasureTheory ProbabilityTheory

namespace KPZBallistic

/-- Standing hypotheses on the clock data: the inter-arrival times `τ x k`, indexed by
`(x, k) ∈ ℤ × ℕ`, are measurable, mutually independent, and each has the exponential law of
rate `1`. -/
structure IsPoissonClocks {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (τ : ℤ → ℕ → Ω → ℝ) : Prop where
  measurable : ∀ x k, Measurable (τ x k)
  indep : iIndepFun (fun p : ℤ × ℕ => τ p.1 p.2) P
  law : ∀ x k, P.map (τ x k) = expMeasure 1

/-- Time of the `n`-th ring (counting from `n = 0`) of the clock of column `x`. -/
def arrivalTime {Ω : Type*} (τ : ℤ → ℕ → Ω → ℝ) (x : ℤ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), τ x k ω

/-- Random deposition height of column `x` at time `t`: the number of rings of the clock of
`x` during `[0, t]`. -/
noncomputable def rdHeight {Ω : Type*} (τ : ℤ → ℕ → Ω → ℝ) (t : ℝ) (x : ℤ) (ω : Ω) : ℕ :=
  {n : ℕ | arrivalTime τ x n ω ≤ t}.ncard

/-- One ballistic-deposition update at column `x`: the new height of `x` is
`max (f x + 1) (max (f (x - 1)) (f (x + 1)))`, all other heights are unchanged. -/
def bdStep (f : ℤ → ℕ) (x : ℤ) : ℤ → ℕ :=
  Function.update f x (max (f x + 1) (max (f (x - 1)) (f (x + 1))))

/-- The rings in the box `[-L, L]` during `[0, t]`, as (time, column) pairs ordered
lexicographically (so by time first). -/
noncomputable def boxEvents {Ω : Type*} (τ : ℤ → ℕ → Ω → ℝ) (L : ℕ) (t : ℝ) (ω : Ω) :
    Finset (ℝ ×ₗ ℤ) :=
  open Classical in
  let S : Set (ℝ ×ₗ ℤ) :=
    {e | |(ofLex e).2| ≤ (L : ℤ) ∧ (ofLex e).1 ≤ t ∧
      ∃ n : ℕ, arrivalTime τ (ofLex e).2 n ω = (ofLex e).1}
  if h : S.Finite then h.toFinset else ∅

/-- Ballistic deposition on the finite substrate `[-L, L]` with flat initial surface: start
from height `0` everywhere and apply `bdStep` at each ring of `[0, t]` in time order. -/
noncomputable def boxHeight {Ω : Type*} (τ : ℤ → ℕ → Ω → ℝ) (L : ℕ) (t : ℝ) (ω : Ω) :
    ℤ → ℕ :=
  open Classical in
  ((boxEvents τ L t ω).sort (· ≤ ·)).foldl (fun f e => bdStep f (ofLex e).2) (fun _ => 0)

/-- Ballistic deposition height (last-arrival height) of column `x` at time `t` on the
infinite substrate `ℤ`, flat initial surface: the limit of the finite-substrate heights as
`L → ∞`, which is their supremum. -/
noncomputable def bdHeight {Ω : Type*} (τ : ℤ → ℕ → Ω → ℝ) (t : ℝ) (x : ℤ) (ω : Ω) : ℕ∞ :=
  ⨆ L : ℕ, ((boxHeight τ L t ω x : ℕ) : ℕ∞)

/-- Next-arrival height of column `x` at time `t`: the height column `x` would jump to if its
clock rang at time `t`. -/
noncomputable def bdNextHeight {Ω : Type*} (τ : ℤ → ℕ → Ω → ℝ) (t : ℝ) (x : ℤ) (ω : Ω) :
    ℕ∞ :=
  max (bdHeight τ t x ω + 1) (max (bdHeight τ t (x - 1) ω) (bdHeight τ t (x + 1) ω))

/-- Real-valued ballistic deposition height (`0` on the null event where the height is
infinite). -/
noncomputable def bdHeightReal {Ω : Type*} (τ : ℤ → ℕ → Ω → ℝ) (t : ℝ) (x : ℤ) (ω : Ω) :
    ℝ :=
  ((bdHeight τ t x ω).toNat : ℝ)

end KPZBallistic


