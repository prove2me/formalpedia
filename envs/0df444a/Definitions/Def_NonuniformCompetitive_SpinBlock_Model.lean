-- Prove2me | Definitions.Def_NonuniformCompetitive_SpinBlock_Model
-- name    : NonuniformCompetitive_SpinBlock_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:50:31.694649+00:00
-- url     : https://prove2.me/theorems/c53f7731-8058-433b-9230-03835578c747
-- title:
--   The spin-block problem: cost of a lock wait, deterministic on-line algorithms, off-line optimum
-- statement:
--   This file sets up the **spin-block problem** of Karlin, Manasse, McGeoch and Owicki (§4.1). A process waits for a lock on a multiprocessor system. At every moment it may keep **spinning**, at cost $1$ per unit of time, or **block**, paying a one-time context-switch cost $C$. The lock is released at a time $\tau \ge 0$ that the on-line algorithm does not know in advance.
--
--   1. **Cost of one wait.** If the process decides to spin until time $b \in [0,\infty]$ and then block ($b=\infty$ meaning "never block"), and the lock is released at time $\tau$, the cost is
--   $$\mathrm{waitCost}_C(b,\tau)=\begin{cases}\tau, & \tau\le b,\\ b+C, & b<\tau.\end{cases}$$
--   On a tie $b=\tau$ the lock is released and the process pays $\tau$.
--
--   2. **Inputs and deterministic on-line algorithms.** An input is a finite sequence $\sigma=(\tau_0,\dots,\tau_{n-1})$ of lock waits, each given by its release time. A deterministic on-line algorithm is a rule $h\mapsto b(h)$ assigning to the list $h$ of release times of the waits already processed the blocking time used for the next wait. Its total cost on $\sigma$ is
--   $$C_A(\sigma)=\sum_{j=0}^{n-1}\mathrm{waitCost}_C\big(b(\tau_0,\dots,\tau_{j-1}),\,\tau_j\big).$$
--
--   3. **Off-line optimum.** Knowing every release time, the optimal off-line algorithm spins if $\tau\le C$ and blocks at once otherwise, so
--   $$C_{opt}(\sigma)=\sum_{j=0}^{n-1}\min(\tau_j, C).$$
--
--   These objects are the model in which Theorem 10 of the paper (the optimal randomized competitive ratio $e/(e-1)$) is stated.
--
--   **Formalization Note** Blocking times take values in $[0,\infty]$ (`ℝ≥0∞`) and release times in $[0,\infty)$ (`ℝ≥0`); the cost of a wait is valued in `ℝ≥0∞` but is always finite. The on-line algorithm may use the release times of earlier waits, which it learns when those waits end; this is the information the paper's adaptive algorithms use (p. 561) and only enlarges the class of algorithms. The off-line cost is a real number.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), p. 558, §4.1 (the problem); p. 560, §4.1 displays for E C_A(σ_τ) and C_opt(σ_τ)

import Mathlib

open scoped NNReal ENNReal

namespace NonuniformCompetitive.SpinBlock

/-- The cost of **one lock wait** in the spin-block problem (Karlin–Manasse–McGeoch–Owicki,
Algorithmica 11 (1994), §4.1, pp. 558 and 560). The process spins until time `b` and then blocks,
paying the context-switch cost `C`; the lock is released at time `τ`. If the lock is released no
later than the blocking time (`τ ≤ b`, ties included) the process has spun for time `τ` and pays `τ`;
otherwise it spun for time `b` and then blocked, paying `b + C`. The value `b = ⊤` means "spin until
the lock is released". -/
noncomputable def waitCost (C : ℝ) (b : ℝ≥0∞) (τ : ℝ≥0) : ℝ≥0∞ :=
  if (τ : ℝ≥0∞) ≤ b then (τ : ℝ≥0∞) else b + ENNReal.ofReal C

/-- A **deterministic on-line algorithm** for the spin-block problem: before each lock wait it
chooses how long to spin before blocking (`⊤` = never block), as a function of the release times
of the previous lock waits only. The input is a finite sequence of lock waits, each given by the
time its lock is released. -/
structure OnlineAlg where
  /-- `blockTime h` is the blocking time chosen for the next wait, given the release times `h`
  of the waits already processed (in order). -/
  blockTime : List ℝ≥0 → ℝ≥0∞

/-- The total cost of the deterministic on-line algorithm `A` on the sequence `σ` of lock waits
(release times): the `j`-th wait is handled with the blocking time `A.blockTime (σ.take j)`. -/
noncomputable def OnlineAlg.cost (C : ℝ) (A : OnlineAlg) (σ : List ℝ≥0) : ℝ≥0∞ :=
  ∑ j : Fin σ.length, waitCost C (A.blockTime (σ.take j)) σ[j]

/-- The cost of the optimal off-line algorithm on the sequence `σ` of lock waits: knowing each
release time `τ` in advance, it spins (cost `τ`) if `τ ≤ C` and blocks immediately (cost `C`)
otherwise, i.e. it pays `min τ C` per wait (§4.1, p. 560, display for `C_opt(σ_τ)`). -/
noncomputable def optCost (C : ℝ) (σ : List ℝ≥0) : ℝ :=
  (σ.map fun τ : ℝ≥0 => min (τ : ℝ) C).sum

end NonuniformCompetitive.SpinBlock


