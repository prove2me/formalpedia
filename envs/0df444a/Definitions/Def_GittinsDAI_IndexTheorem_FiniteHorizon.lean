-- Prove2me | Definitions.Def_GittinsDAI_IndexTheorem_FiniteHorizon
-- name    : GittinsDAI_IndexTheorem_FiniteHorizon
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:26:26.67477+00:00
-- url     : https://prove2.me/theorems/33f2d3e1-6369-4200-bb37-3012bee137ad
-- title:
--   Eq. (5) — the $M$-horizon index $\nu^M(D,x)=\sup_{0<\tau\le M}\nu_\tau(D,x)$ and the stopping rule of Corollary 1
-- statement:
--   Let $D$ be a single bandit process: a Markov chain $x(0), x(1), \dots$ on a measurable state space $\Theta$ with transition kernel $P$, started at $x(0)=x$, which earns the reward $a^t R(x(t))$ at process time $t$, with discount factor $0<a<1$. For a stopping time $\tau$ of the chain write
--   $$R_\tau(D,x) = E\Big\{\sum_{t=0}^{\tau-1} a^t R(x(t)) \,\Big|\, x(0)=x\Big\},\qquad W_\tau(D,x) = E\Big\{\sum_{t=0}^{\tau-1} a^t \,\Big|\, x(0)=x\Big\},\qquad \nu_\tau(D,x)=\frac{R_\tau(D,x)}{W_\tau(D,x)}.$$
--
--   This file defines two objects of Section 4 of Gittins (1979).
--
--   1. **The $M$-horizon index** (Eq. (5), p. 155). For a non-random positive integer $M$,
--   $$\nu^M(D,x) = \sup_{0<\tau\le M} \nu_\tau(D,x),$$
--   the supremum over the stopping times $\tau$ with $1\le\tau\le M$. The set contains $\tau\equiv 1$, so it is nonempty for $M\ge 1$; under the paper's standing integrability assumption its elements are bounded above.
--
--   2. **The stopping rule of Corollary 1** (p. 155). For a positive integer $M$ and the initial state $x$, the time-dependent stopping sets are
--   $$\Theta_0(t) = \{y\in\Theta : \nu^{M-t}(D,y) < \nu^M(D,x)\},\qquad t = 1,2,\dots,M-1,$$
--   and the rule stops at the first $t\in\{1,\dots,M-1\}$ with $x(t)\in\Theta_0(t)$, and at time $M$ if there is none.
--
--   These are the objects of Corollary 1 of Section 4, which the paper uses for the calculation algorithm of its Section 7.
--
--   **Formalization Note** The chain, its stopping times ($\mathbb{N}\cup\{\infty\}$-valued, adapted to the coordinate filtration, time indexed from $0$) and $\nu_\tau$ are the published objects `markovChainMeasure`, `IsPositiveStoppingTime` and `stoppedRatio`. The paper's $\{0<\tau\le M\}$ is the set of stopping times $\tau$ with "the stopping set $\Theta_0$ allowed to depend on the process time $t$" and $\tau\le M$; the Lean takes the supremum over all positive stopping times bounded by $M$, which contains the time-dependent stopping-set rules, and Corollary 1 asserts that one of those attains it. The supremum is a real `sSup`; for $M=0$, a value the paper never uses, it is $\sup\emptyset = 0$ by Lean's convention.
-- source:
--   Gittins, Bandit Processes and Dynamic Allocation Indices, J. R. Statist. Soc. B 41 (1979), p. 155, Section 4, Eq. (5) and Corollary 1

import Mathlib
import Definitions.Def_GittinsIndex
import Definitions.Def_AllocationIndices_Index
open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices

namespace GittinsDAI.IndexTheorem

/-- Gittins (1979), Eq. (5), p. 155: the `M`-horizon dynamic allocation index
`ν^M(D, x) = sup_{0 < τ ≤ M} ν_τ(D, x)`, the supremum of the reward-per-unit-of-discounted-time
ratios `ν_τ(D, x) = R_τ(D, x) / W_τ(D, x)` over the positive stopping times of the single bandit
process (chain law `markovChainMeasure P x`, time indexed from `0`) that are bounded by the
non-random integer `M`. For `M ≥ 1` the set is nonempty (it contains `τ ≡ 1`); for `M = 0` it is
empty and the value is the junk `sSup ∅ = 0`, a case the paper never uses (it takes `M` a positive
integer). -/
noncomputable def finiteHorizonIndex {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] (r : S → ℝ) (α : ℝ) (M : ℕ) (x : S) : ℝ :=
  sSup {g : ℝ | ∃ τ : (ℕ → S) → ℕ∞, IsPositiveStoppingTime τ ∧ (∀ ω, τ ω ≤ (M : ℕ∞)) ∧
    g = stoppedRatio P r α τ x}

/-- The stopping rule of Gittins (1979), Corollary 1, p. 155, for the process started in state
`x`: stop at the first process time `t ∈ {1, 2, …, M − 1}` at which the state `ω t` lies in the
time-dependent stopping set `Θ₀(t) = {y : ν^{M−t}(D, y) < ν^M(D, x)}`, and at time `M` if there
is no such `t`. -/
noncomputable def corollaryStoppingTime {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] (r : S → ℝ) (α : ℝ) (M : ℕ) (x : S) (ω : ℕ → S) : ℕ∞ :=
  min (M : ℕ∞) (⨅ t : {t : ℕ // 1 ≤ t ∧ t < M ∧
      finiteHorizonIndex P r α (M - t) (ω t) < finiteHorizonIndex P r α M x}, ((t : ℕ) : ℕ∞))

end GittinsDAI.IndexTheorem


