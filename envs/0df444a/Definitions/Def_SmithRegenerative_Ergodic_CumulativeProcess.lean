-- Prove2me | Definitions.Def_SmithRegenerative_Ergodic_CumulativeProcess
-- name    : SmithRegenerative_Ergodic_CumulativeProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:13.759023+00:00
-- url     : https://prove2.me/theorems/cc88ed18-705d-4e8c-989e-c181140c59df
-- title:
--   Cumulative process (§5·1): conditions (C1), (C2), cycle increments y_n, the variation process w̃_t and ỹ_n
-- statement:
--   This file defines Smith's **cumulative processes** (§5·1, pp. 22–23) relative to a sequence $t_0, t_1, \dots$ of cycle lengths with epochs $T_k = t_0 + \dots + t_k$.
--
--   Let $w = (w_t)_{t \in \mathbb R}$ be a real-valued process on $(\Omega, \mathcal F, P)$.
--
--   1. **Cycle increments.** $y_n = w_{T_n} - w_{T_{n-1}}$ for $n = 1, 2, \dots$: the increment of $w$ over the $n$-th cycle.
--   2. **Variation process.** On a path that is of bounded variation on every interval $[0,s]$, $s \ge 0$,
--   $$\tilde w_t = \int_0^t |\mathrm dw_t|,$$
--   the total variation of $r \mapsto w_r$ over $[0,t]$ (equation (5·1·1)); on every other path $\tilde w_t = 0$ for all $t$, as the paper prescribes.
--   3. **Cycle variations.** $\tilde y_n = \tilde w_{T_n} - \tilde w_{T_{n-1}}$, the variation of $w$ over the $n$-th cycle. One has $|y_n| \le \tilde y_n$ on bounded-variation paths.
--   4. **Cumulative process.** $w$ is a cumulative process when
--      - (C1) $y_1, y_2, \dots$ are independent and identically distributed;
--      - (C2) almost surely, $w$ is of bounded variation on every finite interval $[0,s]$;
--      - and in addition $\tilde y_1, \tilde y_2, \dots$ are identically distributed.
--
--   With $\kappa_r = E y_1^r$ and $\tilde\kappa_r = E\tilde y_1^r$, a typical example is the total reward earned up to time $t$ in a system that regenerates at the epochs $T_k$; Theorem 7 says that $w_t / t \to \kappa_1/\mu_1$ almost surely.
--
--   **Formalization Note** (C1) is read literally: only the increments $y_n$ are required to be i.i.d.; no independence between the cycle lengths and the increments is assumed. The identical distribution of the $\tilde y_n$ is an explicit extra condition: the paper's notation $\tilde\kappa_r$ presupposes it, and the paper asserts that $\tilde w$ satisfies (C1) whenever $w$ does. The total variation is Mathlib's `eVariationOn` converted to a real number. Measurability of the individual $w_t$ is not required.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, pp. 22–23, §5·1, conditions (C1), (C2), (5·1·1)

import Mathlib
import Definitions.Def_SmithRegenerative_Ergodic_Renewal

open MeasureTheory ProbabilityTheory

namespace SmithRegenerative.Ergodic

/-- Cycle increments `y_n ≡ Δ_n w_t ≡ w_{T_n} − w_{T_{n−1}}` (§5·1, p. 23), for `n = 1, 2, …`.

Formalization Note: only `n ≥ 1` is meaningful; at `n = 0` natural-number subtraction gives
`w_{T_0} − w_{T_0} = 0`. -/
def cycleIncrement {Ω : Type*} (t : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  w (SmithRegenerative.Equilibrium.epoch t n ω) ω - w (SmithRegenerative.Equilibrium.epoch t (n - 1) ω) ω

/-- A sample path of `w` is of bounded variation in every finite interval `[0, s]`, `s ≥ 0`
(the event in condition (C2), §5·1, p. 23). -/
def HasBVPaths {Ω : Type*} (w : ℝ → Ω → ℝ) (ω : Ω) : Prop :=
  ∀ s : ℝ, 0 ≤ s → BoundedVariationOn (fun r => w r ω) (Set.Icc 0 s)

open Classical in
/-- The variation process `w̃_t = ∫₀^t |dw_t|` (5·1·1), p. 23: the total variation of the path
`r ↦ w_r` over `[0, t]`, "on the set of zero probability for which this definition breaks down
we may take w̃_t = 0 for all t".

Formalization Note: on a path of bounded variation on every `[0, s]` this is
`eVariationOn (w · ω) [0, t]` (finite, converted to `ℝ`); on every other path it is `0` for all
`t`, exactly as the paper prescribes. For `t < 0` the interval is empty and the value is `0`. -/
noncomputable def variation {Ω : Type*} (w : ℝ → Ω → ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  if HasBVPaths w ω then (eVariationOn (fun r => w r ω) (Set.Icc 0 s)).toReal else 0

/-- Cycle variations `ỹ_n = w̃_{T_n} − w̃_{T_{n−1}}` (§5·1, p. 23, "the obvious quantities"),
`n = 1, 2, …`: the variation of `w` over the `n`-th cycle `[T_{n−1}, T_n]`. As for
`cycleIncrement`, only `n ≥ 1` is meaningful. -/
noncomputable def cycleVariation {Ω : Type*} (t : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  variation w (SmithRegenerative.Equilibrium.epoch t n ω) ω - variation w (SmithRegenerative.Equilibrium.epoch t (n - 1) ω) ω

/-- **Cumulative process** (§5·1, pp. 22–23): "A real-valued process w_t is defined to be a
cumulative process if it satisfies the following two conditions: (C1) {w_{T_n} − w_{T_{n−1}}},
for n = 1, 2, …, is a sequence of independent, identically distributed, random variables.
(C2) w_t is, with probability one, of bounded variation in every finite t-interval."

Formalization Note: (C1) is read literally: the cycle increments `y_n` (`n ≥ 1`) are mutually
independent and identically distributed. In addition the cycle variations `ỹ_n` (`n ≥ 1`) are
assumed identically distributed (`variation_identDistrib`): the paper's notation
`κ̃_r = E ỹ_n^r` presupposes it, and the page asserts more ("It is clear that w̃_t satisfies (C1)
and (C2) if w_t does so", p. 23). No independence between the cycle lengths `t_i` and the `y_n`
is assumed. (C2) is required on `[0, s]` for every `s ≥ 0` (every finite interval in the
time domain `t ≥ 0`), almost surely. Measurability of the individual `w_t` is not required. -/
structure IsCumulativeProcess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (t : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) : Prop where
  C1_indep : iIndepFun (fun n : ℕ => cycleIncrement t w (n + 1)) P
  C1_identDistrib : ∀ n, IdentDistrib (cycleIncrement t w (n + 1)) (cycleIncrement t w 1) P P
  C2 : ∀ᵐ ω ∂P, HasBVPaths w ω
  variation_identDistrib :
    ∀ n, IdentDistrib (cycleVariation t w (n + 1)) (cycleVariation t w 1) P P

end SmithRegenerative.Ergodic


