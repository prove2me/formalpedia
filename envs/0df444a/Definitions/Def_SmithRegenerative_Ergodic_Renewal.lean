-- Prove2me | Definitions.Def_SmithRegenerative_Ergodic_Renewal
-- name    : SmithRegenerative_Ergodic_Renewal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:48.333745+00:00
-- url     : https://prove2.me/theorems/31ab2529-cbed-45a3-929e-4bf64cc76cdd
-- title:
--   Renewal process (§2·1): i.i.d. cycle lengths t_i, epochs T_k, the counting variable n_t and Z_t
-- statement:
--   This file sets up the renewal process of §2·1 of Smith (1955) and the quantities of §5 built from it.
--
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $t_0, t_1, t_2, \dots$ real random variables on it.
--
--   1. **Renewal process.** The cycle lengths $t_1, t_2, \dots$ form a *renewal process* when they are measurable, mutually independent, identically distributed and non-negative, and are "not zero with probability one", i.e. $P\{t_1 = 0\} < 1$. Strict positivity is not required. The delay $t_0$ is not constrained by this definition; every theorem of the mission assumes $t_0 = 0$ explicitly.
--   2. **Regeneration epochs.** $T_k = t_0 + t_1 + \dots + t_k$ for $k = 0, 1, 2, \dots$ (equation (2·1·3)).
--   3. **Counting variable.** For real $t$,
--   $$n_t = \#\{k \ge 0 : T_k \le t\},$$
--   which for non-negative cycle lengths is the paper's "greatest integer $k$ such that $T_{k-1} \le t$" (with $T_{-1} = 0$): the number of regenerations in $[0,t]$, counting the one at $T_0$.
--   4. **Forward variable.** $Z_t = \sum_{i=1}^{n_t+1} t_i - t$ (§5·2, p. 26). When $t_0 = 0$, $t + Z_t = T_{n_t+1}$ is a regeneration epoch after $t$.
--
--   These objects are shared by every statement of the mission: the renewal strong law is about $n_t$, and Lemma 8 and Theorem 7 compare the cumulative process at $t$ and at $t + Z_t$.
--
--   **Formalization Note** The sequence is indexed by $\mathbb N$, the paper's $t_i$ being `t i`. $n_t$ is a cardinality computed with `Set.ncard`; if infinitely many epochs are $\le t$ (an event of probability zero for a renewal process) it takes the value $0$. That value is a convention on a null event and is never excluded by a hypothesis.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 9, §2·1 (2·1·1), (2·1·3); p. 26, §5·2 (definition of Z_t)

import Mathlib
import Definitions.Def_SmithRegenerative_Equilibrium_EquilibriumProcess

open MeasureTheory ProbabilityTheory

namespace SmithRegenerative.Ergodic

/-- **Renewal process** (Smith, *Regenerative stochastic processes*, Proc. R. Soc. Lond. A
232(1188):6–31 (1955), §2·1, p. 9, unnumbered): "Let {t_i} (i = 1, 2, …) be an infinite sequence
of independent non-negative, identically distributed random variables, which are not zero with
probability one".

Formalization Note: `t : ℕ → Ω → ℝ` is the augmented sequence `t₀, t₁, t₂, …` of the paper; this
structure constrains only the cycle lengths `t 1, t 2, …` (the renewal process proper). The delay
`t 0` is left free here; every theorem of the mission assumes `t₀ = 0` explicitly, as the paper
does in §5. "Random variable" is a measurable real function; "independent" is mutual independence
of `(t (i+1))_{i ≥ 0}` (`iIndepFun`); "identically distributed" is `IdentDistrib (t (i+1)) (t 1)`;
non-negativity holds at every sample point; "not zero with probability one" is
`P {t₁ = 0} < 1`. Strict positivity of the `t_i` is not assumed. -/
structure IsRenewalProcess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (t : ℕ → Ω → ℝ) :
    Prop where
  measurable : ∀ i, Measurable (t (i + 1))
  indep : iIndepFun (fun i : ℕ => t (i + 1)) P
  identDistrib : ∀ i, IdentDistrib (t (i + 1)) (t 1) P P
  nonneg : ∀ i ω, 0 ≤ t (i + 1) ω
  not_ae_zero : P {ω | t 1 ω = 0} < 1

/-- The counting variable `n_t` (§2·1, p. 9): "the greatest integer k such that T_{k−1} ≤ t".
With `T_{−1} = 0` and non-decreasing epochs this is the number of indices `k ≥ 0` with `T_k ≤ t`,
i.e. the number of regenerations in `[0, t]` counting the one at `T_0`.

Formalization Note: `count t s ω = #{k ≥ 0 : T_k(ω) ≤ s}` via `Set.ncard`. If that set is
infinite (`T_k` bounded, an event of probability zero for a renewal process), `Set.ncard`
returns `0`; this value is a convention on a null event and is never assumed away. -/
noncomputable def count {Ω : Type*} (t : ℕ → Ω → ℝ) (s : ℝ) (ω : Ω) : ℕ :=
  {k : ℕ | SmithRegenerative.Equilibrium.epoch t k ω ≤ s}.ncard

/-- The forward variable `Z_t = Σ_{i=1}^{n_t+1} t_i − t` (§5·2, p. 26). -/
noncomputable def Z {Ω : Type*} (t : ℕ → Ω → ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.Icc 1 (count t s ω + 1), t i ω) - s

end SmithRegenerative.Ergodic


