-- Prove2me | Definitions.Def_GreedyReusableNet_IsApproxOracle
-- name    : GreedyReusableNet_IsApproxOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:35:33.898926+00:00
-- url     : https://prove2.me/theorems/3b745f65-fb59-44a9-b3f6-1a7b39b0fc85
-- title:
--   Assumption 4 ($(\alpha,\beta)$-Oracle)
-- statement:
--   **Assumption 4.** For every period $t<T$, every weight function $f\ge0$, every counting vector $n$ and every set of available arms: with probability at least $\beta$ over a uniform seed, the oracle returns an available action set $\mathcal A\in\mathscr A_t$ with
--   $$\sum_{B\in\mathcal A}f(B)\,\mathbb P_t(B\mid\mathcal A,n(B))\ \ge\ \alpha\sum_{B\in\mathcal A'}f(B)\,\mathbb P_t(B\mid\mathcal A',n(B))$$
--   for every available action set $\mathcal A'\in\mathscr A_t$.
--
--   **Formalization Note** The maximization is over the available action sets, as in the oracle calls of Algorithms 2–4. An oracle for the problem over all of $\mathscr A_t$ gives one: set $f$ to $0$ on bundles containing an unavailable arm and delete those bundles from the output, which keeps it in $\mathscr A_t$ (Assumption 1) and does not lower the objective (Assumption 2).
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §2.1, Assumption 4, p.11; Algorithms 2–4, pp.16–17

import Mathlib
import Definitions.Def_GreedyReusableNet_ProblemInstance
import Definitions.Def_GreedyReusableNet_prob
import Definitions.Def_GreedyReusableNet_History
import Definitions.Def_GreedyReusableNet_tapeLaw
import Definitions.Def_GreedyReusableNet_Oracle

open MeasureTheory

namespace GreedyReusableNet

/-- The per-period objective `∑_{B ∈ A} f(B) ℙ_t(B | A, n(B))` (Simchi-Levi, Zheng & Zhu,
SSRN 3981123, eq. (3) and Assumption 4, p.11). -/
noncomputable def objValue {N : ℕ} (d : PeriodData N) (f : Finset (Fin N) → ℝ) (n : Fin N → ℕ)
    (A : Finset (Finset (Fin N))) : ℝ :=
  ∑ B ∈ A, f B * prob d B A n

/-- **Assumption 4 ((α,β)-Oracle)** (Simchi-Levi, Zheng & Zhu, SSRN 3981123, p.11): "for any time
period `t ∈ [T]`, any reward function `f_t(B) ≥ 0`, and any counting vector `n_t ≥ 0`, we can
solve `max_{𝒜_t ∈ 𝒜_t} ∑_{B ∈ 𝒜_t} f_t(B) ℙ_t(B|𝒜_t, n_t(B))` up to an `α` approximation ratio with
probability at least `β`."

For every period `t < T`, every nonnegative weight function `f`, every counting vector `n` and
every set `free` of available arms: with probability at least `β` over the seed, the oracle
returns an available action set of `𝒜_t` whose objective is at least `α` times the objective of
every available action set of `𝒜_t`.

**Formalization Note** The maximization is over the *available* action sets, as in the oracle
calls of Algorithms 2–4 (p.16–17: "`max_{𝒜_t ∈ 𝒜_t, 𝒜_t available}`"). An oracle for the
unrestricted problem gives one: set `f` to `0` on bundles with an unavailable arm and delete those
bundles from its output, which keeps it in `𝒜_t` (Assumption 1) and does not lower the objective
(Assumption 2). On the failure event nothing is required of the output. -/
def IsApproxOracle {N : ℕ} (I : ProblemInstance N) (T : ℕ) (α β : ℝ) (O : Oracle N) : Prop :=
  ∀ t < T, ∀ f : Finset (Fin N) → ℝ, (∀ B, 0 ≤ f B) → ∀ (n : Fin N → ℕ) (free : Finset (Fin N)),
    ENNReal.ofReal β ≤
      unif {u : ℝ | IsAvailableSet (I.period t) free (O.sel (I.period t) f n free u) ∧
        ∀ A' : Finset (Finset (Fin N)), IsAvailableSet (I.period t) free A' →
          α * objValue (I.period t) f n A' ≤
            objValue (I.period t) f n (O.sel (I.period t) f n free u)}

end GreedyReusableNet


