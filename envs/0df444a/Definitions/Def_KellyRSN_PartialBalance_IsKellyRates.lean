-- Prove2me | Definitions.Def_KellyRSN_PartialBalance_IsKellyRates
-- name    : KellyRSN_PartialBalance_IsKellyRates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:36:50.168446+00:00
-- url     : https://prove2.me/theorems/1f5a33cb-c14e-469a-a737-52b05e0b57d5
-- title:
--   Standing assumptions on a Markov process (§1.1)
-- statement:
--   Let $\mathcal S$ be a countable state space and $q(j,k) \in [0,\infty]$, $j,k \in \mathcal S$, transition rates. The rates satisfy the **standing assumptions** of the book if
--
--   1. $q(j,j) = 0$ for every $j$;
--   2. $q(j) = \sum_{k} q(j,k) < \infty$ for every $j$ (the process remains in each state for a positive length of time);
--   3. the process is irreducible: every state $k$ can be reached from every state $j$ through a chain $j = i_0, i_1, \dots, i_m = k$ with $q(i_{r-1}, i_r) > 0$;
--   4. the process is non-explosive.
--
--   The book assumes these properties for every continuous-time Markov process it considers; time homogeneity is built into the description by time-independent rates. Every theorem of this mission takes them as a hypothesis.
--
--   **Formalization Note** The Markov process is represented by its rate matrix. No finiteness of $\mathcal S$, bound on the rates or reversibility is assumed.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, pp. 1-3 (PDF pp. 4-6), §1.1 (countable state space; time homogeneous, irreducible, positive holding times, non-explosive; q(j,j) = 0)

import Mathlib
import Definitions.Def_KellyRSN_PartialBalance_IsNonExplosive

open scoped ENNReal

namespace KellyRSN.PartialBalance

/-- **The standing assumptions of the book on a continuous-time Markov process.**
Kelly, *Reversibility and Stochastic Networks*, Wiley 1979, §1.1, pp. 1–3 (PDF pp. 4–6):
"Let `X(t)` be a stochastic process taking values in a countable state space `𝒮`" (p. 1);
"throughout this work we shall assume that any continuous time Markov process with which we deal
is not only time homogeneous and irreducible but also remains in each state for a positive length
of time and is incapable of passing through an infinite number of states in a finite time. Define
the transition rate from state `j` to state `k` to be `q(j, k) = lim_{τ→0} P(X(t+τ) = k | X(t) = j)/τ`,
`j ≠ k`. It will be convenient to let `q(j, j) = 0`." (pp. 2–3).

`IsKellyRates q` is the conjunction of
1. `q(j, j) = 0` for every `j`;
2. `q(j) = Σ_k q(j, k) < ∞` for every `j` (the process remains in `j` for an exponential time of
   parameter `q(j)`, which is positive iff `q(j) < ∞`);
3. irreducibility: every state `k` can be reached from every state `j` through a chain of positive
   rates;
4. non-explosion (`IsNonExplosive`).

**Formalization Note.** A Markov process is represented by its transition-rate matrix
`q : S → S → ℝ≥0∞` on a countable state type `S` with the discrete σ-algebra; time homogeneity is
built in (the rates do not depend on time). No finiteness of `S`, bound on the rates or
reversibility is assumed. -/
def IsKellyRates {S : Type*} [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (q : S → S → ℝ≥0∞) : Prop :=
  (∀ j, q j j = 0) ∧ (∀ j, ∑' k, q j k ≠ ⊤) ∧
    (∀ j k, Relation.ReflTransGen (fun a b => 0 < q a b) j k) ∧ IsNonExplosive q

end KellyRSN.PartialBalance


