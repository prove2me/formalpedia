-- Prove2me | Definitions.Def_FocusSetRB_IsAperiodicUnichain
-- name    : FocusSetRB_IsAperiodicUnichain
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:15:40.93902+00:00
-- url     : https://prove2.me/theorems/7ed71fdc-a88c-4f5a-82e7-ae3e835ccd7f
-- title:
--   Aperiodic unichain (Assumption 1)
-- statement:
--   A transition matrix $Q$ on the finite set $\mathbb S$ induces an **aperiodic unichain** if its Markov chain has a single recurrent class, possibly together with transient states, and that class is aperiodic. Precisely:
--
--   1. some state is recurrent, where $s$ is recurrent if every state reachable from $s$ can reach $s$ back, and $t$ is reachable from $s$ if $(Q^n)_{st}>0$ for some $n\ge0$;
--   2. any two recurrent states are reachable from each other;
--   3. every recurrent state $s$ has period $1$: the greatest common divisor of $\{n\ge1:(Q^n)_{ss}>0\}$ is $1$.
--
--   **Assumption 1** of the paper asks that some optimal solution $y^*$ of (LP) have a policy $\bar\pi^*$ whose matrix $P_{\bar\pi^*}$ is an aperiodic unichain. It replaces the global attractor and synchronization assumptions of earlier work.
--
--   **Formalization Note** Reachability and recurrence are the published definitions `Reaches` and `IsRecurrentState` of `YoungConventions_Perturbed_FiniteChain`. The period condition is imposed on recurrent states only, so transient states are unconstrained, as the paper's "possibly empty set of transient states" requires.
-- source:
--   Hong, Xie, Chen, Wang, Unichain and Aperiodicity are Sufficient for Asymptotic Optimality of Average-Reward Restless Bandits, arXiv:2402.05689v4, Assumption 1, p.7

import Mathlib
import Definitions.Def_YoungConventions_Perturbed_FiniteChain

namespace FocusSetRB

open YoungConventions.Perturbed

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The transition matrix `Q` induces an **aperiodic unichain** (arXiv:2402.05689v4,
Assumption 1, p.7): "a Markov chain with a single recurrent class and a possibly empty set of
transient states", which is aperiodic. Here: (i) some state is recurrent, (ii) any two recurrent
states reach each other (so the recurrent states form a single class), and (iii) every
recurrent state has period `1`: the only `d` dividing every `n ≥ 1` with `(Qⁿ)_{ss} > 0` is `1`.

**Formalization Note.** Reachability and recurrence are the published
`YoungConventions.Perturbed.Reaches` (`∃ n, (Qⁿ)_{xy} > 0`) and `IsRecurrentState` (every state
reachable from `s` reaches `s` back). Transient states are unconstrained: the period condition is
imposed on recurrent states only, as the source's "possibly empty set of transient states"
requires (periodicity is a class property, so this is aperiodicity of the recurrent class). -/
def IsAperiodicUnichain (Q : Matrix S S ℝ) : Prop :=
  (∃ s, IsRecurrentState Q s) ∧
  (∀ s t, IsRecurrentState Q s → IsRecurrentState Q t → Reaches Q s t) ∧
  (∀ s, IsRecurrentState Q s →
    ∀ d : ℕ, (∀ n : ℕ, 1 ≤ n → 0 < (Q ^ n) s s → d ∣ n) → d = 1)

end FocusSetRB


