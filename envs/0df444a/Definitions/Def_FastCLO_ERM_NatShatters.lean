-- Prove2me | Definitions.Def_FastCLO_ERM_NatShatters
-- name    : FastCLO_ERM_NatShatters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T04:17:22.937887+00:00
-- url     : https://prove2.me/theorems/170576f5-877d-461a-ae8f-c8036716194e
-- title:
--   Natarajan shattering of k points by a class of functions (Definition 2)
-- statement:
--   Let $H$ be a class of functions from a set $\mathcal X$ to a set $\mathcal Y$, and let $k \ge 0$. The class **Natarajan-shatters** $k$ points if there are points $x_1, \dots, x_k \in \mathcal X$ and labels $s_i \ne s'_i$ in $\mathcal Y$ for each $i$ such that, for every $b \in \{0, 1\}^k$, some $\pi \in H$ satisfies
--
--   $$\pi(x_i) = \begin{cases} s_i & \text{if } b_i = 1,\\ s'_i & \text{if } b_i = 0,\end{cases} \qquad i = 1, \dots, k.$$
--
--   The **Natarajan dimension** of $H$ is the largest $k$ for which this happens. "Natarajan dimension at most $\eta$" means that $H$ does not shatter $\eta + 1$ points; "at least $\eta$" means that it shatters $\eta$ points. Shattering is hereditary, so these readings agree with the definition by the largest integer.
--
--   The Natarajan dimension is the multiclass analogue of the VC dimension; the paper uses it for policy classes $\Pi \subseteq [\mathbb R^p \to \mathcal Z^\angle]$.
--
--   **Formalization Note** The dimension itself is not introduced as a supremum of natural numbers, which would take the value $0$ for a class that shatters arbitrarily many points; statements use the shattering predicate directly.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, Definition 2, p. 6

import Mathlib

namespace FastCLO.ERM

/-- Natarajan shattering (arXiv:2011.03030v3, Definition 2, p. 6): a class `H` of functions
`X → Y` shatters `k` points if there are points `x_1, …, x_k` and two labelings `s, s'` with
`s_i ≠ s'_i` for every `i`, such that for every `b ∈ {0,1}^k` some `π ∈ H` takes the value `s_i`
at `x_i` when `b_i = 1` and `s'_i` when `b_i = 0`.

"`H` has Natarajan dimension at most `η`" is `¬ NatShatters H (η + 1)`, and "at least `η`" is
`NatShatters H η`; shattering is hereditary, so these match "the largest integer `η` for which …".

Formalization Note: the dimension is not defined as an `sSup` in `ℕ`, which would be `0` for a class
shattering arbitrarily large sets. The definition is generic in the domain and codomain; the paper
uses it for `X = ℝ^p` and `Y = ℝ^d`. -/
def NatShatters {X Y : Type*} (H : Set (X → Y)) (k : ℕ) : Prop :=
  ∃ (x : Fin k → X) (s s' : Fin k → Y), (∀ i, s i ≠ s' i) ∧
    ∀ b : Fin k → Bool, ∃ π ∈ H, ∀ i, π (x i) = if b i then s i else s' i

end FastCLO.ERM


