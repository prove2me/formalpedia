-- Prove2me | Definitions.Def_CritContracts_Supplement_QueryAlg
-- name    : CritContracts_Supplement_QueryAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:55:57.224598+00:00
-- url     : https://prove2.me/theorems/3151dc96-cf03-4837-adf4-4f12be0d723b
-- title:
--   Randomized adaptive query algorithms with value and $\mathrm{NE}^\star$ oracles
-- statement:
--   Fix $m$. A **query algorithm** for two-agent instances with actions $\{0,\dots,m-1\}$ receives the owner of every action and the action costs; in each round, from the history of its queries and their answers, it draws its next step from a probability distribution: ask a **value query** $f(S)$, ask an **optimal equilibria query** $\mathrm{NE}^\star(\alpha)$, or halt and output a contract $\alpha$. The oracles answer with the real number $f(S)$ and with the entire set $\mathrm{NE}^\star(\alpha)$ (ties included) for $\alpha\in[0,1]^2$; a query at a vector outside $[0,1]^2$, which the paper does not allow, receives the empty set. Running the algorithm on an instance gives a distribution over pairs (output if it halted, number of queries asked); the **success probability** for a property of the output is the limit, as the number of rounds grows, of the probability of halting with an output having the property.
--
--   This is the algorithm class of the information-theoretic lower bound Theorem 4.11.
--
--   **Formalization Note** The algorithm is an arbitrary function: no running-time or computability restriction, real numbers allowed in queries and outputs, arbitrary adaptivity, and each step drawn from a countably supported distribution (which covers every coin-flipping algorithm).
-- source:
--   Ezra–Feldman–Molina–Schlesinger, Sources of Complexity in Multi-Agent Combinatorial Contracts, STOC 2027 submission (manuscript sha256 430be35c86352b23f05ee0e9126d1318096922c9cbe07d419ee38e38bfcba346), Definition 4.10 and Theorem 4.11, p.26 (PDF p.27); proof of Theorem 4.11, p.68 (PDF p.69)

import Mathlib
import Definitions.Def_CritContracts_Supplement_IsCritical

set_option autoImplicit false

namespace CritContracts.Supplement

/-- A query to the oracles of Theorem 4.11: a **value query** `f(S)` or an **optimal equilibria query** `NE★(α)`
(Ezra–Feldman–Molina–Schlesinger, *Sources of Complexity in Multi-Agent Combinatorial Contracts*, STOC 2027
submission (manuscript sha256 430be35c…), §2, p.10, PDF p.11; Definition 4.10, p.26, PDF p.27). -/
inductive Query (m : ℕ) where
  | value (S : Finset (Fin m))
  | nestar (α : Fin 2 → ℝ)

/-- An oracle answer: a reward value, or a set of action profiles. -/
inductive Answer (m : ℕ) where
  | value (v : ℝ)
  | nestar (A : Set (Finset (Fin m)))

/-- A step of a query algorithm: ask a query, or halt and output a contract. -/
inductive Step (m : ℕ) where
  | ask (q : Query m)
  | out (α : Fin 2 → ℝ)

/-- A **randomized adaptive query algorithm** for two-agent instances with `m` actions (Theorem 4.11, p.26, PDF
p.27): from the explicit data of the instance (the owner of each action and the action costs) and the history of
queries and answers so far, a probability distribution over its next step.

**Formalization Note** The lower bound of Theorem 4.11 is information-theoretic (p.26: "independent of
computational assumptions"), so the algorithm is an arbitrary function: no running-time or computability
restriction, real numbers allowed in queries and outputs, arbitrary adaptivity and randomness (each step drawn
from a countably supported distribution, which covers every algorithm that flips coins). -/
structure QueryAlg (m : ℕ) where
  /-- The distribution of the next step, given the owners, the costs and the history. -/
  next : (Fin m → Fin 2) → (Fin m → ℝ) → List (Query m × Answer m) → PMF (Step m)

/-- The oracles' answer on an instance `M`: `f(S)` for a value query; the entire set `NE★(α)` (ties included,
Definition 4.10) for an optimal equilibria query at a contract `α ∈ [0,1]²`. A query at a vector outside
`[0,1]²`, which the paper does not allow, gets the uninformative answer `∅`. -/
noncomputable def answer {m : ℕ} (M : Model (Fin 2) (Fin m)) : Query m → Answer m
  | .value S => .value (M.f S)
  | .nestar α => by classical exact if IsContract α then .nestar (NEstar M α) else .nestar ∅

/-- **Running a query algorithm** on the instance `M` for at most `t` further rounds from the history `h`: the
distribution of the pair (output, if it halted; number of queries asked). -/
noncomputable def queryRun {m : ℕ} (A : QueryAlg m) (M : Model (Fin 2) (Fin m)) :
    ℕ → List (Query m × Answer m) → PMF (Option (Fin 2 → ℝ) × ℕ)
  | 0, h => PMF.pure (none, h.length)
  | t + 1, h => (A.next M.owner M.c h).bind fun s =>
    match s with
    | .out α => PMF.pure (some α, h.length)
    | .ask q => queryRun A M t (h ++ [(q, answer M q)])

/-- The probability that `A`, run on `M`, eventually halts with an output contract satisfying `good`: the
supremum over `t` of the probability of doing so within `t` rounds. -/
noncomputable def successProb {m : ℕ} (A : QueryAlg m) (M : Model (Fin 2) (Fin m))
    (good : (Fin 2 → ℝ) → Prop) : ENNReal :=
  ⨆ t : ℕ, (queryRun A M t []).toOuterMeasure {r | ∃ α, r.1 = some α ∧ good α}

end CritContracts.Supplement


