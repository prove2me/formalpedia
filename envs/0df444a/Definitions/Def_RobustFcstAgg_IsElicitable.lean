-- Prove2me | Definitions.Def_RobustFcstAgg_IsElicitable
-- name    : RobustFcstAgg_IsElicitable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:48:59.748811+00:00
-- url     : https://prove2.me/theorems/35237811-d9a7-4ac5-bb97-335dc0852340
-- title:
--   Elicitability of a query against a set of variables (Definition 2)
-- statement:
--   A query $Q$ of expert $i$ is **elicitable** with respect to a set $\mathcal R$ of real-valued random variables if there is a payment function $\pi(r,\mathcal R)$ such that truthful answering is the unique maximizer of the expert's conditional expected payment:
--   $$Q(S_i,\mathcal D)=\arg\max_{r\in\mathbb R}\mathbb E_{\mathcal D}[\pi(r,\mathcal R)\mid S_i].$$
--
--   This is the incentive constraint on the queries; without it a single query per signal would reveal everything at order one.
--
--   **Formalization Note** One payment $\pi$ works for every instance $\mathcal D$, since the principal does not know $\mathcal D$ (p.4). Conditional expectation is the integral over the hidden signals. For almost every $s$, every report has an integrable payment and every report other than the answer has a strictly smaller expected payment.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Definition 2, p.5

import Mathlib
import Definitions.Def_RobustFcstAgg_Signals
import Definitions.Def_RobustFcstAgg_glue
import Definitions.Def_RobustFcstAgg_InfoStruct_agentLaw
import Definitions.Def_RobustFcstAgg_InfoStruct_restLaw
import Definitions.Def_RobustFcstAgg_Query
open MeasureTheory

namespace RobustFcstAgg

/-- **Elicitability against a set of variables.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Definition 2, p.5: "there exists a payment function
`π(r, R)` such that the query uniquely maximizes their payment conditional on available information:
`Q(S_i, D) = arg max_r E_D[π(r, R) | S_i]`".

**Formalization Note.** One `π`, chosen before `D` ("we do not assume that the principal has any knowledge of
`D`", p.4). `E_D[· | S_i = s]` is the integral over the signals hidden from `i`, by independence. The clause
carries integrability for every report `r`, so a non-integrable payment does not count as `0`. The answer is the
unique maximizer for a.e. `s`. `R D v` is the variable scored at vertex `v` under `D`. -/
def IsElicitable {n : ℕ} (q : Query n) {N : Type} (R : InfoStruct n → N → Signals n → ℝ) : Prop :=
  ∃ π : ℝ → (N → ℝ) → ℝ, ∀ D : InfoStruct n, ∀ᵐ s ∂D.agentLaw q.agent,
    (∀ r, Integrable (fun y => π r fun v => R D v (glue q.agent s y)) (D.restLaw q.agent)) ∧
    ∀ r, r ≠ q.eval D s →
      ∫ y, π r (fun v => R D v (glue q.agent s y)) ∂D.restLaw q.agent <
        ∫ y, π (q.eval D s) (fun v => R D v (glue q.agent s y)) ∂D.restLaw q.agent

end RobustFcstAgg


