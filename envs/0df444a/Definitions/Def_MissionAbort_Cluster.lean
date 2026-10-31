-- Prove2me | Definitions.Def_MissionAbort_Cluster
-- name    : MissionAbort_Cluster
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:49.959249+00:00
-- url     : https://prove2.me/theorems/526152bc-be70-45dc-b5be-9498a1ba531f
-- title:
--   The three health states
-- statement:
--   The system of the mission has three health states: **healthy**, **defective** and **failed**, the states $1$, $2$ and $3$ of the failure process $X(t)$. The same three labels name the clusters $\mathcal X_1,\mathcal X_2,\mathcal X_3$ of the surrogate chain.
--
--   This is the common target of the original failure process and of the surrogate chain, and the cost of the mission depends on the state only through this label.
--
--   **Formalization Note** The type carries the discrete $\sigma$-algebra.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §3.1, pp.8–9, and §4.1, p.13

import Mathlib

namespace MissionAbort

/-- The three health states of the system (Sun, Hu & Ye, arXiv:2505.03225v1, §3.1, pp.8–9):
`healthy` is the page's state 1, `defective` its state 2 and `failed` its state 3. The surrogate's
clusters `X₁, X₂, X₃` (p.13) use the same type.

**Formalization Note.** The σ-algebra is the discrete one; the type has three points. -/
inductive Cluster where
  | healthy
  | defective
  | failed
  deriving DecidableEq, Repr

instance : Fintype Cluster :=
  ⟨{.healthy, .defective, .failed}, fun x => by cases x <;> simp⟩

instance : MeasurableSpace Cluster := ⊤

instance : MeasurableSingletonClass Cluster := ⟨fun _ => trivial⟩

end MissionAbort


