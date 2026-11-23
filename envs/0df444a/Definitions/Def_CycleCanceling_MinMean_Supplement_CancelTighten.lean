-- Prove2me | Definitions.Def_CycleCanceling_MinMean_Supplement_CancelTighten
-- name    : CycleCanceling_MinMean_Supplement_CancelTighten
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:20:35.867188+00:00
-- url     : https://prove2.me/theorems/b2096c6c-0ea9-428a-b624-81b8f4517d90
-- title:
--   Admissible cancellation prefixes and complete cancel-and-tighten phases
-- statement:
--   Fix a finite circulation network $N$. At fixed vertex prices $p$, one admissible step chooses any residual simple cycle all of whose reduced costs are negative and cancels it by exactly its current residual bottleneck, using the published antisymmetric flow update. An admissible run is any finite prefix $H_0,\ldots,H_K$ starting at a circulation. Its definition imposes no length bound or completion condition.
--
--   One complete outer phase begins at a nonoptimal circulation, completes an admissible run at the old prices until the admissible graph is acyclic, and changes only the prices to satisfy
--
--   $$\varepsilon(g,p')\le(1-1/n)\varepsilon(g,p),\qquad n=|V|,$$
--
--   where $g$ is the circulation immediately after Step 1. An outer run is any finite prefix of complete phases, with arbitrary starting circulation and identically zero initial prices. These predicates specify the domain of both clauses of Theorem 4.1.
--
--   **Formalization Note** All admissible cycles and all tightening prices are allowed. Intermediate flows are existential witnesses to actual cancellations. No minimum-mean rule, convergence estimate, final optimality certificate or iteration cap is part of a run predicate. States beyond a prefix's endpoint are irrelevant.
-- source:
--   Goldberg, Tarjan, Finding Minimum-Cost Circulations by Canceling Negative Cycles, J. ACM 36(4), 1989, https://doi.org/10.1145/76359.76368, p. 876, Section 2, cancellation; pp. 880–881, Section 4, Steps 1–2

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_Algorithm
import Definitions.Def_CycleCanceling_MinMean_Supplement_Admissible
import Definitions.Def_CycleCanceling_MinMean_Supplement_PairError

namespace CycleCanceling.MinMean.Supplement

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One arbitrary admissible cancellation, by precisely the current residual bottleneck. -/
def IsAdmissibleStep (N : CircNetwork V) (p : V → ℝ)
    (f g : V → V → ℝ) : Prop :=
  ∃ Γ : List V, IsAdmissibleCycle N f p Γ ∧ g = cancel N f Γ

/-- A finite prefix of Step 1 at fixed prices. There is no length cap or endpoint condition. -/
def IsAdmissibleRun (N : CircNetwork V) (p : V → ℝ)
    (F : ℕ → V → V → ℝ) (K : ℕ) : Prop :=
  IsCirculation N (F 0) ∧ ∀ i < K, IsAdmissibleStep N p (F i) (F (i + 1))

/-- One complete outer phase, pp. 880–881. Step 1 ends acyclic at unchanged prices;
Step 2 changes only prices and reduces the error measured immediately before that update.
A phase starts only if its starting circulation is nonoptimal. -/
def IsCancelTightenPhase (N : CircNetwork V) (f : V → V → ℝ) (p : V → ℝ)
    (g : V → V → ℝ) (p' : V → ℝ) : Prop :=
  ¬ IsMinCost N f ∧
  ∃ (K : ℕ) (H : ℕ → V → V → ℝ),
    H 0 = f ∧ IsAdmissibleRun N p H K ∧ H K = g ∧
    IsAdmissibleAcyclic N g p ∧
    pairError N g p' ≤ (1 - 1 / (Fintype.card V : ℝ)) * pairError N g p

/-- All finite prefixes of the cancel-and-tighten algorithm. Initially any circulation
and zero prices; each counted phase completes both steps. No terminal optimality,
iteration bound, convergence rate or cycle selection rule is assumed. -/
def IsCancelTightenRun (N : CircNetwork V) (F : ℕ → V → V → ℝ)
    (P : ℕ → V → ℝ) (T : ℕ) : Prop :=
  IsCirculation N (F 0) ∧ P 0 = (fun _ => 0) ∧
  ∀ t < T, IsCancelTightenPhase N (F t) (P t) (F (t + 1)) (P (t + 1))

end CycleCanceling.MinMean.Supplement


