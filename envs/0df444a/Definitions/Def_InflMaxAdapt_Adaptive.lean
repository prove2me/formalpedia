-- Prove2me | Definitions.Def_InflMaxAdapt_Adaptive
-- name    : InflMaxAdapt_Adaptive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:36:10.260356+00:00
-- url     : https://prove2.me/theorems/8013e456-2d10-43d2-a296-5196f857efaf
-- title:
--   Best adaptive value $\mathrm{Adaptive}_k$
-- statement:
--   The value of the best **adaptive policy** with budget $k$ is
--   $$
--   \mathrm{Adaptive}_k(V, \mathbf p) \;=\; \max_{\pi \in \Pi_k} \mathbb E[\sigma(\pi)],
--   $$
--   where $\Pi_k$ is the set of adaptive policies with budget $k$ and full-adoption feedback, over any source of external randomness.
--
--   **Formalization Note** $\Pi_k$ ranges over all probability spaces $(\Omega, \mu)$ and all policies on them with measurable decision rules, and the maximum is the supremum of their values. The set of values is nonempty when $V$ is nonempty (constant policies) and bounded by $|V|$. For an empty vertex set and $k \ge 1$ no seed sequence exists and the value is $0$, the influence of the empty seed set.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 1.1, printed p.2 (PDF p.3)

import Mathlib
import Definitions.Def_InflMaxAdapt_arcValue
import Definitions.Def_InflMaxAdapt_Policy_IsMeasurable

open MeasureTheory

namespace InflMaxAdapt

/-- The value of the best adaptive policy (Section 1.1, printed p.2 = PDF p.3, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)):
`Adaptive_k(V, p) = max_{π ∈ Π_k} E[σ(π)]`, over all adaptive policies with budget `k` and
full-adoption feedback.

**Formalization Note** `Π_k` ranges over every probability space `(Ω, μ)` with `Ω : Type` carrying
the external randomness and every policy on it with measurable decision rules; the paper's `max` is
the supremum `sSup` of their values. The value set is nonempty when `V` is nonempty (constant
policies) and bounded by `|V|`; for empty `V` and `k ≥ 1` no seed sequence exists and the value is
`0`, the influence of the empty seed set. -/
noncomputable def Adaptive {V : Type} [Fintype V] [DecidableEq V] (p : V → V → ℝ) (k : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
    (π : Policy V k Ω), π.IsMeasurable ∧ r = arcValue p μ π}

end InflMaxAdapt


