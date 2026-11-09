-- Prove2me | Definitions.Def_InflMaxAdapt_edgeAdaptive
-- name    : InflMaxAdapt_edgeAdaptive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:36:58.929411+00:00
-- url     : https://prove2.me/theorems/0f4cfb0b-e58a-4e4a-b63a-92460ec8a898
-- title:
--   $\mathrm{Adaptive}_k$ in the undirected-edge representation
-- statement:
--   The best adaptive value in the undirected-edge representation, $\mathrm{Adaptive}_k = \max_{\pi \in \Pi_k} \mathbb E[\sigma(\pi)]$, over all adaptive policies with budget $k$ and full-adoption feedback.
--
--   **Formalization Note** As for the arc model: a supremum over all probability spaces of external randomness and all policies with measurable decision rules.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 2, printed p.5 (PDF p.6), and footnote 3

import Mathlib
import Definitions.Def_InflMaxAdapt_edgeValue
import Definitions.Def_InflMaxAdapt_Policy_IsMeasurable

open MeasureTheory

namespace InflMaxAdapt

/-- `Adaptive_k` in the undirected-edge representation (Sections 1.1 and 2, footnote 3, printed
pp.2, 5 = PDF pp.3, 6, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)): the supremum of `edgeValue` over every probability space
`(Ω, μ)` with `Ω : Type` and every policy on it with measurable decision rules. -/
noncomputable def edgeAdaptive {V : Type} [Fintype V] [DecidableEq V] (q : Sym2 V → ℝ) (k : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
    (π : Policy V k Ω), π.IsMeasurable ∧ r = edgeValue q μ π}

end InflMaxAdapt


