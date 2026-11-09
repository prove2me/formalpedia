-- Prove2me | Definitions.Def_InflMaxAdapt_edgeValue
-- name    : InflMaxAdapt_edgeValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:15.479653+00:00
-- url     : https://prove2.me/theorems/1dbe98f8-d1b6-41e8-958f-a3e4b8907d94
-- title:
--   Expected influence of a policy in the undirected-edge representation
-- statement:
--   The expected influence $\mathbb E[\sigma(\pi)]$ of an adaptive policy $\pi$ when the live edges are drawn from independent bond percolation with edge probabilities $q$, the external randomness $\omega \sim \mu$ is independent of the live edges, and every seed is chosen with the full cascades of the earlier seeds as feedback.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 2, printed p.5 (PDF p.6), and footnote 3

import Mathlib
import Definitions.Def_InflMaxAdapt_edgeWeight
import Definitions.Def_InflMaxAdapt_edgeCascade
import Definitions.Def_InflMaxAdapt_Policy_seeds

open MeasureTheory

namespace InflMaxAdapt

/-- The expected influence `E[σ(π)]` of an adaptive policy in the undirected-edge
representation (Sections 1.1 and 2, printed pp.2, 5 = PDF pp.3, 6, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)): `ω ∼ μ` independent of
the live edge set `E`, and the policy receives the full cascades `C(v) = edgeCascade E {v}`. -/
noncomputable def edgeValue {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (q : Sym2 V → ℝ) (μ : Measure Ω) (π : Policy V k Ω) : ℝ :=
  ∫ ω, ∑ E : Finset (Sym2 V),
    edgeWeight q E * ((edgeCascade E (π.seeds ω (fun v => edgeCascade E {v}))).card : ℝ) ∂μ

end InflMaxAdapt


