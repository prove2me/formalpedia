-- Prove2me | Definitions.Def_InfHorizonVP_HypH1
-- name    : InfHorizonVP_HypH1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:18:07.623321+00:00
-- url     : https://prove2.me/theorems/14c06994-e56a-4a50-980b-9e6cc712b88b
-- title:
--   Hypothesis (H1): $\mathcal A_{(t,\xi)}\neq\emptyset$
-- statement:
--   **(H1)** For every $(t,\xi)\in\mathbb R_+\times E$ the set $\mathcal A_{(t,\xi)}$ of admissible trajectories is nonempty.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §3.1, p.8, (H1)

import Mathlib
import Definitions.Def_InfHorizonVP_Admissible
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Hypothesis (H1).**
Frankowska, Sagara, arXiv:1801.00400v3, §3.1, p.8: "(H1) 𝒜_(t,ξ) is nonempty for every
(t, ξ) ∈ R+ × E." -/
def HypH1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Γ : ℝ → E → Set E) : Prop :=
  ∀ t, 0 ≤ t → ∀ ξ : E, (Admissible Γ t ξ).Nonempty

end InfHorizonVP


