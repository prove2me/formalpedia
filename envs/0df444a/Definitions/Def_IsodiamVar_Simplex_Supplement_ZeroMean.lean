-- Prove2me | Definitions.Def_IsodiamVar_Simplex_Supplement_ZeroMean
-- name    : IsodiamVar_Simplex_Supplement_ZeroMean
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:49:09.689838+00:00
-- url     : https://prove2.me/theorems/5fbb3155-6665-4592-bfb9-53027e8fba4a
-- title:
--   Equation (2.1) — probabilities on K with zero barycenter
-- statement:
--   Let $\mathcal P(K)$ denote the Borel probability measures carried by $K\subseteq\mathbb R^n$. The zero-mean class is
--
--   $$\mathcal P_0(K)=\{\mu\in\mathcal P(K):\bar x(\mu)=0\}.$$
--
--   It is the feasible class in Proposition 2.1. No assumption that this class is nonempty is built into the predicate.
-- source:
--   Lim & McCann, Geometrical bounds for the variance and recentered moments, arXiv:2001.11851v1, p. 8, (2.1)

import Definitions.Def_IsodiamVar_Simplex_Supplement_Barycenter

open MeasureTheory

namespace IsodiamVar.Simplex.Supplement

/-- Equation (2.1), p. 8: probability measures on K with zero barycenter. -/
def InP0 {n : ℕ} (K : Set (E n)) (μ : Measure (E n)) : Prop :=
  InP K μ ∧ barycenter μ = 0

end IsodiamVar.Simplex.Supplement


