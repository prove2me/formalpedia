-- Prove2me | Definitions.Def_GradedReserve_IsTauAdmissible
-- name    : GradedReserve_IsTauAdmissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:34:59.561899+00:00
-- url     : https://prove2.me/theorems/37642394-ca54-4f40-97e4-5514a85c2d30
-- title:
--   $\tau$-admissibility (Definition 2.1)
-- statement:
--   **Definition 2.1** (Rational revenue guarantee). The mechanism $G_\pi$ is **$\tau$-admissible** if it has at least one symmetric Bayes–Nash equilibrium and every symmetric Bayes–Nash equilibrium yields expected revenue $\mathrm{Rev}_{\mathrm{rat}}\ge\tau$.
--
--   The design problem maximizes the anchored revenue over $\tau$-admissible mechanisms.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Definition 2.1, p.4 (PDF 5)

import Mathlib
import Definitions.Def_GradedReserve_IsSymBNE
import Definitions.Def_GradedReserve_revRat
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- Definition 2.1 (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Definition 2.1, p.4, PDF 5): `G_π` is `τ`-admissible if it has at least one
symmetric BNE and every symmetric BNE yields expected revenue `Rev_rat ≥ τ`. -/
def IsTauAdmissible (f : ℝ → ℝ) (n : ℕ) (τ : ℝ) (π : ℝ → ℝ) : Prop :=
  (∃ σ, IsSymBNE f n π σ) ∧ ∀ σ, IsSymBNE f n π σ → τ ≤ revRat f n π σ

end GradedReserve


