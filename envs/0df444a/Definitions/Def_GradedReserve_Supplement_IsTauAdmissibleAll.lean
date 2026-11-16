-- Prove2me | Definitions.Def_GradedReserve_Supplement_IsTauAdmissibleAll
-- name    : GradedReserve_Supplement_IsTauAdmissibleAll
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:44:37.439135+00:00
-- url     : https://prove2.me/theorems/521e4861-29c2-43ce-ae54-83d52a3d0c80
-- title:
--   $\tau$-admissibility with the guarantee in every BNE
-- statement:
--   $G_\pi$ is **$\tau$-admissible in every BNE** if it has at least one Bayes–Nash equilibrium and every BNE, asymmetric and mixed ones included, yields expected revenue at least $\tau$. Definition 2.1 asks this of symmetric BNE only; Theorem 3.4 shows that on graded reserves the two requirements select the same mechanisms.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 3.4, last sentence, p.7 (PDF 8); proof p.32 (PDF 33)

import Mathlib
import Definitions.Def_GradedReserve_Supplement_IsBNE
import Definitions.Def_GradedReserve_Supplement_expRevenue
import Definitions.Def_GradedReserve_Supplement_gradedMech
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- `τ`-admissibility of `G_π` with the guarantee required in every BNE (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 3.4, last
sentence, p.7, PDF 8: "on `G` the guarantee holds in every BNE, and Theorem 3.1 holds verbatim with
this stronger requirement"): `G_π` has at least one BNE, and every BNE, asymmetric and mixed ones
included, yields expected revenue at least `τ`. Compare Definition 2.1 (the base mission's
`GradedReserve.IsTauAdmissible`), which quantifies over symmetric BNE only. -/
def IsTauAdmissibleAll (n : ℕ) (f : ℝ → ℝ) (τ : ℝ) (π : ℝ → ℝ) : Prop :=
  (∃ σ : Fin n → Kernel ℝ ℝ, IsBNE (gradedMech n π) f σ) ∧
  ∀ σ : Fin n → Kernel ℝ ℝ, IsBNE (gradedMech n π) f σ → τ ≤ expRevenue (gradedMech n π) f σ

end GradedReserve.Supplement


