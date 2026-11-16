-- Prove2me | Definitions.Def_GradedReserve_Supplement_IsRevPreserving
-- name    : GradedReserve_Supplement_IsRevPreserving
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:46:51.283709+00:00
-- url     : https://prove2.me/theorems/489e1fca-a295-4c9a-ac5b-6937a7755f3a
-- title:
--   Revenue-preserving choice of the upper reserve
-- statement:
--   A curve $\rho\mapsto r'(\rho)$, $\rho\in[0,\delta)$, is **revenue preserving** if $r'(0)=r$ and for every $\rho\in[0,\delta)$ the two-tier rule $\pi_{h,\rho,r'(\rho)}$ has a symmetric BNE and every symmetric BNE has rational revenue exactly $\tau$ ("with $r'$ chosen so that the rational revenue equals $\tau$").
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 3.6, p.8 (PDF 9); proof p.17 (PDF 18)

import Mathlib
import Definitions.Def_GradedReserve_IsSymBNE
import Definitions.Def_GradedReserve_revRat
import Definitions.Def_GradedReserve_Supplement_twoTier
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- A revenue-preserving choice of the upper reserve in Theorem 3.6 (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 3.6, p.8, PDF 9:
"with `r′` chosen so that the rational revenue equals `τ`"; proof p.17, PDF 18): the curve
`ρ ↦ r′(ρ)` starts at `r′(0) = r`, and for every `ρ ∈ [0, δ)` the two-tier rule
`twoTier r h ρ (r′ ρ)` has a symmetric BNE and every symmetric BNE has rational revenue `τ`. -/
def IsRevPreserving (f : ℝ → ℝ) (n : ℕ) (τ r h δ : ℝ) (r' : ℝ → ℝ) : Prop :=
  r' 0 = r ∧ ∀ ρ ∈ Ico (0:ℝ) δ,
    (∃ σ : Kernel ℝ ℝ, IsSymBNE f n (twoTier r h ρ (r' ρ)) σ) ∧
    ∀ σ : Kernel ℝ ℝ, IsSymBNE f n (twoTier r h ρ (r' ρ)) σ →
      revRat f n (twoTier r h ρ (r' ρ)) σ = τ

end GradedReserve.Supplement


