-- Prove2me | Definitions.Def_GradedReserve_Supplement_IsMonoBidShape
-- name    : GradedReserve_Supplement_IsMonoBidShape
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:48:39.229942+00:00
-- url     : https://prove2.me/theorems/11f41369-b9cb-45cf-8a89-84634fc9b7e2
-- title:
--   Strictly increasing bid function with participation threshold $a$
-- statement:
--   A bid function $\beta$ has participation threshold $a\in[0,1]$ and lowest valid bid $t_0$ if types $v<a$ exit, types $v\in(a,1]$ bid in $[t_0,1]$, and $\beta$ is strictly increasing on $(a,1]$. This is the shape of "the symmetric strictly increasing BNE" of Theorem 6.1.
--
--   **Formalization Note** The action of the single type $a$ is left free.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 6.1, p.11 (PDF 12); proof p.33 (PDF 34)

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- The shape of a strictly increasing symmetric equilibrium bid function with participation
threshold `a` and lowest valid bid `t₀` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 6.1, p.11, PDF 12: "the symmetric strictly
increasing BNE under continuous bids"; proof p.33, PDF 34: "Let `t₀` be the lowest valid bid of the
format (`r`, `d` or the entry threshold) and `a` the participation threshold of `β`"): types below
`a` exit (negative action), types in `(a, 1]` submit valid bids in `[t₀, 1]`, and `β` is strictly
increasing on `(a, 1]`.

**Formalization Note.** The action of the single type `a` is left free (one type has probability
zero). -/
def IsMonoBidShape (β : ℝ → ℝ) (a t₀ : ℝ) : Prop :=
  a ∈ Icc (0:ℝ) 1 ∧ (∀ v ∈ Ico (0:ℝ) a, β v < 0) ∧ (∀ v ∈ Ioc a 1, β v ∈ Icc t₀ 1) ∧
    StrictMonoOn β (Ioc a 1)

end GradedReserve.Supplement


