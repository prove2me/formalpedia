-- Prove2me | Definitions.Def_PermanentStars_Counting_Parameters
-- name    : PermanentStars_Counting_Parameters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:25.215594+00:00
-- url     : https://prove2.me/theorems/908cb01d-bd38-445d-8fb4-9d61b8319fd3
-- title:
--   The 280 explicit rational cutoff parameters
-- statement:
--   Use zero-based $k=j-1$ and define
--   $$r_0=1,\quad r_{k+1}=\lceil4r_k/3\rceil.$$
--   There are 280 selected cutoffs. The fractions and exponential bases are
--   $$\alpha_0=11/100,\ c_0=100/89,\qquad \alpha_k=1/[r_k(k+14)],\ c_k=2-2/(3r_k)\quad(k>0).$$
--   Set $\beta_0=2$, $\beta_k=r_k-r_{k-1}$ for $k>0$, and $L=\sum_{k<280}\beta_k\alpha_k$. The parameter record is computed from this list using a finite lookup by cutoff value.
--
--   All arithmetic here is exact. Strict increase, validity, the mass and exponent inequalities and the final resource bounds remain conclusions of Proposition A.1. No floating-point assertion or logarithm interval is an axiom.
-- source:
--   Radu Curticapean, STOC 2027 submission #1331 (October 2026), Appendix A, equations (26)–(29), pp.15–16

import Definitions.Def_PermanentStars_Counting_Partitions

namespace PermanentStars.Counting

/-- Appendix A, (28): index k is the paper's j=k+1. Integer division implements the ceiling. -/
def explicitCutoff : ℕ → ℕ
  | 0 => 1
  | k + 1 => (4 * explicitCutoff k + 2) / 3

def explicitAlpha (k : ℕ) : ℚ :=
  if k = 0 then 11 / 100 else 1 / ((explicitCutoff k : ℚ) * (k + 14))

def explicitC (k : ℕ) : ℚ :=
  if k = 0 then 100 / 89 else 2 - 2 / (3 * (explicitCutoff k : ℚ))

def explicitBeta (k : ℕ) : ℕ :=
  if k = 0 then 2 else explicitCutoff k - explicitCutoff (k - 1)

def explicitMass : ℚ :=
  ∑ k ∈ Finset.range 280, (explicitBeta k : ℚ) * explicitAlpha k

/-- The finite parameters are computed from (28)--(29), not free objects constrained by hypotheses.
The sum is a lookup by the cutoff value; strict increase is a conclusion of Proposition A.1. -/
def explicitParameters : Cutoffs :=
  ⟨(Finset.range 280).image explicitCutoff,
    fun r => ∑ k ∈ Finset.range 280, if explicitCutoff k = r then explicitAlpha k else 0⟩

end PermanentStars.Counting


