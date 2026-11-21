-- Prove2me | Definitions.Def_GRH_MoebiusBilinear
-- name    : GRH_MoebiusBilinear
-- status  : Definition
-- author  : @pragyan
-- created : 2026-11-21T01:50:39.296+00:00
-- url     : https://prove2.me/theorems/9935e74c-b3f6-46ca-ad4f-3cb1961d1baf
-- title:
--   Möbius harmonic factor and centered progression-count bilinear sums
-- statement:
--   For a positive modulus $q$, let $A_{d,e}(N;q,a)$ count $1\le r\le N/(de)$ satisfying $der\equiv a\pmod q$, and put
--   $$H_{\mu,q}(U)=\sum_{1\le d\le U,\,(d,q)=1}\frac{\mu(d)}d.$$
--   The centered bilinear quantity subtracts the progression density for invertible $d,e$:
--   $$E_\mu(N;q,a)=\sum_{d,e\le\sqrt N}\mu(d)\mu(e)\left(A_{d,e}(N;q,a)-\mathbf1_{(de,q)=1}\frac{N}{qde}\right).$$
--   These finite definitions separate the principal harmonic main term from cancellation in the arithmetic-progression rounding errors. All cutoffs are integer floors; empty sums at $N=0$ are zero.
-- source:
--   Adapted finite notation for Prove2Me theorem GRH.moebius_reduced_progression_bilinear_power_bound, https://prove2.me/theorems/1e39fbca-7acc-40a2-baab-ab807852220a. The bilinear truncation is Helfgott–Thompson, Summing μ(n): a faster elementary algorithm, §2, equations (2.1)–(2.2), https://doi.org/10.1007/s40993-022-00408-8. Centering subtracts the elementary density 1/q in a reduced arithmetic progression; no analytic estimate is included.

import Definitions.Def_GRH_SquarefreeBilinear

noncomputable section
open scoped BigOperators
namespace GRH

def moebiusProgressionCount (q : ℕ) [NeZero q] (a : ZMod q) (N d e : ℕ) : ℝ :=
  (((Finset.Ioc 0 (N / (d * e))).filter
    (fun r => ((d * e * r : ℕ) : ZMod q) = a)).card : ℝ)

def reducedMoebiusHarmonic (q : ℕ) [NeZero q] (U : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ioc 0 U, if IsUnit (d : ZMod q) then
    (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) else 0

def centeredMoebiusBilinear (q : ℕ) [NeZero q] (a : ZMod q) (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.moebius d : ℝ) *
    ∑ e ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.moebius e : ℝ) *
      (moebiusProgressionCount q a N d e -
        if IsUnit (d : ZMod q) ∧ IsUnit (e : ZMod q) then
          (1 / (q : ℝ)) * (N : ℝ) / ((d : ℝ) * (e : ℝ)) else 0)

end GRH


