-- Prove2me | Definitions.Def_GRH_SquarefreeBilinear
-- name    : GRH_SquarefreeBilinear
-- status  : Definition
-- author  : @pragyan
-- created : 2026-11-21T01:11:12.925693+00:00
-- url     : https://prove2.me/theorems/94c78a2f-0bbc-4e51-89db-7c94fb5dad1a
-- title:
--   Squarefree progression density and centered Liouville bilinear sums
-- statement:
--   For a positive modulus $q$, define the squarefree progression density and a coprime harmonic Liouville sum by
--   $$\kappa_q=\frac1q\sum_{\substack{k\ge1\\(k,q)=1}}\frac{\mu(k)}{k^2},\qquad H_q(U)=\sum_{\substack{1\le d\le U\\(d,q)=1}}\frac{\lambda(d)}d.$$
--   For a residue class $a$, let $A_{d,e}(N;q,a)$ count positive squarefree $r\le\lfloor N/(de)\rfloor$ with $der\equiv a\pmod q$. Set $U=\lfloor\sqrt N\rfloor$ and define
--   $$E_q(N,a)=\sum_{1\le d,e\le U}\lambda(d)\lambda(e)\left(A_{d,e}(N;q,a)-\mathbf1_{(d,q)=(e,q)=1}\frac{\kappa_q N}{de}\right).$$
--   The quotient in the subtracted term is real. For reduced residue classes the density agrees with the standard squarefree progression main term. These definitions separate that scalar main term from the signed centered discrepancy; they assert no cancellation estimates.
-- source:
--   R. M. Nunes, Squarefree numbers in arithmetic progressions, arXiv:1402.0684v2, §1, equation (1.1), https://arxiv.org/html/1402.0684#S1.E1 (squarefree density and error convention). NIST DLMF §27.2(i), equations (27.2.12)–(27.2.13), https://dlmf.nist.gov/27.2#E13 (Möbius and Liouville functions). The bilinear combination is defined for the decomposition of https://prove2.me/theorems/dd1bd87e-604f-4753-a99c-ded025ae6c8e.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section
open scoped BigOperators
namespace GRH

def squarefreeProgressionCount (q : ℕ) [NeZero q] (a : ZMod q) (N d e : ℕ) : ℝ :=
  (((Finset.Ioc 0 (N / (d * e))).filter
    (fun r => Squarefree r ∧ ((d * e * r : ℕ) : ZMod q) = a)).card : ℝ)

def reducedLiouvilleHarmonic (q : ℕ) [NeZero q] (U : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ioc 0 U, if IsUnit (d : ZMod q) then
    (ArithmeticFunction.liouville d : ℝ) / (d : ℝ) else 0

def squarefreeProgressionDensity (q : ℕ) : ℝ :=
  (1 / (q : ℝ)) * ∑' k : ℕ, if Nat.Coprime k q then
    (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 else 0

def centeredSquarefreeBilinear (q : ℕ) [NeZero q] (a : ZMod q) (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.liouville d : ℝ) *
    ∑ e ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.liouville e : ℝ) *
      (squarefreeProgressionCount q a N d e -
        if IsUnit (d : ZMod q) ∧ IsUnit (e : ZMod q) then
          squarefreeProgressionDensity q * (N : ℝ) / ((d : ℝ) * (e : ℝ)) else 0)

end GRH


