-- Prove2me | Definitions.Def_RecGaussColoring_Main_Parameters
-- name    : RecGaussColoring_Main_Parameters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:23:28.083533+00:00
-- url     : https://prove2.me/theorems/30879329-1fe1-40b9-811f-d3a5e5858579
-- title:
--   Certificate transition constants and potential
-- statement:
--   For a real parameter $c$, let $c^\dagger=(\sqrt{97}-7)/12$, $L=\tfrac12\sqrt{(1+4c)/(1+c)}$, and $q=\sqrt{c/(1+c)}$. The transition functions are
--   $$
--   B(a,y)=-\frac a2+\frac{\sqrt3}{2}\sqrt{1-a^2}\,y,\qquad
--   A(a,y)=\frac12\sqrt{1-a^2}+\frac{\sqrt3}{2}ay,
--   $$
--   $$
--   \lambda_{\rm new}=\frac{\lambda A(a,y)+3/2-(\sqrt3/2)\sqrt{(5+3c-\lambda^2)(c/(1+c)-y^2)}}{\sqrt{1-B(a,y)^2}}-\tau.
--   $$
--   The module also defines $b_2(y)=1/4+3y/4$, the full $\lambda_2(y)$ of Lemma 2.7, $\nu_0(c)$ of (2.19), $V(a,\lambda)=\lambda-3(1+c)(1/\sqrt{1-a^2}-1)/(1+4c)$, the increment $\mu(c)$ of p. 18, and $K=[-L,L]\times[0,\sqrt{5+3c}]$. The sparse-degree exponent is $3(1+c)/(5+3c)$, the independent-set exponent is $1-1/(5+3c)$, and the final coloring exponent is $(13-\sqrt{97})/18$.
--
--   These are explicit arithmetic functions, with no inequalities or positivity assertions built into them. Polylogarithmic factors use $n^\alpha(\log(n+2))^k$ for $k\in\mathbb N$.
-- source:
--   Ijay Narang, Yukai Tang, STOC 2027 submission #295 (October 2026), (2.17)–(2.19); Lemmas 2.7–2.8, pp. 12,16; potential and µ, pp. 16,18, p. 15. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/295.pdf

import Mathlib

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
noncomputable section

namespace RecGaussColoring.Main

/-- Theorem 1.5, p. 5. -/
def cDagger : ℝ := (Real.sqrt 97 - 7) / 12
/-- Page 15. -/
def corrBound (c : ℝ) : ℝ := (1/2 : ℝ) * Real.sqrt ((1+4*c)/(1+c))
def typeBound (c : ℝ) : ℝ := Real.sqrt (c/(1+c))
def nuZero (c : ℝ) : ℝ := min
  (Real.sqrt 3 / (4*(1+c)) * (Real.sqrt (1+c) - Real.sqrt (c*(1+4*c))))
  ((3/2 : ℝ) - Real.sqrt 3 / 2 * Real.sqrt (c*(5+3*c)/(1+c)))
/-- Equations (2.17) and (2.18). -/
def transB (a y : ℝ) : ℝ := -a/2 + Real.sqrt 3/2 * Real.sqrt (1-a^2) * y
def transA (a y : ℝ) : ℝ := (1/2 : ℝ) * Real.sqrt (1-a^2) + Real.sqrt 3/2 * a*y
/-- Lemma 2.7, p. 12. -/
def bTwo (y : ℝ) : ℝ := (1/4 : ℝ) + (3/4 : ℝ)*y
def lambdaTwo (c y : ℝ) : ℝ :=
  ((9/4 : ℝ) - (3/4 : ℝ)*y - Real.sqrt 3/2 *
    Real.sqrt ((2+3*c)*(c/(1+c)-y^2))) / Real.sqrt (1-(bTwo y)^2)
/-- Lemma 2.8, p. 16. -/
def nextLambda (c a lam y τ : ℝ) : ℝ :=
  (lam * transA a y + (3/2 : ℝ) - Real.sqrt 3/2 *
    Real.sqrt ((5+3*c-lam^2)*(c/(1+c)-y^2))) /
      Real.sqrt (1-(transB a y)^2) - τ
/-- Pages 16 and 18. -/
def potential (c a lam : ℝ) : ℝ :=
  lam - 3*(1+c)/(1+4*c) * (1/Real.sqrt (1-a^2)-1)
def mu (c : ℝ) : ℝ :=
  3/(8*(1+c)) * (3*Real.sqrt ((1+c)/(1+4*c))-Real.sqrt (5+3*c))
def parameterRegion (c : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc (-corrBound c) (corrBound c) ×ˢ Set.Icc 0 (Real.sqrt (5+3*c))

def sparseExponent (c : ℝ) : ℝ := 3*(1+c)/(5+3*c)
def independentExponent (c : ℝ) : ℝ := 1-1/(5+3*c)
def colorExponent : ℝ := (13-Real.sqrt 97)/18

def softPower (α : ℝ) (k : ℕ) (n : ℕ) : ℝ :=
  (n : ℝ)^α * (Real.log ((n : ℝ)+2))^k

end RecGaussColoring.Main


