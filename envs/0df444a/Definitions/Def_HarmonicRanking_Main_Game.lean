-- Prove2me | Definitions.Def_HarmonicRanking_Main_Game
-- name    : HarmonicRanking_Main_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:05.605294+00:00
-- url     : https://prove2.me/theorems/e704002b-133d-4eb0-af8f-4a49542814ef
-- title:
--   Continuous two-curve variational objective
-- statement:
--   A curve pair consists of arbitrary functions $a,b:[0,1]\to[0,1]$. It is admissible when both are Lebesgue completion-measurable and the strict upper indicators $U(x,y)=1_{y>a(x)}$ and $\widetilde V(x,y)=1_{x>b(y)}$ are disjoint almost everywhere in the unit square. Put $S=(1-U)(1-\widetilde V)$ and define
--
--   $$
--   \Gamma(h,a,b)=\int_{[0,1]^2}\!\left[S+(U+\widetilde V)\bigl(g_h(x,a(x))+g_h(y,b(y))\bigr)\right]dx\,dy,
--   $$
--   $$
--   \gamma_{\rm EW}(h)=\inf_{(a,b)\in\mathcal T}\Gamma(h,a,b),\qquad
--   \gamma_{\rm EW}=\sup_{h\text{ a score}}\gamma_{\rm EW}(h).
--   $$
--
--   The curves have no cross-section monotonicity or grid restriction. Completion-measurability uses a.e. measurable representatives for Lebesgue law. For source scores these are bounded integrable payoffs; $a=b=1$ witnesses a nonempty domain and gives payoff 1. The values are defined from these actual domains rather than supplied as free parameters. This is the shared continuous interface for Propositions 4.2 and 5.2.
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), pp. 13–14, Eqs. (10)–(19), Definition 4.1

import Definitions.Def_HarmonicRanking_Main_Instance

open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace HarmonicRanking.Main

abbrev UnitRank := Set.Icc (0 : ℝ) 1

def unitLaw : Measure UnitRank := Measure.comap Subtype.val volume

def squareLaw : Measure (UnitRank × UnitRank) := unitLaw.prod unitLaw

/-- Arbitrary curves, with no cross-section monotonicity constraint. -/
structure Curves where
  a : UnitRank → UnitRank
  b : UnitRank → UnitRank

/-- Completion-measurability is expressed by a.e. measurability for Lebesgue law. -/
def Curves.admissible (c : Curves) : Prop :=
  AEMeasurable c.a unitLaw ∧ AEMeasurable c.b unitLaw ∧
  ∀ᵐ z ∂squareLaw, ¬ ((c.a z.1 : ℝ) < z.2 ∧ (c.b z.2 : ℝ) < z.1)

def gameIntegrand (h : ℝ → ℝ) (c : Curves) (z : UnitRank × UnitRank) : ℝ :=
  let U : ℝ := if (c.a z.1 : ℝ) < z.2 then 1 else 0
  let V : ℝ := if (c.b z.2 : ℝ) < z.1 then 1 else 0
  (1 - U) * (1 - V) + (U + V) *
    (gain h z.1 (c.a z.1) + gain h z.2 (c.b z.2))

def Gamma (h : ℝ → ℝ) (c : Curves) : ℝ :=
  ∫ z, gameIntegrand h c z ∂squareLaw

/-- Nonempty bounded set of payoffs for every IsScore h; a=b=1 is feasible. -/
def gammaEW (h : ℝ → ℝ) : ℝ := sInf {v | ∃ c : Curves, c.admissible ∧ Gamma h c = v}

/-- The full score class, not only the step scores. -/
def gammaFamily : ℝ := sSup {v | ∃ h : ℝ → ℝ, IsScore h ∧ gammaEW h = v}

end HarmonicRanking.Main


