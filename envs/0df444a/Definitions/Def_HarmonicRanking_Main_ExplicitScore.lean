-- Prove2me | Definitions.Def_HarmonicRanking_Main_ExplicitScore
-- name    : HarmonicRanking_Main_ExplicitScore
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:35:05.115817+00:00
-- url     : https://prove2.me/theorems/692f300a-e6c4-4fc7-8ce9-8b5b5064a745
-- title:
--   Exact 240-step score and individually rounded capacities
-- statement:
--   Set $m=240$, $p=0.9938$, $c_1=-0.74112772$, $c_2=0.58515414$, and $\delta=0.30$, all exact rationals. Define
--
--   $$
--   \widetilde h(x)=(1-x)^p\exp\bigl(c_1((1-x)-1)+c_2((1-x)^2-1)\bigr),\qquad
--   H_i=\left\lfloor10^{30}\frac{\widetilde h((i-1+\delta)/240)}{\widetilde h(\delta/240)}\right\rfloor.
--   $$
--
--   The algorithm's score $h^\star$ is the 240-step score with heights $H_i$. Its exact network is the preceding threshold network. For every already-normalized arc capacity $c_e$, define the integer capacity $\widehat c_e=\lfloor10^{12}c_e\rfloor$; in particular each hard arc has capacity $2\cdot10^{12}$. Integer flows have integer amounts satisfying these bounds and conservation at nonterminal vertices. Their value is net integer source outflow.
--
--   The target factor is $698015475248/10^{12}$. This prescription uses exact real powers, exponentials, and floors, not floating-point evaluations or an assumed external list. It supplies the fixed data for the unconditional certificate theorem; neither validity of a certificate nor a numerical lower bound is a field or hypothesis of this definition.
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), pp. 19–20, Eq. (37), integer-height prescription, Eqs. (38)–(39), rounding before Lemma 6.1

import Definitions.Def_HarmonicRanking_Main_Network

set_option autoImplicit false
noncomputable section

namespace HarmonicRanking.Main

/-- Equation (37), exact terminating rational parameters and real power. -/
def smoothProfile (x : ℝ) : ℝ :=
  (1-x) ^ (9938 / 10000 : ℝ) *
    Real.exp ((-74112772 / 100000000 : ℝ) * ((1-x)-1) +
      (58515414 / 100000000 : ℝ) * ((1-x)^2-1))

/-- The manuscript's exact prescription, not floating-point samples or a free list. -/
def explicitHeightInt (i : Fin 240) : ℤ :=
  ⌊(10 : ℝ)^30 * smoothProfile (((i.val : ℝ) + 30/100) / 240) /
    smoothProfile ((30/100 : ℝ) / 240)⌋

def explicitHeights (i : Fin 240) : ℝ := explicitHeightInt i

def explicitScore : ℝ → ℝ := stepScore explicitHeights

def certificateScale : ℤ := 10^12

def competitiveFactor : ℝ := (698015475248 : ℝ) / 10^12

/-- Rounding is applied to each normalized arc, before any aggregation.
Hard capacities scale to integers, so their floor is exactly 2*10^12. -/
def roundedCapacity (e : StepArc 240) : ℤ :=
  ⌊(certificateScale : ℝ) * stepCapacity explicitHeights e⌋

def integerDivergence (f : StepArc 240 → ℤ) (v : StepNode 240) : ℤ :=
  (∑ e, if (stepDigraph 240).tail e = v then f e else 0) -
    ∑ e, if (stepDigraph 240).head e = v then f e else 0

def IntegerFeasible (f : StepArc 240 → ℤ) : Prop :=
  (∀ e, 0 ≤ f e ∧ f e ≤ roundedCapacity e) ∧
  ∀ v, v ≠ .source → v ≠ .sink → integerDivergence f v = 0

def integerFlowValue (f : StepArc 240 → ℤ) : ℤ := integerDivergence f .source

end HarmonicRanking.Main


