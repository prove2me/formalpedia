-- Prove2me | Definitions.Def_PrefRobustSR_WorstCase_Model
-- name    : PrefRobustSR_WorstCase_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:08:49.332765+00:00
-- url     : https://prove2.me/theorems/1f0b95ea-783b-4a85-b1c0-4a7628f3505d
-- title:
--   Definition 2.1 and (1.2)–(1.4): loss class and shortfall risks
-- statement:
--   Let $(\Omega,\mathcal B,P)$ be a probability space and let $Z$ be a real position. The **loss class** $\mathcal L$ consists of convex, nondecreasing functions $l:\mathbb R\to\mathbb R$ that are strictly increasing on $[z_0,\infty)$ for some $z_0<0$.
--
--   For a cash amount $t$, set $g_{P,l,Z}(t)=\mathbb E_P[l(-Z-t)]-l(0)$. Define the individual shortfall risk, the preference robust shortfall risk for a set $L$ of loss functions, and the worst risk for a set $\mathcal R$ of risk measures by
--   $$
--   SR_l^P(Z)=\inf\{t\in\mathbb R:g_{P,l,Z}(t)\le0\},\qquad
--   SR_L^P(Z)=\inf\{t\in\mathbb R:\sup_{l\in L}g_{P,l,Z}(t)\le0\},\qquad
--   \varrho_{\mathcal R}(Z)=\sup_{\rho\in\mathcal R}\rho(Z).
--   $$
--   These definitions connect the paper's cash-acceptability model to its representation theorem.
--
--   **Formalization Note** Expectations use the published extended expectation `DupacovaWets.Consistency.expect`: they are $+\infty$ if the positive part is not integrable. Infima and suprema are in the extended reals, so an empty feasible set has infimum $+\infty$, an unbounded feasible set has infimum $-\infty$, and a supremum over an empty $L$ is $-\infty$. Each $l(0)$ is subtracted before taking the supremum. Risk-measure maps act on all real functions; the theorems evaluate them on the paper's admissible positions.
-- source:
--   Delage, Guo & Xu, Shortfall risk models when information of loss function is incomplete, preprint dated April 25, 2018 (later article DOI: https://doi.org/10.1287/opre.2021.2212; numbering follows the preprint), pp. 2–4, (1.2), (1.3), (1.4), Definition 2.1

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect

namespace PrefRobustSR.WorstCase

open MeasureTheory

/-- Definition 2.1, p. 4: the class 𝓛 of convex, non-decreasing loss functions
that are strictly increasing from some negative argument onward. -/
def LossClass : Set (ℝ → ℝ) :=
  {l | ConvexOn ℝ Set.univ l ∧ Monotone l ∧
    ∃ z0 : ℝ, z0 < 0 ∧ StrictMonoOn l (Set.Ici z0)}

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The expected loss above the benchmark l(0), with the extended expectation convention. -/
noncomputable def gap (P : Measure Ω) (l : ℝ → ℝ) (Z : Ω → ℝ) (t : ℝ) : EReal :=
  DupacovaWets.Consistency.expect P
    (fun ω => ((l (-Z ω - t) : ℝ) : EReal)) - ((l 0 : ℝ) : EReal)

/-- Equation (1.2), p. 2: the utility-based shortfall risk SR^P_l(Z). -/
noncomputable def SR (P : Measure Ω) (l : ℝ → ℝ) (Z : Ω → ℝ) : EReal :=
  sInf ((fun t : ℝ => (t : EReal)) '' {t : ℝ | gap P l Z t ≤ 0})

/-- Equation (1.3), p. 3: the preference robust shortfall risk SR^P_L(Z).
The one constraint takes the supremum of each function's own gap. -/
noncomputable def SRL (P : Measure Ω) (L : Set (ℝ → ℝ)) (Z : Ω → ℝ) : EReal :=
  sInf ((fun t : ℝ => (t : EReal)) ''
    {t : ℝ | (⨆ l ∈ L, gap P l Z t) ≤ 0})

/-- Equation (1.4), p. 3: the worst risk over a set 𝓡 of risk measures. -/
noncomputable def robustRisk (R : Set ((Ω → ℝ) → EReal)) (Z : Ω → ℝ) : EReal :=
  ⨆ ρ ∈ R, ρ Z

end PrefRobustSR.WorstCase


