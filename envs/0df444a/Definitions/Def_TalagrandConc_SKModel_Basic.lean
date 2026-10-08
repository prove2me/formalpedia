-- Prove2me | Definitions.Def_TalagrandConc_SKModel_Basic
-- name    : TalagrandConc_SKModel_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:43:57.162353+00:00
-- url     : https://prove2.me/theorems/842f93e6-f0a9-4a88-980b-6246cc04fe30
-- title:
--   The high-temperature Sherrington–Kirkpatrick partition function and coupling law
-- statement:
--   For $N\ge1$, let the interaction coordinates be the pairs $1\le i<j\le N$. A spin configuration $\varepsilon$ assigns $-1$ or $1$ to each site. For real couplings $h_{ij}$ and inverse temperature $\beta>0$, define
--
--   $$Z_N(h)=2^{-N}\sum_{\varepsilon\in\{-1,1\}^N}\exp\left(\frac{\beta}{\sqrt N}\sum_{i<j}h_{ij}\varepsilon_i\varepsilon_j\right),\qquad F_N(h)=\log Z_N(h).$$
--
--   For a probability law $\nu$ on $\mathbb R$, the couplings have the product law $P_N=\nu^{\otimes\binom N2}$. An admissible law has finite first three moments, mean and third moment zero, variance one, and a finite exponential moment $\mathbb E e^{\alpha|h|}$ for some $\alpha>0$. The light-tail condition further requires both $e^h$ and $e^{-h}$ to be integrable with expectations below $2$. A median $M$ of $F_N$ satisfies $P_N(F_N\le M)\ge1/2$ and $P_N(M\le F_N)\ge1/2$.
--
--   These definitions fix the common stochastic model for all the chapter's bounds.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), pp. 191–192, Eqs. (12.1)–(12.2) and paragraph before Theorem 12.1

import Mathlib

namespace TalagrandConc.SKModel

/-- The unordered interaction edges, represented by pairs with the smaller index first. -/
abbrev Interaction (N : ℕ) := {p : Fin N × Fin N // p.1 < p.2}

/-- A spin takes the values `-1` and `1`; `Bool.true` denotes `1`. -/
def spin {N : ℕ} (ε : Fin N → Bool) (i : Fin N) : ℝ :=
  if ε i then 1 else -1

/-- The Gibbs partition function of (12.1), normalized by the number of spin configurations. -/
noncomputable def partitionFunction (N : ℕ) (β : ℝ) (h : Interaction N → ℝ) : ℝ :=
  ((2 : ℝ) ^ N)⁻¹ *
    ∑ ε : Fin N → Bool,
      Real.exp ((β / Real.sqrt N) *
        ∑ p : Interaction N, h p * spin ε p.1.1 * spin ε p.1.2)

/-- The log partition function. -/
noncomputable def freeEnergy (N : ℕ) (β : ℝ) (h : Interaction N → ℝ) : ℝ :=
  Real.log (partitionFunction N β h)

/-- The common product law of the independent interactions. -/
noncomputable def couplingLaw (N : ℕ) (ν : MeasureTheory.Measure ℝ) :
    MeasureTheory.Measure (Interaction N → ℝ) :=
  MeasureTheory.Measure.pi (fun _ : Interaction N => ν)

/-- The standing centered, normalized, zero-third-moment, locally exponential-integrable law. -/
def AdmissibleLaw (ν : MeasureTheory.Measure ℝ) : Prop :=
  MeasureTheory.Integrable (fun x : ℝ => x) ν ∧
  MeasureTheory.Integrable (fun x : ℝ => x ^ 2) ν ∧
  MeasureTheory.Integrable (fun x : ℝ => x ^ 3) ν ∧
  (∫ x : ℝ, x ∂ν) = 0 ∧
  (∫ x : ℝ, x ^ 2 ∂ν) = 1 ∧
  (∫ x : ℝ, x ^ 3 ∂ν) = 0 ∧
  ∃ α : ℝ, 0 < α ∧ MeasureTheory.Integrable (fun x : ℝ => Real.exp (α * |x|)) ν

/-- The extra two-sided exponential moment condition of Theorem 12.1. -/
def LightTails (ν : MeasureTheory.Measure ℝ) : Prop :=
  MeasureTheory.Integrable (fun x : ℝ => Real.exp x) ν ∧
  MeasureTheory.Integrable (fun x : ℝ => Real.exp (-x)) ν ∧
  (∫ x : ℝ, Real.exp x ∂ν) < 2 ∧
  (∫ x : ℝ, Real.exp (-x) ∂ν) < 2

/-- A median, in the paper's two-sided probability sense. -/
def IsMedian (N : ℕ) (ν : MeasureTheory.Measure ℝ) (β M : ℝ) : Prop :=
  (couplingLaw N ν {h | freeEnergy N β h ≤ M}).toReal ≥ 1 / 2 ∧
  (couplingLaw N ν {h | M ≤ freeEnergy N β h}).toReal ≥ 1 / 2

end TalagrandConc.SKModel


