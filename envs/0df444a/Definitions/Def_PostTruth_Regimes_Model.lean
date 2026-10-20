-- Prove2me | Definitions.Def_PostTruth_Regimes_Model
-- name    : PostTruth_Regimes_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:56.54534+00:00
-- url     : https://prove2.me/theorems/52cb03c5-7996-4a62-9402-9c8ecb9ddd20
-- title:
--   The mean-field misinformation model, prior and split laws, beliefs, and mislearning
-- statement:
--   The state is $\theta\in\{L,R\}$. Organic news matches the state with probability $p$, while a fraction $q$ of messages is misinformation; the random split $r$ is the fraction of misinformation advocating $R$. Initial beliefs $x$ are distributed according to $H$, and the split has density $f$ and law $F$.
--
--   The model fixes the face-value posteriors after one $R$ or $L$ message, the large-population DeGroot consensus $\pi_\infty(\theta,r)$ obtained by averaging those posteriors over $H$, and the Bayesian posterior $\pi_B(\theta,r,x)$ obtained by comparing the densities of the two splits that explain the observed message share. Write $d=(2p-1)(1-q)/q$. Under state $L$ those splits are $r$ and $r-d$; under state $R$ they are $r+d$ and $r$.
--
--   A society mislearns if its terminal belief favors the wrong state for a positive mass of agents. A tie at $1/2$ counts as wrong. Its mislearning probability is the $F$-measure of the set of splits at which it mislearns. The DeGroot cutoffs are $\widetilde r_L=(1-2(1-q)(1-p))/(2q)$ and $\widetilde r_R=(1-2(1-q)p)/(2q)$, and the misinformation threshold is $q^*=(2p-1)/(2p)$.
--
--   These definitions give a common model for the two learning rules and the threshold results.
--
--   **Formalization Note** The paper's large-population limit is represented by the formulas used in its proofs. The Bayesian belief at $T$ is the period-two posterior, since later observations reveal no new information. $H$ is atomless and concentrated on $[0,1]$; $F$ is supplied by a measurable nonnegative density of integral one, supported in $[0,1]$. Full support means a density uniformly bounded below by a positive constant on the specified interval and zero outside it. Mislearning probabilities are extended nonnegative reals.
-- source:
--   Mostagir & Siderius, Learning in a Post-Truth World, SSRN working paper 3879174 (version of 2 July 2021), pp. 4–6 and 18–19, §2, equations (1)–(2), proofs of Lemmas 1–2; https://ssrn.com/abstract=3879174

import Mathlib

namespace PostTruth.Regimes

open MeasureTheory
open scoped ENNReal

/-- The true state, with beliefs interpreted as probabilities of `R`. -/
inductive State | L | R

/-- The nondegenerate misinformation regime in Section 2. -/
def Standing (p q : ℝ) : Prop :=
  (1 / 2 : ℝ) < p ∧ p ≤ 1 ∧ 0 < q ∧ q < 1 / 2

/-- A continuous prior law of beliefs in the unit interval. -/
structure PriorLaw (H : Measure ℝ) : Prop where
  isProb : IsProbabilityMeasure H
  conc : H ((Set.Icc (0 : ℝ) 1)ᶜ) = 0
  noAtoms : NullSingletonClass H

/-- Symmetry of initial beliefs about the midpoint. -/
def Symmetric (H : Measure ℝ) : Prop :=
  H.map (fun x : ℝ => 1 - x) = H

/-- The density-based full-support convention in footnotes 7 and 8. -/
def PriorFullSupportOn (H : Measure ℝ) (a b : ℝ) : Prop :=
  ∃ h : ℝ → ℝ≥0∞, Measurable h ∧ H = volume.withDensity h ∧
    (∃ μ : ℝ, 0 < μ ∧ ∀ x ∈ Set.Icc a b, ENNReal.ofReal μ < h x) ∧
    H ((Set.Icc a b)ᶜ) = 0

/-- A density for the fraction of misinformation advocating `R`. -/
structure SplitLaw where
  f : ℝ → ℝ
  meas : Measurable f
  nonneg : ∀ r, 0 ≤ f r
  zero_off : ∀ r, r ∉ Set.Icc (0 : ℝ) 1 → f r = 0
  total : ∫ r, f r = 1

noncomputable def SplitLaw.law (F : SplitLaw) : Measure ℝ :=
  volume.withDensity (fun r => ENNReal.ofReal (F.f r))

/-- Positivity on exactly one closed interval, as in footnotes 7 and 8. -/
def SplitLaw.FullSupportOn (F : SplitLaw) (a b : ℝ) : Prop :=
  (∃ μ : ℝ, 0 < μ ∧ ∀ r ∈ Set.Icc a b, μ < F.f r) ∧
  ∀ r, r ∉ Set.Icc a b → F.f r = 0

/-- The large-population fraction of messages advocating `R`. -/
def shareR (p q : ℝ) : State → ℝ → ℝ
  | .L, r => (1 - p) * (1 - q) + q * r
  | .R, r => p * (1 - q) + q * r

/-- Equation (1): the face-value update after an `R` message. -/
noncomputable def postR (p x : ℝ) : ℝ :=
  p * x / (p * x + (1 - p) * (1 - x))

/-- Equation (2): the face-value update after an `L` message. -/
noncomputable def postL (p x : ℝ) : ℝ :=
  (1 - p) * x / ((1 - p) * x + p * (1 - x))

/-- Mean-field DeGroot consensus from the proof of Lemma 1. -/
noncomputable def piDeGroot (p q : ℝ) (H : Measure ℝ)
    (θ : State) (r : ℝ) : ℝ :=
  ∫ x, (shareR p q θ r * postR p x +
    (1 - shareR p q θ r) * postL p x) ∂H

/-- Distance between the two narrative splits that explain one message share. -/
noncomputable def gap (p q : ℝ) : ℝ := (2 * p - 1) * (1 - q) / q

/-- The split for the narrative in which the true state is `L`. -/
noncomputable def splitL (p q : ℝ) : State → ℝ → ℝ
  | .L, r => r
  | .R, r => r + gap p q

/-- The split for the narrative in which the true state is `R`. -/
noncomputable def splitR (p q : ℝ) : State → ℝ → ℝ
  | .L, r => r - gap p q
  | .R, r => r

/-- Mean-field Bayesian posterior at the second period, from Lemma 2. -/
noncomputable def piBayes (p q : ℝ) (F : SplitLaw) (θ : State)
    (r x : ℝ) : ℝ :=
  x * F.f (splitR p q θ r) /
    (x * F.f (splitR p q θ r) +
      (1 - x) * F.f (splitL p q θ r))

/-- A tie at one half is counted as wrong for either true state. -/
def Wrong : State → ℝ → Prop
  | .L, b => (1 / 2 : ℝ) ≤ b
  | .R, b => b ≤ (1 / 2 : ℝ)

def MislearnsDeGroot (p q : ℝ) (H : Measure ℝ)
    (θ : State) (r : ℝ) : Prop :=
  Wrong θ (piDeGroot p q H θ r)

/-- In the continuum population, a positive mass of wrong agents. -/
def MislearnsBayes (p q : ℝ) (H : Measure ℝ) (F : SplitLaw)
    (θ : State) (r : ℝ) : Prop :=
  0 < H {x | Wrong θ (piBayes p q F θ r x)}

noncomputable def probDeGroot (p q : ℝ) (H : Measure ℝ)
    (F : SplitLaw) (θ : State) : ℝ≥0∞ :=
  F.law {r | MislearnsDeGroot p q H θ r}

noncomputable def probBayes (p q : ℝ) (H : Measure ℝ)
    (F : SplitLaw) (θ : State) : ℝ≥0∞ :=
  F.law {r | MislearnsBayes p q H F θ r}

/-- Lemma 1's `L`-state cutoff. -/
noncomputable def rTilde (p q : ℝ) : ℝ :=
  (1 - 2 * (1 - q) * (1 - p)) / (2 * q)

/-- Lemma 1's `R`-state cutoff. -/
noncomputable def rTildeR (p q : ℝ) : ℝ :=
  (1 - 2 * (1 - q) * p) / (2 * q)

/-- The threshold chosen in the proof of Theorem 1. -/
noncomputable def qStar (p : ℝ) : ℝ := (2 * p - 1) / (2 * p)

end PostTruth.Regimes


