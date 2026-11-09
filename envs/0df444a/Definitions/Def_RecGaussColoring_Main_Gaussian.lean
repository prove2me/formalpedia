-- Prove2me | Definitions.Def_RecGaussColoring_Main_Gaussian
-- name    : RecGaussColoring_Main_Gaussian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:23:32.386568+00:00
-- url     : https://prove2.me/theorems/ef7a62c6-81f8-4fb5-8fb3-de741693136e
-- title:
--   Gaussian probabilities, quantiles and finite covers
-- statement:
--   Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. Write $\Phi(t)=\Pr[Z\le t]$ for $Z\sim N(0,1)$, $\Phi^c=1-\Phi$, and $\phi(t)=e^{-t^2/2}/\sqrt{2\pi}$. The real quantile is $\inf\{t:p\le\Phi(t)\}$ on $0<p<1$; the extended quantile is $-\infty$ at $p\le0$ and $+\infty$ at $p\ge1$. For a finite family $X$, define
--   $$
--   X\text{ is an }(s,\delta)\text{-cover}\quad\Longleftrightarrow\quad
--   \Pr_{\gamma_d}[\exists x\in X:\langle\gamma,x\rangle\ge s]\ge\delta.
--   $$
--   Projection off a unit direction $z$ means $x-\langle x,z\rangle z$. Gaussian-maximum upper events use $>t$ and lower events use $\le t-L$. The lower-tail bound explicitly returns $1$ when the upper-event probability is zero. Minkowski combinations are sets of vectors $\theta a+(1-\theta)b$.
--
--   The CDF and both quantiles are imported from the published `Cohen2019_Robust_Phi`; this module supplies their complementary tail and the cover, projection, maximum-event and Minkowski-set constructions used by the analytic milestones. **Formalization Note** Gaussian probabilities are the real values of Mathlib's standard Gaussian measure; no integrals are used. The real quantile's value outside $(0,1)$ is zero and is never used in a nontrivial bound there.
-- source:
--   Ijay Narang, Yukai Tang, STOC 2027 submission #295 (October 2026), Notation; Definition 1.2, p. 4; Lemma 2.4, p. 8, p. 2. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/295.pdf

import Definitions.Def_Cohen2019_Robust_Phi

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open Cohen2019.Robust
open scoped Topology
noncomputable section

namespace RecGaussColoring.Main

/-- CDF and quantiles are imported from the published Cohen2019_Robust_Phi. -/
def PhiTail (t : ℝ) : ℝ := 1 - Phi t

def phi (t : ℝ) : ℝ := Real.exp (-t^2 / 2) / Real.sqrt (2 * Real.pi)

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def gaussProb {d : ℕ} (A : Set (Space d)) : ℝ := (stdGaussian (Space d)).real A

/-- Definition 1.2; the event includes equality at the threshold. -/
def IsCover {d : ℕ} (X : Finset (Space d)) (s δ : ℝ) : Prop :=
  δ ≤ gaussProb {g | ∃ x ∈ X, s ≤ ⟪g, x⟫}

def projectOff {d : ℕ} (z x : Space d) : Space d := x - ⟪x, z⟫ • z

/-- Avoid an empty-family maximum: the lower-tail event is a finite intersection. -/
def maxLowerEvent {d N : ℕ} (Y : Fin N → Space d) (s : ℝ) : Set (Space d) :=
  {g | ∀ r, ⟪g, Y r⟫ ≤ s}

def maxUpperProb {d N : ℕ} (Y : Fin N → Space d) (t : ℝ) : ℝ :=
  gaussProb {g | ∃ r, t < ⟪g, Y r⟫}

/-- Lemma 2.4's RHS, including its explicit p=0 case (source proof p. 8). -/
def lowerTailBound (p δ t T L : ℝ) : ℝ :=
  if p = 0 then 1 else
    Phi ((1 + L / (T - t)) * PhiInvReal (1-p) -
      L / (T-t) * PhiInvReal (1-δ))

/-- Minkowski combination, defined pointwise even at θ=0 or θ=1. -/
def minkowskiMix {d : ℕ} (θ : ℝ) (A B : Set (Space d)) : Set (Space d) :=
  {z | ∃ a ∈ A, ∃ b ∈ B, z = θ • a + (1-θ) • b}

end RecGaussColoring.Main


