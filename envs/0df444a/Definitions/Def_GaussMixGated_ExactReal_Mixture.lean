-- Prove2me | Definitions.Def_GaussMixGated_ExactReal_Mixture
-- name    : GaussMixGated_ExactReal_Mixture
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:24:11.028201+00:00
-- url     : https://prove2.me/theorems/9fc46fb4-9876-445b-85a5-3cbbae7b518b
-- title:
--   Gaussian location mixtures, covered submixtures, the reference mixture $Q$ and the fitted law $q$
-- statement:
--   Let $\nu=\sum_{i<s}w_i\delta_{\mu_i}$ with $s\le k$, $w_i>0$, $\sum_i w_i=1$ and $\mu_i\in\mathbb R^d$; the means may coincide. For $\sigma>0$ the mixture
--
--   $$\nu*N(0,\sigma^2I_d)=\sum_{i<s}w_i\,N(\mu_i,\sigma^2I_d)$$
--
--   is formed from the standard Gaussian of $\mathbb R^d$ pushed forward by $g\mapsto\mu_i+\sigma g$. With $\sigma=1$ it is the target $P$ of (1); for $\sigma\ge1$ it is $P_\sigma$ of §2.
--
--   Given centers $c_1,\dots,c_m$ and a radius $r$, atom $i$ is **covered** if $\|\mu_i-c_j\|\le r$ for some $j$. The **covered mass** is $\sum_{i\text{ covered}}w_i$ and the **normalized covered submixture** is
--
--   $$F=\Big(\sum_{i\text{ covered}}w_i\Big)^{-1}\sum_{i\text{ covered}}w_i\,N(\mu_i,\sigma^2I_d).$$
--
--   The **omitted mass** at radius $R$ is the $\nu$-mass of atoms farther than $R$ from every center. The reference mixture is $Q=\frac1m\sum_jN(c_j,\sigma^2I_d)$, the contaminated law is $P'=(1-b)F+bH$, and for a positive numerator $f$ the fitted law is $q=Qf/Z$ with $Z=\mathbb E_Qf$.
--
--   These are the objects of (1), §2 and Theorems 2.1–2.3.
-- source:
--   Zheng, Xie, He, Learning Finite Gaussian Location Mixtures via Gated Moments and Posterior Covers, STOC 2027 submission #36 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/36.pdf, PDF p. 3, (1); PDF p. 5, §2 preamble; PDF p. 6, Theorems 2.1–2.3

import Mathlib

open MeasureTheory ProbabilityTheory

noncomputable section

namespace GaussMixGated.ExactReal

/-!
# Gaussian location mixtures (Zheng–Xie–He, STOC 2027 #36, (1) on PDF p. 3; §2 preamble, PDF p. 5;
Theorems 2.1–2.3, PDF p. 6)

A latent measure `ν = ∑_{i<s} w_i δ_{μ_i}` is given by `s`, weights `w : Fin s → ℝ` and means
`μ : Fin s → ℝ^d`; the means may coincide. `ν ∗ N(0, σ² I_d)` is the weighted sum of the laws
`N(μ_i, σ² I_d)`.
-/

/-- `N(c, σ² I_d)`: the image of the standard Gaussian of `ℝ^d` under `g ↦ c + σ g`. -/
def gaussLaw (d : ℕ) (σ : ℝ) (c : EuclideanSpace ℝ (Fin d)) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  (stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun g => c + σ • g)

/-- `ν ∗ N(0, σ² I_d) = ∑_i w_i N(μ_i, σ² I_d)` for `ν = ∑_i w_i δ_{μ_i}`. With `σ = 1` this is
the target `P` of (1); for `σ ≥ 1` it is `P_σ` of §2. -/
def mixtureLaw (d s : ℕ) (σ : ℝ) (w : Fin s → ℝ) (μ : Fin s → EuclideanSpace ℝ (Fin d)) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  ∑ i, ENNReal.ofReal (w i) • gaussLaw d σ (μ i)

/-- `ν = ∑_i w_i δ_{μ_i}` is a mixing measure with at most `k` atoms: `s ≤ k`, positive weights
summing to one. -/
def IsMixingMeasure (k s : ℕ) (w : Fin s → ℝ) : Prop :=
  s ≤ k ∧ (∀ i, 0 < w i) ∧ ∑ i, w i = 1

/-- Atom `i` is covered by the centers `c_1, …, c_m` within radius `r`. -/
def IsCovered {d s m : ℕ} (μ : Fin s → EuclideanSpace ℝ (Fin d))
    (c : Fin m → EuclideanSpace ℝ (Fin d)) (r : ℝ) (i : Fin s) : Prop :=
  ∃ j, dist (μ i) (c j) ≤ r

/-- The latent (`ν`-)mass of the covered atoms. -/
def coveredMass {d s m : ℕ} (w : Fin s → ℝ) (μ : Fin s → EuclideanSpace ℝ (Fin d))
    (c : Fin m → EuclideanSpace ℝ (Fin d)) (r : ℝ) : ℝ :=
  open Classical in ∑ i with IsCovered μ c r i, w i

/-- The normalized submixture of all covered atoms (Theorem 2.1):
`F = (∑_{i covered} w_i)⁻¹ ∑_{i covered} w_i N(μ_i, σ² I_d)`. -/
def coveredSubmixture {d s m : ℕ} (σ : ℝ) (w : Fin s → ℝ) (μ : Fin s → EuclideanSpace ℝ (Fin d))
    (c : Fin m → EuclideanSpace ℝ (Fin d)) (r : ℝ) : Measure (EuclideanSpace ℝ (Fin d)) :=
  open Classical in
  (ENNReal.ofReal (coveredMass w μ c r))⁻¹ •
    ∑ i with IsCovered μ c r i, ENNReal.ofReal (w i) • gaussLaw d σ (μ i)

/-- The latent mass of the atoms at distance more than `R` from every center
(the mass omitted by the radius-`R` balls around the centers). -/
def omittedMass {d s m : ℕ} (w : Fin s → ℝ) (μ : Fin s → EuclideanSpace ℝ (Fin d))
    (c : Fin m → EuclideanSpace ℝ (Fin d)) (R : ℝ) : ℝ :=
  open Classical in ∑ i with ∀ j, R < dist (μ i) (c j), w i

/-- The reference mixture `Q = (1/m) ∑_j N(c_j, σ² I_d)` of Theorem 2.1. -/
def centerMixture {d m : ℕ} (σ : ℝ) (c : Fin m → EuclideanSpace ℝ (Fin d)) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  ∑ j, (m : ENNReal)⁻¹ • gaussLaw d σ (c j)

/-- The contaminated observation law `P′ = (1 − b) F + b H`. -/
def contaminated {α : Type*} [MeasurableSpace α] (b : ℝ) (F H : Measure α) : Measure α :=
  ENNReal.ofReal (1 - b) • F + ENNReal.ofReal b • H

/-- The fitted law `q = Q f / Z`, `Z = E_Q f`, of Theorem 2.2. -/
def fittedLaw {α : Type*} [MeasurableSpace α] (Q : Measure α) (f : α → ℝ) : Measure α :=
  (ENNReal.ofReal (∫ x, f x ∂Q))⁻¹ • Q.withDensity (fun x => ENNReal.ofReal (f x))

end GaussMixGated.ExactReal


