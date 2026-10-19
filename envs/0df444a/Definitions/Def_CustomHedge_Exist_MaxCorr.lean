-- Prove2me | Definitions.Def_CustomHedge_Exist_MaxCorr
-- name    : CustomHedge_Exist_MaxCorr
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:16:35.161185+00:00
-- url     : https://prove2.me/theorems/a240757f-a419-4032-b861-1c0971f3d96f
-- title:
--   (6), p. 11 — L² norm, claim spaces 𝓗 and ℍ of a sub-σ-algebra, Pearson correlation, maximal correlation of two σ-algebras
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a measure space (a probability space in all uses below) and let $m\subseteq\mathcal F$ be a sub-σ-algebra.
--
--   1. The $L^2$ norm of a real random variable $Z$ is $\|Z\|_2=\big(\mathbb E[Z^2]\big)^{1/2}$.
--   2. The **claim space** $\mathcal H_m$ is the set of real random variables that are $m$-measurable and have finite variance ($Z\in L^2(P)$). With $m=\sigma(X)$ this is the space $\mathcal H_X$ of claims written on $X$.
--   3. The **centered claim space** $\mathbb H_m$ is the subspace of $Z\in\mathcal H_m$ with $\mathbb E[Z]=0$.
--   4. The **Pearson correlation** of $\varphi,\psi$ is
--   $$\rho(\varphi,\psi)=\frac{\mathbb E\big[(\varphi-\mathbb E\varphi)(\psi-\mathbb E\psi)\big]}{\sqrt{\operatorname{Var}\varphi\,\operatorname{Var}\psi}}.$$
--   5. The **maximal correlation** of two sub-σ-algebras $m_1,m_2$ is
--   $$r(m_1,m_2)=\sup\big\{\rho(\varphi,\psi)\;:\;\varphi\in\mathbb H_{m_1},\ \psi\in\mathbb H_{m_2},\ \operatorname{Var}\varphi>0,\ \operatorname{Var}\psi>0\big\}.$$
--   With $m_1=\sigma(X)$ and $m_2=\sigma(I)$ this is the index $r_{XI}$ of display (6) in Guiotto and Roncoroni: the supremum of $\rho(\phi(X),\psi(I))$ over finite-variance, mean-zero functionals of $X$ and of $I$.
--
--   The maximal correlation (Hirschfeld, Gebelein, Rényi) measures the strongest linear dependence that any pair of square-integrable functionals of two random elements can display; it is zero under independence and one under functional dependence.
--
--   **Formalization Note** Measurability for the sub-σ-algebra is strong measurability, which for real-valued functions is ordinary measurability. The Pearson correlation is defined only when both variances are positive, so the supremum ranges over pairs with positive variances; the paper's display (6) leaves this implicit. The supremum is taken in $\mathbb R$ with Lean's convention $\sup\emptyset=0$: when every centered $\varphi$ or every centered $\psi$ has variance zero (for instance when $X$ or $I$ is constant) the index is $0$, consistent with the range $[0,1]$ stated in (6). The set is bounded above by $1$ (Cauchy–Schwarz), so the supremum is never the junk value of an unbounded set.
-- source:
--   Guiotto & Roncoroni, Combined custom hedging: optimal design, noninsurable exposure, and operational risk management, manuscript OPRE-2019-01-058.R3 (Operations Research 2022), p. 7 (PDF 7), §2.2 (spaces 𝓗_#); p. 11 (PDF 11), display (6); p. ec24 (PDF 55), proof of Theorem 1 (space ℍ_X); p. ec15 (PDF 46), Appendix EC.2.1

import Mathlib

namespace CustomHedge.Exist

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The `L²(P)` norm `‖Z‖₂ = (E[Z²])^{1/2}` of a real random variable. -/
noncomputable def l2norm (P : Measure[mΩ] Ω) (Z : Ω → ℝ) : ℝ :=
  Real.sqrt (∫ ω, Z ω ^ 2 ∂P)

/-- `Z ∈ 𝓗_m`: `Z` is `m`-measurable (strongly, i.e. for the sub-σ-algebra `m`) and has finite
variance (`Z ∈ L²(P)`). With `m = σ(X)` this is the claim space `𝓗_X`. -/
def InClaims (P : Measure[mΩ] Ω) (m : MeasurableSpace Ω) (Z : Ω → ℝ) : Prop :=
  StronglyMeasurable[m] Z ∧ MemLp Z 2 P

/-- `Z ∈ ℍ_m`: `Z ∈ 𝓗_m` and `Z` is `P`-centered, `E[Z] = 0`. -/
def InCentered (P : Measure[mΩ] Ω) (m : MeasurableSpace Ω) (Z : Ω → ℝ) : Prop :=
  InClaims P m Z ∧ ∫ ω, Z ω ∂P = 0

/-- Pearson linear correlation
`ρ(φ, ψ) = E[(φ - Eφ)(ψ - Eψ)] / √(Var φ · Var ψ)`. -/
noncomputable def pearsonCorr (P : Measure[mΩ] Ω) (φ ψ : Ω → ℝ) : ℝ :=
  (∫ ω, (φ ω - ∫ ω', φ ω' ∂P) * (ψ ω - ∫ ω', ψ ω' ∂P) ∂P) /
    Real.sqrt (variance φ P * variance ψ P)

/-- Maximal (Hirschfeld–Gebelein–Rényi) correlation of two sub-σ-algebras `m₁, m₂`:
the supremum of the Pearson correlation `ρ(φ, ψ)` over `P`-centered, finite-variance
`φ` (`m₁`-measurable) and `ψ` (`m₂`-measurable) whose correlation is defined, i.e. with
positive variances. (`sSup ∅ = 0`.) -/
noncomputable def maximalCorrelation (P : Measure[mΩ] Ω) (m₁ m₂ : MeasurableSpace Ω) : ℝ :=
  sSup {r : ℝ | ∃ φ ψ : Ω → ℝ, InCentered P m₁ φ ∧ InCentered P m₂ ψ ∧
    0 < variance φ P ∧ 0 < variance ψ P ∧ r = pearsonCorr P φ ψ}

end CustomHedge.Exist


