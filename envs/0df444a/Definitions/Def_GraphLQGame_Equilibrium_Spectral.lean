-- Prove2me | Definitions.Def_GraphLQGame_Equilibrium_Spectral
-- name    : GraphLQGame_Equilibrium_Spectral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T12:25:32.670685+00:00
-- url     : https://prove2.me/theorems/5b244a64-91ba-48f5-a52a-24ecd5f8db0d
-- title:
--   The eigenvalue distribution $\mu_G$ (2.8), the class $\mathcal P_{\mathrm{Lap}}$, $Q_\mu$ (3.1), $\mathrm{Var}(\mu)$ (3.4), and solutions of $f' = cQ_\mu'(f)$ on $\mathbb R_+$
-- statement:
--   1. For a graph $G$ on $n$ vertices with Laplacian eigenvalues $\lambda^G_1,\dots,\lambda^G_n$ (with multiplicity), $\mu_G := \frac1n\sum_{i=1}^n\delta_{\lambda_i^G}$ (2.8).
--   2. $\mathcal P_{\mathrm{Lap}}$ is the set of probability measures on $[-2,0]$ with mean $-1$.
--   3. For a measure $\mu$, $Q_\mu(x) := \exp\int_{[-2,0]}\log(1-x\lambda)\,\mu(d\lambda)$ (3.1), and $\mathrm{Var}(\mu):=\int_{[-2,0]}(\lambda+1)^2\,\mu(d\lambda)$ (3.4).
--   4. A function $f$ solves $f'(t)=cQ'(f(t))$ for $t>0$, $f(0)=0$ **on $\mathbb R_+$** if $f$ is continuous and nonnegative on $[0,\infty)$, continuously differentiable on $(0,\infty)$, $f(0)=0$, and $f'(t)=cQ'(f(t))$ for every $t>0$.
--
--   These objects carry the analysis of the ODE in §3, which applies to $Q_G$ through $Q_G=Q_{\mu_G}$.
--
--   **Formalization Note** The eigenvalues are the real roots, with multiplicity, of the characteristic polynomial of $L_G$; when $G$ has no isolated vertices there are $n$ of them (Remark 2.4). Measures live on $\mathbb R$; membership in $\mathcal P_{\mathrm{Lap}}$ says the complement of $[-2,0]$ is null.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), §2.3, p. 7, (2.8); §3, p. 19, (3.1), (3.4), 𝒫_Lap; Proposition 3.2, p. 20

import Mathlib
import Definitions.Def_GraphLQGame_Equilibrium_Graph

open MeasureTheory
open scoped ENNReal

namespace GraphLQGame.Equilibrium

/-- The empirical eigenvalue distribution `μ_G = (1/n) Σ_{i=1}^n δ_{λ_i^G}` of `L_G` (2.8), p. 7,
eigenvalues repeated by multiplicity.

Formalization Note: the eigenvalues are the real roots of the characteristic polynomial of `L_G`,
with multiplicity. When `G` has no isolated vertices, `L_G` has `n` real eigenvalues (Remark 2.4),
so these are all of them. -/
noncomputable def specMeasure {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Measure ℝ :=
  ((n : ℝ≥0∞)⁻¹) • (((lap G).charpoly.roots).map (fun l => Measure.dirac l)).sum

/-- `𝒫_Lap` (§3, p. 19): probability measures on `[−2, 0]` with mean `−1`. -/
def IsPLap (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ (Set.Icc (-2 : ℝ) 0)ᶜ = 0 ∧ ∫ x, x ∂μ = -1

/-- `Q_μ(x) = exp ∫_{[−2,0]} log(1 − xλ) μ(dλ)` (3.1), p. 19. -/
noncomputable def Qmu (μ : Measure ℝ) (x : ℝ) : ℝ :=
  Real.exp (∫ l in Set.Icc (-2 : ℝ) 0, Real.log (1 - x * l) ∂μ)

/-- `Var(μ) = ∫_{[−2,0]} (λ + 1)² μ(dλ)` (3.4), p. 19. -/
noncomputable def VarMu (μ : Measure ℝ) : ℝ :=
  ∫ l in Set.Icc (-2 : ℝ) 0, (l + 1) ^ 2 ∂μ

/-- `f : ℝ₊ → ℝ₊` is a solution in the sense of Proposition 3.2 (p. 20) of
`f'(t) = c Q'(f(t))` for `t > 0`, `f(0) = 0`: `f` is continuous and nonnegative on `ℝ₊`,
continuously differentiable on `(0, ∞)`, `f(0) = 0`, and `f'(t) = c Q'(f(t))` for every `t > 0`
(`Q'` is `deriv Q`).

Formalization Note: only the values of `f` on `ℝ₊ = [0, ∞)` are constrained. -/
def IsODESolRplus (c : ℝ) (Q : ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  f 0 = 0 ∧ ContinuousOn f (Set.Ici 0) ∧ (∀ t, 0 ≤ t → 0 ≤ f t) ∧
    ContDiffOn ℝ 1 f (Set.Ioi 0) ∧ ∀ t, 0 < t → HasDerivAt f (c * deriv Q (f t)) t

end GraphLQGame.Equilibrium


