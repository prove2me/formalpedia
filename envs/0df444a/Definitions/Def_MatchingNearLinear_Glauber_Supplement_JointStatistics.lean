-- Prove2me | Definitions.Def_MatchingNearLinear_Glauber_Supplement_JointStatistics
-- name    : MatchingNearLinear_Glauber_Supplement_JointStatistics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:56:26.219204+00:00
-- url     : https://prove2.me/theorems/e3fe203b-9229-4dd7-909f-c2cc05181d0d
-- title:
--   Joint dimer–monomer indicators and the statistics of Appendix A
-- statement:
--   Let $\mu=\mu_{G,\lambda}$ be the monomer–dimer law with unit monomer weights on a labeled simple graph $G=(V,E)$. For a matching $M$ put $X_e=\mathbf 1\{e\in M\}$ and $J_u=\mathbf 1\{u\text{ unmatched}\}$; $Z=(X,J)$ is indexed by $E\sqcup V$. Write $\mu(e)=\mathbb E_\mu X_e$ and $\mu(u^0)=\mathbb P_\mu(J_u=1)$. For $\theta\in\mathbb R^E$ define
--   $$Y_{uv}=X_{uv}-\lambda_{uv}J_uJ_v,\qquad I=\sum_{uv\in E}\theta_{uv}Y_{uv},\qquad II=\sum_{uv\in E}\lambda_{uv}\theta_{uv}J_uJ_v-\sum_{u\in V}\frac{\sum_{e\sim u}\mu(e)\theta_e}{\mu(u^0)}J_u,$$
--   the forms
--   $$Q_1(\theta)=\sum_{e\in E}\mu(e)\theta_e^2+\sum_{u\in V}\frac{\big(\sum_{e\sim u}\mu(e)\theta_e\big)^2}{\mu(u^0)},\qquad Q_2(\theta)=\sum_{e\in E}\mu(e)\theta_e^2,$$
--   and the constant $\eta(x)=\big(\sqrt{1+3x}+6\sqrt x\big)^2$.
--
--   **Formalization Note** $\mu(u^0)>0$ for every vertex because the empty matching has positive mass, so the divisions are genuine.
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Appendix A, printed pp. 46–47 (PDF pp. 48–49); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_Supplement_StarKernel

set_option autoImplicit false

/-!
# Joint dimer–monomer indicators and the statistics of Appendix A

Miao–Yin, *Sampling Matchings in Near-linear Time*, STOC 2027 submission #444, Appendix A
(printed pp. 46–47, PDF pp. 48–49). For `M ∼ μ = μ_{G,λ}`: `X_e = 1{e ∈ M}`,
`J_u = 1{u unmatched}`, `μ(e) = E X_e`, `μ(u⁰) = P(J_u = 1)`, `Y_{uv} = X_{uv} − λ_{uv} J_u J_v`.
-/

namespace MatchingNearLinear.Glauber.Supplement

open scoped BigOperators
noncomputable section
open Classical

open MatchingNearLinear.Glauber

/-- The joint observable `Z = (X, J)`, indexed by edges then vertices. -/
def jointIndicators {n m : ℕ} (G : Input n m) (M : Config m) : Fin m ⊕ Fin n → ℝ
  | .inl e => indicator M e
  | .inr v => monomer G M v

/-- `μ(e) = E_μ X_e`. -/
def dimerMean {n m : ℕ} (G : Input n m) (lam : Fin m → ℝ) (e : Fin m) : ℝ :=
  observableMean (matchingLaw G lam) (jointIndicators G) (.inl e)

/-- `μ(u⁰) = P_μ(J_u = 1)`. -/
def monomerMean {n m : ℕ} (G : Input n m) (lam : Fin m → ℝ) (u : Fin n) : ℝ :=
  observableMean (matchingLaw G lam) (jointIndicators G) (.inr u)

/-- `Y_{uv} = X_{uv} − λ_{uv} J_u J_v`. -/
def centeredDimer {n m : ℕ} (G : Input n m) (lam : Fin m → ℝ) (e : Fin m) (M : Config m) : ℝ :=
  indicator M e - lam e * monomer G M (G.u e) * monomer G M (G.v e)

/-- `Σ_{e ∼ u} μ(e) θ_e`. -/
def incidentMass {n m : ℕ} (G : Input n m) (lam : Fin m → ℝ) (θ : Fin m → ℝ) (u : Fin n) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e => Incident G e u), dimerMean G lam e * θ e

/-- `I(X) = Σ_{uv ∈ E} θ_{uv} Y_{uv}`. -/
def statI {n m : ℕ} (G : Input n m) (lam : Fin m → ℝ) (θ : Fin m → ℝ) (M : Config m) : ℝ :=
  ∑ e, θ e * centeredDimer G lam e M

/-- `II(X) = Σ_{uv ∈ E} λ_{uv} θ_{uv} J_u J_v − Σ_u (Σ_{e∼u} μ(e) θ_e / μ(u⁰)) J_u`. -/
def statII {n m : ℕ} (G : Input n m) (lam : Fin m → ℝ) (θ : Fin m → ℝ) (M : Config m) : ℝ :=
  (∑ e, lam e * θ e * monomer G M (G.u e) * monomer G M (G.v e)) -
    ∑ u, incidentMass G lam θ u / monomerMean G lam u * monomer G M u

/-- `Σ_e μ(e) θ_e² + Σ_u (Σ_{e∼u} μ(e) θ_e)² / μ(u⁰)`, the right side of (74). -/
def dimerVertexForm {n m : ℕ} (G : Input n m) (lam : Fin m → ℝ) (θ : Fin m → ℝ) : ℝ :=
  (∑ e, dimerMean G lam e * (θ e)^2) + ∑ u, (incidentMass G lam θ u)^2 / monomerMean G lam u

/-- `Σ_e μ(e) θ_e²`, the right side of (75). -/
def dimerForm {n m : ℕ} (G : Input n m) (lam : Fin m → ℝ) (θ : Fin m → ℝ) : ℝ :=
  ∑ e, dimerMean G lam e * (θ e)^2

/-- `η(x) = (√(1 + 3x) + 6√x)²`. -/
def jointConstant (x : ℝ) : ℝ := (Real.sqrt (1 + 3 * x) + 6 * Real.sqrt x)^2

end

end MatchingNearLinear.Glauber.Supplement


