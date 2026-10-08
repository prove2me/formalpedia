-- Prove2me | Definitions.Def_MinimaxWass_Smooth_Setting
-- name    : MinimaxWass_Smooth_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:11:43.013876+00:00
-- url     : https://prove2.me/theorems/e10eefc1-1fd0-4150-8f58-1f8f9e38c126
-- title:
--   §3, App. C.5 — dual objective, empirical measure and sample law, multiplier interval Λ, and dual class Φ
-- statement:
--   This file defines the dual objective, empirical measure and sample law, multiplier interval Λ, and dual class Φ used in Lee and Raginsky’s excess-risk bound under a single smooth hypothesis (§3.3 and Appendix C.5). The risk, envelope, entropy integral, and Rademacher average below come from the shared `MinimaxWass.DataDep.Setting` and `MinimaxWass.Lipschitz.Setting` definitions.
--
--   Let $\mathcal Z$ be a metric space with metric $d_{\mathcal Z}$ and its Borel $\sigma$-algebra, let $p\ge 1$ and $\varrho>0$, and let $B^W_{\varrho,p}(P)=\{Q: W_p(Q,P)\le\varrho\}$ be the $p$-Wasserstein ball around a Borel probability measure $P$ (the published definition `WassersteinLinOpt.Ball.wassersteinBall`). For a hypothesis $f:\mathcal Z\to\mathbb R$ and a class $\mathcal F$ of hypotheses:
--
--   1. **Risk.** $R(Q,f)=\mathbf E_Q[f(Z)]=\int_{\mathcal Z} f\,dQ$.
--   2. **Local worst-case risk.** $R_{\varrho,p}(P,f)=\sup_{Q\in B^W_{\varrho,p}(P)} R(Q,f)$.
--   3. **Local minimax risk.** $R^*_{\varrho,p}(P,\mathcal F)=\inf_{f\in\mathcal F}R_{\varrho,p}(P,f)$.
--   4. **Dual function and dual objective.** For $\lambda\in\mathbb R$,
--   $$\varphi_{\lambda,f}(z)=\sup_{z'\in\mathcal Z}\bigl\{f(z')-\lambda\, d_{\mathcal Z}^p(z,z')\bigr\},\qquad \lambda\varrho^p+\mathbf E_Q[\varphi_{\lambda,f}(Z)].$$
--   5. **Sample and empirical measure.** A sample $Z_1,\dots,Z_n$ is a point $\omega\in\mathcal Z^n$; its law is the product measure $P^{\otimes n}$, and for $n>0$ the empirical distribution is $P_n=\frac1n\sum_{i=1}^n\delta_{Z_i}$.
--   6. **Covering number and entropy integral.** $\mathcal N(\mathcal F,\|\cdot\|_\infty,u)$ is the least cardinality of a finite $S\subseteq\mathcal F$ such that every $f\in\mathcal F$ has some $g\in S$ with $\sup_z|f(z)-g(z)|\le u$ (and $\infty$ if there is none), and
--   $$\mathfrak C(\mathcal F)=\int_0^\infty\sqrt{\log\mathcal N(\mathcal F,\|\cdot\|_\infty,u)}\,du\in[0,\infty].$$
--   7. **The multiplier interval and the dual class** (Appendix C.5): $\Lambda=[0,\,C_0 2^{p-1}(1+(\mathrm{diam}(\mathcal Z)/\varrho)^p)]$ and $\Phi=\{\varphi_{\lambda,f}:\lambda\in\Lambda,\ f\in\mathcal F\}$.
--   8. **Expected Rademacher average.**
--   $$\mathfrak R_n(\Phi)=\mathbf E\Bigl[\sup_{\varphi\in\Phi}\frac1n\sum_{i=1}^n\varepsilon_i\varphi(Z_i)\Bigr],$$
--   with $Z_1,\dots,Z_n$ i.i.d. $P$ and independent i.i.d. Rademacher signs $\varepsilon_i$.
--
--   These are the quantities in which Theorem 3 of the paper and its proof are stated.
--
--   **Formalization Note** The paper's ball is $\{Q\in\mathcal P_p(\mathcal Z):W_p(P,Q)\le\varrho\}$; the published ball ranges over all Borel probability measures, which is the same set because a measure at finite $W_p$-distance from $P\in\mathcal P_p$ has a finite $p$-th moment (and on a bounded space every measure does). Suprema and infima are real-valued; they are used only for classes uniformly bounded in $[0,M]$, where the ball (it contains $P$) and the classes are nonempty and the values bounded. The covering number is the internal one (centres in $\mathcal F$), the larger of the two conventions; the integrand is $+\infty$ where the covering number is infinite. The expectation over the Rademacher signs is the uniform average over $\{\pm1\}^n$, and the outer expectation is over $P^{\otimes n}$. $\mathrm{diam}(\mathcal Z)$ is the metric diameter, which is meaningful under Assumption 1 (bounded $\mathcal Z$), carried by every theorem that uses it.
-- source:
--   Lee & Raginsky, Minimax statistical learning with Wasserstein distances, arXiv:1705.07815v2, p. 1 (R(P,f), P_n), p. 2 Definition 1, p. 3 (ball, R_{ϱ,p}, R*_{ϱ,p}), p. 4 (8) (φ_{λ,f}), p. 5 (𝔆(ℱ)), pp. 16–17 Appendix C.5 (Λ, Φ, ℜ_n(Φ))

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinBall
import Definitions.Def_MinimaxWass_DataDep_Setting
import Definitions.Def_MinimaxWass_Lipschitz_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace MinimaxWass.Smooth

open WassersteinLinOpt.Ball

variable {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵]

/-- The dual objective of (8): `λ ϱ^p + E_Q[φ_{λ,f}(Z)]`. -/
noncomputable def dualObjective (p ϱ : ℝ) (Q : ProbabilityMeasure 𝒵) (f : 𝒵 → ℝ) (lam : ℝ) : ℝ :=
  lam * ϱ ^ p + ∫ z, MinimaxWass.DataDep.phi p lam f z ∂(Q : Measure 𝒵)

/-- The empirical measure `P_n = (1/n) ∑_{i=1}^n δ_{Z_i}` of a sample `ω = (Z_1, …, Z_n)`, as a
measure. -/
noncomputable def empiricalMeasure {n : ℕ} (ω : Fin n → 𝒵) : Measure 𝒵 :=
  (n : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (ω i)

omit [MetricSpace 𝒵] in
theorem empiricalMeasure_univ {n : ℕ} (hn : 0 < n) (ω : Fin n → 𝒵) :
    empiricalMeasure ω Set.univ = 1 := by
  have hn' : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  simp [empiricalMeasure, ENNReal.inv_mul_cancel hn' (ENNReal.natCast_ne_top n)]

/-- The empirical distribution `P_n` of a sample of size `n > 0`, as a probability measure. -/
noncomputable def empiricalPM {n : ℕ} (hn : 0 < n) (ω : Fin n → 𝒵) : ProbabilityMeasure 𝒵 :=
  ⟨empiricalMeasure ω, ⟨empiricalMeasure_univ hn ω⟩⟩

/-- The law of an i.i.d. sample `Z_1, …, Z_n ∼ P`: the product measure `P^{⊗ n}` on `Fin n → 𝒵`. -/
noncomputable def sampleLaw (P : ProbabilityMeasure 𝒵) (n : ℕ) : Measure (Fin n → 𝒵) :=
  Measure.pi (fun _ : Fin n => (P : Measure 𝒵))

variable (𝒵) in
/-- The multiplier interval `Λ = [0, C₀ 2^{p−1} (1 + (diam(𝒵)/ϱ)^p)]` of Appendix C.5 (p. 16). -/
noncomputable def lamInterval (p ϱ C₀ : ℝ) : Set ℝ :=
  Set.Icc 0 (C₀ * 2 ^ (p - 1) * (1 + (Metric.diam (Set.univ : Set 𝒵) / ϱ) ^ p))

/-- The class `Φ = {φ_{λ,f} : λ ∈ Λ, f ∈ ℱ}` of Appendix C.5 (p. 16). -/
def phiClass (p : ℝ) (Λ : Set ℝ) (ℱ : Set (𝒵 → ℝ)) : Set (𝒵 → ℝ) :=
  {g | ∃ lam ∈ Λ, ∃ f ∈ ℱ, g = MinimaxWass.DataDep.phi p lam f}

end MinimaxWass.Smooth


