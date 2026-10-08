-- Prove2me | Definitions.Def_MinimaxWass_Lipschitz_Setting
-- name    : MinimaxWass_Lipschitz_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T20:09:06.119809+00:00
-- url     : https://prove2.me/theorems/2d0b7cd0-984d-4a72-9f6f-0b12389e03c5
-- title:
--   §2, §3.2, App. C.3/C.5, pp. 3, 6, 15–17 — local minimax risk R*_{ϱ,p}, empirical measure P_n, Λ = [0, Lϱ^{−(p−1)}], Φ = {φ_{λ,f}}, Rademacher average ℜ_n(Φ)
-- statement:
--   This file adds, on top of the shared objects of `MinimaxWass.DataDep.Setting`, the quantities in which Theorem 2 of Lee and Raginsky and the steps of its proof (Appendix C.3 and C.5) are stated. Throughout, $\mathcal Z$ is a metric space with metric $d_{\mathcal Z}$ and its Borel $\sigma$-algebra, $p \ge 1$, and $\varrho > 0$ is the Wasserstein radius. From the imported file it uses the risk $R(Q,f)=\int f\,dQ$, the local worst-case risk $R_{\varrho,p}(P,f)=\sup_{Q\in B^W_{\varrho,p}(P)}R(Q,f)$ over the published $p$-Wasserstein ball, and the dual integrand $\varphi_{\lambda,f}(z)=\sup_{z'\in\mathcal Z}\{f(z')-\lambda d^p_{\mathcal Z}(z,z')\}$ of (8).
--
--   1. **Local minimax risk.** For a class $\mathcal F$ of functions $\mathcal Z\to\mathbb R$, $$R^*_{\varrho,p}(P,\mathcal F) := \inf_{f \in \mathcal F} R_{\varrho,p}(P,f).$$
--   2. **Empirical distribution.** For a sample $\omega = (Z_1,\dots,Z_n)$ with $n \ge 1$, $P_n := \frac1n\sum_{i=1}^n \delta_{Z_i}$; this is the shared empirical law of `MinimaxWass.DataDep.Setting`.
--   3. **Dual multipliers.** For a Lipschitz constant $L$, $\Lambda := [0, L\varrho^{-(p-1)}]$, the interval of Lemma 1 and Remark 3.
--   4. **The class $\Phi$.** $\Phi := \{\varphi_{\lambda,f} : \lambda \in \Lambda,\ f \in \mathcal F\}$.
--   5. **Expected Rademacher average.** For a class $\Phi$ of functions, $Z_1,\dots,Z_n$ i.i.d. from $P$ and independent uniform signs $\varepsilon_i \in \{\pm1\}$ independent of the sample, $$\mathfrak R_n(\Phi) := \mathbf E\Big[\sup_{\varphi \in \Phi} \frac1n \sum_{i=1}^n \varepsilon_i \varphi(Z_i)\Big].$$
--
--   The class $\Phi$ with $\Lambda$ from Lemma 1 is the one whose Rademacher average Appendix C.3 bounds by $\frac{24}{\sqrt n}\mathfrak C(\mathcal F)+\frac{24L C_0\,\mathrm{diam}(\mathcal Z)^p}{\sqrt n\,\varrho^{p-1}}$.
--
--   **Formalization Note** The infimum in $R^*_{\varrho,p}$ and the supremum in $\mathfrak R_n$ are real-valued; the theorems that use them assume a bounded $\mathcal Z$, $0 \le f \le M$ and a named member of $\mathcal F$, so each is over a nonempty set bounded on the relevant side. $R^*_{\varrho,p}$ has the same body as the version in `MinimaxWass.DataDep.Setting`, which additionally takes a proof that $\mathcal F$ is nonempty. The expectation over the signs is the average over the $2^n$ sign vectors, inside the Bochner integral over the product law $P^{\otimes n}$; the theorems that use $\mathfrak R_n$ assume a finite entropy integral, which makes the class separable in the uniform norm and the integrand measurable.
-- source:
--   Lee & Raginsky, Minimax statistical learning with Wasserstein distances, arXiv:1705.07815v2, p. 1 (R(P,f), P_n), p. 3 (ball, R_{ϱ,p}, R*_{ϱ,p}), p. 4 (8), p. 5 (Assumptions 1–2, 𝔆(ℱ)), p. 6 (Remark 3, Λ), Appendix C.3 p. 15 and C.5 pp. 16–17 (Φ, ℜ_n(Φ))

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinBall
import Definitions.Def_MinimaxWass_DataDep_Setting

open MeasureTheory WassersteinLinOpt.Ball
open scoped ENNReal NNReal

namespace MinimaxWass.Lipschitz

variable {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵]

/-- The local minimax risk `R*_{ϱ,p}(P, ℱ) := inf_{f ∈ ℱ} R_{ϱ,p}(P, f)` (§2, p. 3), with
`R_{ϱ,p}` the shared `MinimaxWass.DataDep.localRisk`.  Same body as
`MinimaxWass.DataDep.localMinimaxRisk`, without that version's (unused) nonemptiness argument;
the theorems that use it name a member of `ℱ` (an ERM output or a minimizer), so the
infimum is never over an empty class. -/
noncomputable def localMinimaxRisk (p ϱ : ℝ) (P : ProbabilityMeasure 𝒵) (ℱ : Set (𝒵 → ℝ)) : ℝ :=
  ⨅ f : ℱ, MinimaxWass.DataDep.localRisk p ϱ P (f : 𝒵 → ℝ)

/-- The empirical distribution `P_n := (1/n) Σ_{i=1}^n δ_{Z_i}` of a sample `ω = (Z_1, …, Z_n)`
(§1, p. 1), as a probability measure (`0 < n`): the shared `MinimaxWass.DataDep.empiricalPM`. -/
noncomputable def empiricalPM {n : ℕ} (hn : 0 < n) (ω : Fin n → 𝒵) : ProbabilityMeasure 𝒵 :=
  MinimaxWass.DataDep.empiricalPM hn ω

/-- The interval `Λ := [0, L ϱ^{−(p−1)}]` of dual multipliers allowed by Lemma 1 (p. 6; Remark 3,
p. 6; Appendix C.3, p. 15). -/
def lamIntervalL (p ϱ L : ℝ) : Set ℝ :=
  Set.Icc 0 (L * ϱ ^ (-(p - 1)))

/-- The function class `Φ := {φ_{λ,f} : λ ∈ Λ, f ∈ ℱ}` (Appendix C.5, p. 16, with `Λ` of
Lemma 1 as Appendix C.3 directs). -/
def phiClass (p ϱ L : ℝ) (ℱ : Set (𝒵 → ℝ)) : Set (𝒵 → ℝ) :=
  {g | ∃ lam ∈ lamIntervalL p ϱ L, ∃ f ∈ ℱ, g = MinimaxWass.DataDep.phi p lam f}

/-- The expected Rademacher average `ℜ_n(Φ) := E[sup_{φ ∈ Φ} (1/n) Σ_i ε_i φ(Z_i)]`
(Appendix C.5, p. 17), with `Z_1, …, Z_n` i.i.d. `P` and independent uniform signs `ε_i`;
the expectation over the signs is the average over the `2^n` sign vectors. -/
noncomputable def rademacherAvg (P : ProbabilityMeasure 𝒵) (n : ℕ) (Φ : Set (𝒵 → ℝ)) : ℝ :=
  ∫ ω, (1 / (2 : ℝ) ^ n) * ∑ ε : Fin n → Bool,
      (⨆ g : Φ, (1 / (n : ℝ)) * ∑ i, (if ε i then (1 : ℝ) else -1) * (g : 𝒵 → ℝ) (ω i))
    ∂(Measure.pi (fun _ : Fin n => (P : Measure 𝒵)))

end MinimaxWass.Lipschitz


