-- Prove2me | Definitions.Def_OnlineDiscUniv_optDisc
-- name    : OnlineDiscUniv_optDisc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:49.389107+00:00
-- url     : https://prove2.me/theorems/b7ae0903-6349-4849-beea-c659273589e7
-- title:
--   Expected discrepancy, failure and success probabilities, and the optimal online values $\inf_\varepsilon\mathbb E_\mu D_{M,N}$ and $\sup_\varepsilon\mathbb P_\mu(D_{M,N}\le\kappa)$
-- statement:
--   For an online algorithm $A$ with seed law $\rho$ and entry law $\mu$, the seed and the input are independent, so the joint law is $\rho\otimes\mu^{\otimes MN}$. The module defines
--   $$
--   \mathbb E_\mu D_{M,N},\qquad\mathbb P_\mu(D_{M,N}>\kappa),\qquad\mathbb E_\mu(D_{M,N}-\kappa)_+,\qquad\mathbb P_\mu(D_{M,N}\le\kappa),
--   $$
--   all including the seed, and the optimal values
--   $$
--   \inf_{\varepsilon\text{ online}}\mathbb E_\mu D_{M,N},\qquad\sup_{\varepsilon\text{ online}}\mathbb P_\mu(D_{M,N}\le\kappa).
--   $$
--
--   **Formalization Note** Expectations are lower integrals in $[0,\infty]$. The paper does not fix the seed space: the infimum and supremum range over every seed space (a type with a $\sigma$-algebra), every probability law of the seed and every measurable causal online algorithm for that seed space; deterministic algorithms are the one-point seed spaces.
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), §2.1, p.5 (PDF p.6); Theorem 1.1, pp.1–2 (PDF pp.2–3); (5.5), p.24 (PDF p.25)

import Mathlib
import Definitions.Def_OnlineDiscUniv_OnlineAlg

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace OnlineDiscUniv

variable {S : Type*} [MeasurableSpace S] {M N : ℕ}

/-- The expected discrepancy `E_μ D_{M,N}` of an online algorithm with seed law `ρ` (Jo–Lee,
arXiv:2610.00103, artifact sha256 cb190f12…, §2.1, printed p.5, PDF p.6). The seed is independent
of the input, so the joint law is the product `ρ ⊗ inputLaw μ M N`.

**Formalization Note** A lower integral in `ℝ≥0∞` (never the junk `0` of a non-integrable
Bochner integral). -/
noncomputable def expDisc (μ : Measure ℝ) (ρ : Measure S) (A : OnlineAlg S M N) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (disc A p.1 p.2) ∂(ρ.prod (inputLaw μ M N))

/-- The failure probability `P_μ(D_{M,N} > κ)` (Jo–Lee, arXiv:2610.00103, Theorem 1.1(i), p.1,
PDF p.2), including the seed. -/
noncomputable def failProb (μ : Measure ℝ) (ρ : Measure S) (A : OnlineAlg S M N) (κ : ℝ) :
    ℝ≥0∞ :=
  (ρ.prod (inputLaw μ M N)) {p | κ < disc A p.1 p.2}

/-- The expected excess `E_μ(D_{M,N} − κ)_+` (Jo–Lee, arXiv:2610.00103, Theorem 1.1(i), p.1,
PDF p.2), a lower integral in `ℝ≥0∞` (`ofReal` of a negative number is `0`, the positive
part). -/
noncomputable def expExcess (μ : Measure ℝ) (ρ : Measure S) (A : OnlineAlg S M N) (κ : ℝ) :
    ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (disc A p.1 p.2 - κ) ∂(ρ.prod (inputLaw μ M N))

/-- The success probability `P_μ(D_{M,N} ≤ κ)` (Jo–Lee, arXiv:2610.00103, Theorem 1.1(ii),
p.2, PDF p.3), including the seed. -/
noncomputable def succProb (μ : Measure ℝ) (ρ : Measure S) (A : OnlineAlg S M N) (κ : ℝ) :
    ℝ≥0∞ :=
  (ρ.prod (inputLaw μ M N)) {p | disc A p.1 p.2 ≤ κ}

/-- The optimal expected discrepancy `inf_{ε online} E_μ D_{M,N}` (Jo–Lee, arXiv:2610.00103,
(2.1), p.5, PDF p.6; Theorem 1.1, p.1, PDF p.2).

**Formalization Note** The paper does not fix the seed space. The infimum ranges over every seed
space `S : Type` with a σ-algebra, every probability law `ρ` of the seed, and every (jointly
measurable, causal) online algorithm with seed space `S`. Deterministic algorithms are included
(a one-point seed space). -/
noncomputable def optDisc (μ : Measure ℝ) (M N : ℕ) : ℝ≥0∞ :=
  ⨅ (S : Type) (_ : MeasurableSpace S) (ρ : Measure S) (_ : IsProbabilityMeasure ρ)
    (A : OnlineAlg S M N), expDisc μ ρ A

/-- The supremal success probability `sup_{ε online} P_μ(D_{M,N} ≤ κ)` (Jo–Lee,
arXiv:2610.00103, Theorem 1.1(ii), p.2, PDF p.3; (5.5), p.24, PDF p.25), over the same class of
randomized online algorithms as `optDisc`. -/
noncomputable def optSucc (μ : Measure ℝ) (M N : ℕ) (κ : ℝ) : ℝ≥0∞ :=
  ⨆ (S : Type) (_ : MeasurableSpace S) (ρ : Measure S) (_ : IsProbabilityMeasure ρ)
    (A : OnlineAlg S M N), succProb μ ρ A κ

end OnlineDiscUniv


