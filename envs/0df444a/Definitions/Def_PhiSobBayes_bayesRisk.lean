-- Prove2me | Definitions.Def_PhiSobBayes_bayesRisk
-- name    : PhiSobBayes_bayesRisk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:07:03.515218+00:00
-- url     : https://prove2.me/theorems/2e002b1a-c5c9-4c4c-a389-af427ad2eb10
-- title:
--   $\Phi$-Bayes risk $R_\Phi(t,f)$
-- statement:
--   Let $\mu$ be a prior on $\mathbb R^n$, $J$ an open interval, $\Phi:J\to\mathbb R$, $t>0$ and $f:\mathbb R^n\to J$. The **$\Phi$-optimal risk** (or $\Phi$-Bayes risk) of estimating $f(X)$ from $Y_t$ is
--   $$R_\Phi(t,f)=\inf_h\ \mathbb E\,B_\Phi\big(f(X),h(Y_t)\big),$$
--   the infimum over all measurable estimators $h:\mathbb R^n\to J$, with $(X,Y_t)\sim P_t$.
--
--   The constant estimator $h\equiv\mathbb E_\mu f$ has risk $\mathrm{Ent}^\Phi_\mu(f)$ (the $\Phi$-trivial risk), so $R_\Phi(t,f)\le\mathrm{Ent}^\Phi_\mu(f)$. The goal theorem compares $R_\Phi$ with this trivial risk.
--
--   **Formalization Note** The expectation is a lower Lebesgue integral in $[0,\infty]$ of $B_\Phi(f(x),h(y))$, which is nonnegative on $J\times J$ for convex $\Phi$. A real-valued Bochner integral would give the value $0$ to an estimator of infinite risk. Estimators are Borel measurable and take all their values in $J$.
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Definition 5, p.14 (PDF 14)

import Mathlib
import Definitions.Def_PhiSobBayes_bregman
import Definitions.Def_PhiSobBayes_gamJoint

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace PhiSobBayes

/-- The **Φ-optimal risk** (Φ-Bayes risk) of estimating `f(X)` from `Y_t`:
`R_Φ(t, f) = inf_h 𝔼 B_Φ(f(X), h(Y_t))`, the infimum over measurable `J`-valued estimators `h`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Definition 5, p.14 (PDF 14): "the infimum is over all measurable estimators ℎ : ℝ𝑛 → 𝐽
based on 𝑌𝑡".

**Formalization Note** The expectation is under the planted model `gamJoint μ t` and is a lower
Lebesgue integral in `[0, ∞]` of `B_Φ(f(x), h(y))`, which is `≥ 0` on `J × J` for convex `Φ`
(`ENNReal.ofReal` only clips values outside that case). A Bochner integral would give the junk
value `0` for an estimator with infinite risk. Estimators are Borel measurable and take every value
in `J`. -/
noncomputable def bayesRisk {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (J : Set ℝ)
    (Φ : ℝ → ℝ) (t : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ≥0∞ :=
  ⨅ (h : EuclideanSpace ℝ (Fin n) → ℝ) (_ : Measurable h) (_ : ∀ y, h y ∈ J),
    ∫⁻ p, ENNReal.ofReal (bregman Φ (f p.1) (h p.2)) ∂(gamJoint μ t)

end PhiSobBayes


