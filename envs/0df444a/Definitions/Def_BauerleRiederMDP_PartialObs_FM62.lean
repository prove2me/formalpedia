-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_FM62
-- name    : BauerleRiederMDP_PartialObs_FM62
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:14.992599+00:00
-- url     : https://prove2.me/theorems/25f565f1-9e3a-4d28-95c7-48cbc5aaa510
-- title:
--   Assumption (FM) (i)–(iii) of Section 6.2
-- statement:
--   Assumption (FM) of Section 6.2 (dynamic mean–variance problem) consists of:
--
--   1. $\sup_y\mathbb E\|R(y)\|^2<\infty$;
--   2. there is a $k\in\{1,\dots,d\}$ with $\mathbb E R_k(y)>0$ for all $y\in E_Y$, or $\mathbb E R_k(y)<0$ for all $y\in E_Y$;
--   3. the covariance matrix $\big(\operatorname{Cov}(R_j(y),R_k(y))\big)_{1\le j,k\le d}$ is positive definite for all $y\in E_Y$.
--
--   The fourth condition of the book, $x_0S^0_N<\mu$, involves the problem data and is a hypothesis of Theorem 6.2.3.
--
--   **Formalization Note** The book writes (i) as $\sup_y\mathbb E\|R(y)\|<\infty$. The covariance matrices in (iii) and the matrices $C_n(\rho)=\int\!\int d_n(\Phi(\rho,z))zz^\top Q^R(dz\mid y)\rho(dy)$ of (6.7), which the book uses for every $\rho\in\mathbb P(E_Y)$, need finite second moments under every mixture $\int Q^R(\cdot\mid y)\rho(dy)$; for all $\rho$ at once this is exactly the uniform second-moment bound in 1., which also implies the book's first-moment bound.
-- source:
--   Bäuerle & Rieder (2011), §6.2, Assumption (FM), p.184 (PDF 197)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_Market

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **Assumption (FM) (i)–(iii) of §6.2**, the dynamic mean-variance problem.
Bäuerle & Rieder (2011), §6.2, p.184 (PDF 197): "Assumption (FM):
(i) `sup_y IE ‖R(y)‖ < ∞`.
(ii) There exists a `k ∈ {1, …, d}` such that `IE R_k(y) > 0` for all `y ∈ E_Y` or `IE R_k(y) < 0` for
all `y ∈ E_Y`.
(iii) The covariance matrix of the relative risk process `(Cov(R_j(y), R_k(y)))_{1≤j,k≤d}` is
positive definite for all `y ∈ E_Y`.
(iv) `x_0 S^0_N < μ`."
Item (iv) involves the problem data and is a hypothesis of Theorem 6.2.3.

**Formalization Note.** (i) is stated in `L²`: `sup_y IE ‖R(y)‖² < ∞`. The covariance matrices in
(iii) and the matrices `C_n(ρ) = ∫ ∫ d_n(Φ(ρ, z)) z zᵀ Q^R(dz|y) ρ(dy)` of (6.7), which the book
uses for every `ρ ∈ IP(E_Y)`, require finite second moments of `R` under every mixture
`∫ Q^R(·|y) ρ(dy)`; for all `ρ` at once this is exactly the uniform bound (and it implies the
first-moment bound (i)). The sup norm is used on `Fin d → ℝ`. -/
structure FM62 {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d) : Prop where
  /-- (FM)(i), in `L²`: `sup_y IE ‖R(y)‖² < ∞`. -/
  moment2 : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ y, ∫⁻ z, ‖z‖ₑ ^ 2 ∂M.QR y ≤ K
  /-- (FM)(ii): one coordinate has a mean of constant strict sign. -/
  mean_sign : ∃ k : Fin d, (∀ y, 0 < ∫ z, z k ∂M.QR y) ∨ (∀ y, ∫ z, z k ∂M.QR y < 0)
  /-- (FM)(iii): the covariance matrix of `R(y)` is positive definite for every `y`. -/
  cov_posDef : ∀ y, (Matrix.of fun j k : Fin d =>
    ∫ z, (z j - ∫ w, w j ∂M.QR y) * (z k - ∫ w, w k ∂M.QR y) ∂M.QR y).PosDef

end BauerleRiederMDP.PartialObs


