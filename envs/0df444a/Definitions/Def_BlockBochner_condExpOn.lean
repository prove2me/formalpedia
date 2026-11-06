-- Prove2me | Definitions.Def_BlockBochner_condExpOn
-- name    : BlockBochner_condExpOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:36:19.032743+00:00
-- url     : https://prove2.me/theorems/fc985cdf-f599-4b5d-8f56-514f7c3b0b12
-- title:
--   Conditional expectation $E_\nu[\,\cdot\mid X_J]$ on $L^2(\nu)$
-- statement:
--   For a measure $\nu$ on $\prod_i X_i$ and a set of sites $J$, $E_\nu[\,\cdot\mid X_J]$ is the conditional expectation given the spins at $J$, viewed as a bounded operator on $L^2(\nu)$: the orthogonal projection of $L^2(\nu)$ onto the closed subspace of (classes of) $\sigma(X_J)$-measurable functions.
--
--   The paper's single-site operators are $E_v f=E_\mu[f\mid X_{-v}]$ (Sec. 1.6) and, on a link $\nu$, $P^\nu_i f=E_\nu[f\mid X_{R\setminus\{i\}}]$ (Sec. 2.2); both are this operator with $J=\{v\}^c$.
--
--   **Formalization Note** Mathlib's `condExpL2` for the $\sigma$-algebra $\sigma(X_J)$, composed with the inclusion into $L^2(\nu)$ (`Lp ℝ 2 ν`).
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 1.6, p.8; Sec. 2.2, p.16

import Mathlib
import Definitions.Def_BlockBochner_coordSigma

open MeasureTheory

namespace BlockBochner

/-- **Conditional expectation `E_ν[· | X_J]` on `L²(ν)`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 1.6, p.8
(`E_v f = E_µ[f | X_{−v}]`) and Sec. 2.2, p.16 (`P^ν_i f = E_ν[f | X_{R∖{i}}]`): the conditional
expectation given the spins at the sites of `J`, as an operator on `L²(ν)`. It is the orthogonal
projection of `L²(ν)` onto the closed subspace of (classes of) `σ(X_J)`-measurable functions.

**Formalization Note** `L²(ν)` is `Lp ℝ 2 ν`. The operator is Mathlib's `condExpL2` for the
σ-algebra `coordSigma J`, followed by the inclusion of that subspace into `L²(ν)`; it is defined for
every measure `ν` on a product of measurable spaces, so the same definition serves `µ`, its marginals
and its links. -/
noncomputable def condExpOn {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (ν : Measure (∀ i, X i)) (J : Set ι) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  (lpMeas ℝ ℝ (coordSigma J) 2 ν).subtypeL ∘L condExpL2 ℝ ℝ (coordSigma_le J)

end BlockBochner


