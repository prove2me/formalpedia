-- Prove2me | Definitions.Def_ShadowBootstrap_shadowSecondMoment
-- name    : ShadowBootstrap_shadowSecondMoment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:27.033198+00:00
-- url     : https://prove2.me/theorems/0d7b0377-1935-4562-8063-1b0d7c2da666
-- title:
--   Second moment $\mathbb E\hat\rho^2$ of the shadow estimator (Eq. (7))
-- statement:
--   For an ensemble $E$ of $n$-qubit unitaries with shadow channel $\mathcal M$ (Eq. (2), p.9), a randomized measurement samples $U \sim E$, measures a state $\rho$ in the rotated basis and records the outcome $b$ with probability $\langle b|U\rho U^\dagger|b\rangle$; the shadow estimator is $\hat\rho = \mathcal M^{-1}(U^\dagger|b\rangle\langle b|U)$ (Eq. (3)). Its **second moment** is
--   $$\mathbb E\,\hat\rho^2 = \mathbb E_{U,b}\big[\mathcal M^{-1}(U^\dagger|b\rangle\langle b|U)^2\big] = \sum_i w_i \sum_b \langle b|U_i\rho U_i^\dagger|b\rangle\, \hat\rho_{i,b}^2 .$$
--
--   It is the matrix whose operator norm Lemma 3.7 bounds by $O(d)$; it controls the finite-shot part of the residual estimator in Lemma 4.2.
--
--   **Formalization Note** Shadows and outcome probabilities are the published `ClassicalShadow.Linear.shadow` and `snapProb`. $\mathcal M^{-1}$ is `Ring.inverse`, so statements assume or prove that $\mathcal M$ is invertible.
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Definition 3.2, Eqs. (2)–(3), p.9; Lemma 3.7, Eq. (7), p.10

import Mathlib
import Definitions.Def_ClassicalShadow_Linear_Setting

open ClassicalShadow.Linear

namespace ShadowBootstrap

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Lemma 3.7, Eq. (7), p.10: the second moment of the shadow estimator,
`E ρ̂² = E_{U, b} [M⁻¹(U†|b⟩⟨b|U)²] = Σ_i w_i Σ_b ⟨b|U_i ρ U_i†|b⟩ ρ̂_{i,b}²`, where the record
`(U_i, b)` is drawn by sampling `U_i ∼ E` and measuring the state `ρ` in the rotated basis.

**Formalization Note** The shadow `ρ̂_{i,b}` is the published
`ClassicalShadow.Linear.shadow E (i, b) = M⁻¹(U_i†|b⟩⟨b|U_i)` and the outcome probability the
published `snapProb E ρ (i, b) = w_i ⟨b|U_i ρ U_i†|b⟩`; `M⁻¹` is `Ring.inverse`, so statements
assume or prove `IsUnit (measChannel E)`. -/
noncomputable def shadowSecondMoment {n : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι)
    (ρ : Op n) : Op n :=
  ∑ ω, ((snapProb E ρ ω : ℝ) : ℂ) • (shadow E ω * shadow E ω)

end ShadowBootstrap


