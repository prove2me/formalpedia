-- Prove2me | Definitions.Def_LogLogJam_Vsq
-- name    : LogLogJam_Vsq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:57.370507+00:00
-- url     : https://prove2.me/theorems/226662a4-726f-48c6-a8f8-57693a959496
-- title:
--   Squeezed covariance $V_{\lambda,\theta}$, energy $E$, and trace distance on the squeezed family
-- statement:
--   For $\lambda>0$ and $\theta\in\mathbb R$ let $R(\theta)=\begin{pmatrix}\cos\theta&-\sin\theta\\\sin\theta&\cos\theta\end{pmatrix}$ be the rotation matrix. The **squeezed vacuum** $\rho_{\lambda,\theta}$ is the single-mode pure Gaussian state with zero mean and covariance matrix
--
--   $$
--   V_{\lambda,\theta}=R(\theta)\begin{pmatrix}\lambda&0\\0&\lambda^{-1}\end{pmatrix}R(\theta)^\top .
--   $$
--
--   Its **energy** is $E=\tfrac14\operatorname{tr}V_{\lambda,\theta}=\tfrac14(\lambda+\lambda^{-1})$; for $E>1/2$ the paper takes $\lambda>1$ the unique solution of this equation. The angle $\theta$ lives on $\mathbb T=\mathbb R/\pi\mathbb Z$, since $V_{\lambda,\theta}$ is $\pi$-periodic.
--
--   The **trace distance** between two members of the family is
--
--   $$
--   D_{\mathrm{tr}}(\rho_{\lambda,\theta},\rho_{\lambda,\theta'})=\sqrt{1-\frac{2}{\sqrt{\det(V_{\lambda,\theta}+V_{\lambda,\theta'})}}},
--   $$
--
--   the pure-state formula of Lemma 4.1 at zero mean. These objects define the hard instance of the lower bound: the learner must locate the squeezing angle $\theta$.
--
--   **Formalization Note** The squeezing parameter is written `lam`. Lemma 4.1 is used as the definition of the trace distance on this family, so no Fock space is needed. The vacuum covariance is the identity (the paper's normalization).
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), §4.2, p.16 (rotation); §5.1, eq. (9), p.22 (PDF p.25); Lemma 4.1, pp.15–16 (PDF pp.18–19)

import Mathlib

open Matrix

namespace LogLogJam

/-- The single-mode phase-space rotation matrix
`R(θ) = [[cos θ, −sin θ], [sin θ, cos θ]]` (Chen, Gong, Ye, Zhang, *The log log jam in Gaussian state
tomography*, arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, §4.2, p.16, and
eq. (9), p.22). -/
noncomputable def rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- The covariance matrix of the squeezed vacuum `ρ_{λ,θ}` (arXiv:2607.12983, version of
November 3, 2026, sha256 97b751ca…, §5.1, eq. (9), p.22):
`V_{λ,θ} = R(θ) diag(λ, λ⁻¹) R(θ)ᵀ`.

**Formalization Note** The squeezing parameter is written `lam` (`λ` is reserved in Lean). The
paper takes `λ > 1`; the matrix is defined for every real `lam` and the hypotheses on `lam` sit in
the statements. `θ` is real; `V_{λ,θ}` is `π`-periodic in `θ`, so `θ ∈ ℝ` represents
`θ ∈ 𝕋 = ℝ/πℤ`. The vacuum covariance is the identity (the paper's normalization, §4.2, p.15). -/
noncomputable def Vsq (lam θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  rot θ * !![lam, 0; 0, lam⁻¹] * (rot θ)ᵀ

/-- The energy `E = ¼(λ + λ⁻¹)` of the squeezed vacuum `ρ_{λ,θ}` (arXiv:2607.12983, version of
November 3, 2026, sha256 97b751ca…, §5.1, p.22: "let λ > 1 be the unique solution to
E = ¼(λ + λ⁻¹)"; this is `E(ρ) = ¼ Tr V(ρ)` of §4.2, p.15, at zero mean). -/
noncomputable def energy (lam : ℝ) : ℝ :=
  (lam + lam⁻¹) / 4

/-- The trace distance `D_tr(ρ_{λ,θ}, ρ_{λ,θ'})` between two squeezed vacua (arXiv:2607.12983,
version of November 3, 2026, sha256 97b751ca…, Lemma 4.1, pp.15–16, with `n = 1` and zero means):
`D_tr = √(1 − F)` with fidelity `F = 2 / √det(V_{λ,θ} + V_{λ,θ'})`.

**Formalization Note** Lemma 4.1 (a fact about pure Gaussian states on Fock space) is used as the
definition of the trace distance on this family; the classical encoding of the mission needs no
Fock space. For these matrices `det(V_{λ,θ} + V_{λ,θ'}) ≥ 4` whenever `lam > 0`, so the square roots
are taken of nonnegative numbers. -/
noncomputable def trDist (lam θ θ' : ℝ) : ℝ :=
  Real.sqrt (1 - 2 / Real.sqrt (Vsq lam θ + Vsq lam θ').det)

end LogLogJam


