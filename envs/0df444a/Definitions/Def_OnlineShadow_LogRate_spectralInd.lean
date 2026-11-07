-- Prove2me | Definitions.Def_OnlineShadow_LogRate_spectralInd
-- name    : OnlineShadow_LogRate_spectralInd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:10:35.265576+00:00
-- url     : https://prove2.me/theorems/fe93ab8a-8cbc-40b1-8f31-3820ac2548ec
-- title:
--   Spectral projector $B=\mathbf 1_{|\overline A-\mathrm{Tr}(A\rho)1|\ge\xi}$
-- statement:
--   For $\xi\in\mathbb R$, the projector
--   $$B=\mathbf 1_{|\overline A-\mathrm{Tr}(A\rho)1|\ge\xi}$$
--   onto the span of the eigenvectors of $\overline X=\overline A\otimes1_{\mathcal R}-\mathrm{Tr}(A\rho)1$ whose eigenvalue has absolute value at least $\xi$: the quantum event that the empirical average deviates from the mean by at least $\xi$ (Lemma 3.4).
--
--
--   **Formalization Note** Obtained by the continuous functional calculus applied to the indicator of $\{x:\xi\le|x|\}$. $\overline X$ is Hermitian with finite spectrum, so this is the spectral formula.
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Lemma 3.4, p. 9

import Mathlib
import Definitions.Def_OnlineShadow_LogRate_Xbar

namespace OnlineShadow.LogRate

/-- The spectral projector `B = 1_{|Ā − Tr(Aρ)1| ≥ ξ}` onto the eigenspaces of `X̄ = Ā ⊗ 1_R − Tr(Aρ)1`
with eigenvalue of absolute value at least `ξ` (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Lemma 3.4, p.9).

**Formalization Note** Mathlib's continuous functional calculus applied to the indicator of
`{x : ξ ≤ |x|}`. `X̄` is Hermitian and its spectrum is finite, so the indicator is continuous on it and
the calculus is the spectral formula. -/
noncomputable def spectralInd {d r : ℕ} (ψ : Fin d × Fin r → ℂ) (n : ℕ) (A : Matrix (Fin d) (Fin d) ℂ)
    (ξ : ℝ) : Matrix (Fin n → Fin d × Fin r) (Fin n → Fin d × Fin r) ℂ :=
  cfc (fun x : ℝ => if ξ ≤ |x| then (1 : ℝ) else 0) (Xbar ψ n A)

end OnlineShadow.LogRate


