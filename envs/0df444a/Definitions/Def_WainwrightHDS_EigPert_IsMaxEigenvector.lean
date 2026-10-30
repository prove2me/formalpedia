-- Prove2me | Definitions.Def_WainwrightHDS_EigPert_IsMaxEigenvector
-- name    : WainwrightHDS_EigPert_IsMaxEigenvector
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:25:43.44012+00:00
-- url     : https://prove2.me/theorems/632d1871-6210-4284-8d75-2207a2cc5ee2
-- title:
--   Maximal unit eigenvector of a symmetric matrix
-- statement:
--   Let $Q$ be a real symmetric $d \times d$ matrix with $d \ge 1$ and largest eigenvalue $\gamma_1(Q)$. A vector $v \in \mathbb{R}^d$ is a **maximal eigenvector** of $Q$ if
--
--   $$
--   v \in \mathbb{S}^{d-1}, \text{ i.e. } \|v\|_2 = 1, \qquad\text{and}\qquad Qv = \gamma_1(Q)\, v .
--   $$
--
--   Equivalently (Rayleigh–Ritz), $v$ maximizes $\langle v, Qv\rangle$ over the unit sphere. These are the objects $\theta^*$ and $\widehat\theta$ compared in the eigenvector perturbation bound of Theorem 8.5; a maximal eigenvector is determined at best up to sign.
--
--   **Formalization Note** The dimension is written $d = n + 1$ so that $\gamma_1$ exists. Vectors live in `EuclideanSpace ℝ (Fin (n+1))` and $Q$ acts through `Matrix.toEuclideanLin`.
-- source:
--   Wainwright, High-Dimensional Statistics, Cambridge University Press 2019, Section 8.2.1, p. 242 (PDF p. 262) and Theorem 8.5, p. 243 (PDF p. 263), "maximum eigenvector θ* ∈ S^{d−1}"

import Mathlib
import Definitions.Def_WainwrightHDS_EigPert_gamma

namespace WainwrightHDS.EigPert

/-- **Maximal (unit) eigenvector of a symmetric matrix.**
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, Section 8.2.1, p. 242 (PDF p. 262) and Theorem 8.5, p. 243 (PDF p. 263):
"maximum eigenvector `θ* ∈ S^{d−1}`".

`IsMaxEigenvector Q hQ v` says that `v` lies on the Euclidean unit sphere `S^{d−1}` and is an
eigenvector of `Q` for its largest eigenvalue `γ₁(Q) = gamma Q hQ 0`: `‖v‖₂ = 1` and `Q v = γ₁(Q) v`.

**Formalization Note.** The dimension is written `d = n + 1` so that `γ₁` exists. Vectors live in
`EuclideanSpace ℝ (Fin (n+1))` (Euclidean norm) and `Q` acts through `Matrix.toEuclideanLin`.
The eigenvector form is used; by the Rayleigh–Ritz characterization (6.3) it is equivalent to
"`v` maximizes `⟨v, Qv⟩` over `S^{d−1}`". -/
def IsMaxEigenvector {n : ℕ} (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hQ : Q.IsHermitian)
    (v : EuclideanSpace ℝ (Fin (n + 1))) : Prop :=
  ‖v‖ = 1 ∧ Matrix.toEuclideanLin Q v = gamma Q hQ 0 • v

end WainwrightHDS.EigPert


