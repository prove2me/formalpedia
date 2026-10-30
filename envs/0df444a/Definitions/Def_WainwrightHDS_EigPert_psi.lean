-- Prove2me | Definitions.Def_WainwrightHDS_EigPert_psi
-- name    : WainwrightHDS_EigPert_psi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:26:08.361814+00:00
-- url     : https://prove2.me/theorems/34a6d464-f530-49e4-9f16-4d1d35bc445c
-- title:
--   The function $\Psi(\Delta; P)$ of Eq. (8.13)
-- statement:
--   Let $P$ be a real $d \times d$ matrix and $\theta^* \in \mathbb{R}^d$. For an error vector $\Delta \in \mathbb{R}^d$ define
--
--   $$
--   \Psi(\Delta; P) := \langle \Delta, P\Delta\rangle + 2\,\langle \Delta, P\theta^*\rangle .
--   $$
--
--   In the proof of Theorem 8.5 it is evaluated at $\widehat\Delta = \widehat\theta - \theta^*$; for symmetric $P$ it equals $\langle\widehat\theta, P\widehat\theta\rangle - \langle\theta^*, P\theta^*\rangle$. It is the right-hand side of the PCA basic inequality (Lemma 8.6).
--
--   **Formalization Note** Vectors live in `EuclideanSpace ℝ (Fin d)`, $P$ acts through `Matrix.toEuclideanLin`, and $\langle\cdot,\cdot\rangle$ is the Euclidean inner product. The argument order is `psi θstar P Δ`.
-- source:
--   Wainwright, High-Dimensional Statistics, Cambridge University Press 2019, proof of Theorem 8.5, p. 243 (PDF p. 263), Eq. (8.13)

import Mathlib

namespace WainwrightHDS.EigPert

/-- **The function `Ψ(Δ; P)` of Eq. (8.13).**
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, proof of Theorem 8.5, p. 243 (PDF p. 263):
"`Ψ(Δ; P) := ⟨Δ, PΔ⟩ + 2⟨Δ, Pθ*⟩`. (8.13)"

`psi θstar P Δ = ⟨Δ, PΔ⟩ + 2⟨Δ, Pθ*⟩` for a matrix `P`, the reference vector `θ*` and an error
vector `Δ`.

**Formalization Note.** Vectors live in `EuclideanSpace ℝ (Fin d)`, `P` acts through
`Matrix.toEuclideanLin`, and `⟨·,·⟩` is the Euclidean inner product `inner ℝ`. -/
noncomputable def psi {d : ℕ} (θstar : EuclideanSpace ℝ (Fin d))
    (P : Matrix (Fin d) (Fin d) ℝ) (Δ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  inner ℝ Δ (Matrix.toEuclideanLin P Δ) + 2 * inner ℝ Δ (Matrix.toEuclideanLin P θstar)

end WainwrightHDS.EigPert


