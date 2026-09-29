-- Prove2me | Definitions.Def_PenningTrap_model
-- name    : PenningTrap_model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T17:02:57.008987+00:00
-- url     : https://prove2.me/theorems/29652d48-fe6a-4839-b271-5adbd061f983
-- title:
--   Penning trap: mode matrix $M(\omega)=K-\omega^2 I-i\omega\omega_c C(b)$ and its characteristic cubic
-- statement:
--   This is the linear model of a charged particle in a Penning trap.
--
--   Let $K$ be a real $3\times3$ matrix and $b=(b_1,b_2,b_3)\in\mathbb{R}^3$. Write $C(b)$ for the antisymmetric matrix of the map $u\mapsto b\times u$,
--
--   $$C(b)=\begin{pmatrix}0&-b_3&b_2\\ b_3&0&-b_1\\ -b_2&b_1&0\end{pmatrix}.$$
--
--   For real numbers $\omega_c$ (the free-space cyclotron frequency $qB/m$) and $\omega$, the **mode matrix** is the complex matrix
--
--   $$M(\omega)=K-\omega^2 I-i\,\omega\,\omega_c\,C(b),$$
--
--   obtained by substituting $r(t)=u\,e^{-i\omega t}$ into the equation of motion $r''=-Kr+\omega_c\,(r'\times b)$ of a particle moving in the linear force field $-Kr$ and the magnetic field $B\,b$; here $K$ is the Hessian of the electrostatic potential divided by the mass.
--
--   The **characteristic cubic** of the trap is the real polynomial in $\lambda=\omega^2$
--
--   $$q(\lambda)=\det(\lambda I-K)-\omega_c^2\,\lambda\big(\lambda\langle b,b\rangle-\langle b,Kb\rangle\big).$$
--
--   These three constructions are the whole model: the normal-mode frequencies of the trap are the $\omega$ with $\det M(\omega)=0$, and the tilt of the magnetic field relative to the axis of the potential, as well as any elliptic distortion of the potential, are encoded simply by letting $K$ be an arbitrary symmetric matrix.
--
--   **Formalization Note.** All three are total definitions with no side conditions: symmetry of $K$, tracelessness of $K$ and $\langle b,b\rangle=1$ are hypotheses of the individual theorems rather than part of the model.
-- source:
--   X. Fan, T. G. Myers, B. A. D. Sukra, G. Gabrielse, Measurement of the Electron Magnetic Moment, Phys. Rev. Lett. 130, 071801 (2023), arXiv:2209.13084v2, p. 2, Eq. (4) (invariance theorem), with Eq. (2)-(3) for the trap frequencies; original source L. S. Brown and G. Gabrielse, Phys. Rev. A 25, 2423 (1982).

import Mathlib

open Matrix

namespace PenningTrap

/-- The matrix of the linear map `u ↦ b ×₃ u` on `Fin 3 → ℝ`. -/
def crossMatrix (b : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -b 2, b 1; b 2, 0, -b 0; -b 1, b 0, 0]

/-- The mode matrix `M(ω) = K - ω² I - i ω ω_c C(b)` of a charged particle moving in the
linear force field `-K r` together with the magnetic force `ω_c (r' ×₃ b)`. -/
noncomputable def modeMatrix (K : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ) (wc w : ℝ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  K.map (fun x : ℝ => (x : ℂ)) - ((w : ℂ) ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℂ)
    - (Complex.I * (w : ℂ) * (wc : ℂ)) • (crossMatrix b).map (fun x : ℝ => (x : ℂ))

/-- The characteristic cubic of the trap, as a polynomial in `lam = ω²`:
`det (lam I - K) - ω_c² lam (lam ⟪b, b⟫ - ⟪b, K b⟫)`. -/
noncomputable def charCubic (K : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ) (wc lam : ℝ) : ℝ :=
  (lam • (1 : Matrix (Fin 3) (Fin 3) ℝ) - K).det
    - wc ^ 2 * lam * (lam * (b ⬝ᵥ b) - b ⬝ᵥ K.mulVec b)

end PenningTrap


