-- Prove2me | Definitions.Def_QubitPhaseEst_blochState
-- name    : QubitPhaseEst_blochState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:14.139587+00:00
-- url     : https://prove2.me/theorems/762324b6-5627-4f39-b988-ff61cdbb3c08
-- title:
--   Qubit state $\rho_{\vec n}=\tfrac12(I+\vec n\cdot\vec\sigma)$ and Bloch vector $r(\sin\theta\cos\psi,\sin\theta\sin\psi,\cos\theta)$
-- statement:
--   For a vector $\vec n=(n_x,n_y,n_z)\in\mathbb R^3$ the **qubit state with Bloch vector** $\vec n$ is the $2\times2$ matrix
--
--   $$
--   \rho_{\vec n}=\tfrac12\bigl(I+n_x\sigma_x+n_y\sigma_y+n_z\sigma_z\bigr),
--   $$
--
--   with the Pauli matrices $\sigma_x,\sigma_y,\sigma_z$ in the basis in which $\sigma_z=\mathrm{diag}(1,-1)$. It is a density matrix exactly when $|\vec n|\le 1$, and a mixed state when $|\vec n|<1$. In this basis $\langle 0|\rho_{\vec n}|0\rangle=(1+n_z)/2$ and $\langle 0|\rho_{\vec n}|1\rangle=(n_x-i n_y)/2$.
--
--   The module also defines the Bloch vector in polar coordinates, $\vec n(r,\theta,\psi)=r(\sin\theta\cos\psi,\ \sin\theta\sin\psi,\ \cos\theta)$, with length $r$, polar angle $\theta$ from the $z$ axis and azimuth $\psi$. Every vector of $\mathbb R^3$ has this form; the paper's vectors, which have no $y$ component, are those with $\psi=0$.
--
--   **Formalization Note** The Pauli matrices are the published `BBPSSW.Distill.pauli`. The condition $|\vec n|<1$ is not part of the definition; theorems state it as $n_x^2+n_y^2+n_z^2<1$, because the default norm on `Fin 3 → ℝ` is the sup norm.
-- source:
--   D'Ariano, Macchiavello, Perinotti, Optimal phase estimation for qubit mixed states, arXiv:quant-ph/0411133v3, Sec. II, p. 1, unnumbered (ρ_n = ½(I + n·σ)); p. 2 (n with no y component); p. 3 (angle θ, after Eq. (21))

import Mathlib
import Definitions.Def_BBPSSW_Distill_pauli

namespace QubitPhaseEst

/-- **The one-qubit state with Bloch vector `n`.** D'Ariano, Macchiavello, Perinotti, *Optimal
phase estimation for qubit mixed states*, arXiv:quant-ph/0411133v3, Sec. II, unnumbered, p. 1:
`ρ_n = ½(I + n·σ)`.

**Formalization Note.** The Pauli matrices are the published `BBPSSW.Distill.pauli`, on `Fin 2`
with `0` = spin up, so `σ_z = diag(1, −1)`. The bound `|n| < 1` of the paper is a hypothesis of the
theorems, not part of this definition; it is written `n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 < 1`, because
the default norm on `Fin 3 → ℝ` is the sup norm. -/
noncomputable def blochState (n : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 + (n 0 : ℂ) • BBPSSW.Distill.pauli .x + (n 1 : ℂ) • BBPSSW.Distill.pauli .y
    + (n 2 : ℂ) • BBPSSW.Distill.pauli .z)

/-- The Bloch vector `r (sin θ cos ψ, sin θ sin ψ, cos θ)` of length `r` (for `0 ≤ r`).
arXiv:quant-ph/0411133v3, Sec. II, p. 3: the paper's angle `θ`, with `ψ = 0` there, since it takes
`n` without `y` component (p. 2).

**Formalization Note.** The azimuth `ψ` is the generalization of this formalization: every Bloch
vector is of this form. -/
noncomputable def blochVec (r θ ψ : ℝ) : Fin 3 → ℝ :=
  ![r * Real.sin θ * Real.cos ψ, r * Real.sin θ * Real.sin ψ, r * Real.cos θ]

end QubitPhaseEst


