-- Prove2me | Definitions.Def_QubitFreqSensing_Propagator
-- name    : QubitFreqSensing_Propagator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:04.148741+00:00
-- url     : https://prove2.me/theorems/aeb63d19-0c8f-48de-8f8d-c48b66caf3e2
-- title:
--   Propagator $U_h(a,b)=\exp(-i\Theta Z)$ of the field $h(t)Z$, the basis kets and the rotation $e^{i\theta Y}$
-- statement:
--   The sensing qubit evolves under a Hamiltonian $H(t)=h(t)\,Z$, where $Z=\mathrm{diag}(1,-1)$ is the Pauli $Z$ matrix and $h:\mathbb R\to\mathbb R$ is a scalar field: $h(t)=B\cos(\omega t+\phi)$ when the signal is present and $h\equiv 0$ when it is absent. Time $t$ is absolute, the protocol starting at $t=0$. Since all $H(t)$ are diagonal they commute, and the propagator from time $a$ to time $b$ is
--
--   $$
--   U_h(a,b)=\begin{pmatrix} e^{-i\Theta} & 0\\ 0 & e^{i\Theta}\end{pmatrix}=e^{-i\Theta Z},\qquad \Theta=\int_a^b h(t)\,dt .
--   $$
--
--   The module also fixes the standard basis states $|0\rangle=(1,0)$, $|1\rangle=(0,1)$ and the single-qubit rotation
--
--   $$
--   e^{i\theta Y}=\cos\theta\, I+i\sin\theta\, Y ,
--   $$
--
--   with $Y=\begin{pmatrix}0&-i\\ i&0\end{pmatrix}$ the Pauli $Y$ matrix (taken from the published `MIPRE.LCS.Pauli`). Protocol 1 uses $e^{\pm i\sigma_1\pi Y/4}$ as its first and last gates.
--
--   These are the building blocks of the single-qubit pulse protocols of the mission.
--
--   **Formalization Note** For continuous $h$ the closed form solves $i\,\partial_b U_h(a,b)=h(b)Z\,U_h(a,b)$, $U_h(a,a)=I$ (checked entrywise in the sanity file). $\Theta$ is an interval integral, which Lean sets to $0$ for a non-integrable $h$; the mission only uses continuous fields.
-- source:
--   Chen, Coladangelo, Li, Zhang, Sensing frequencies at the discrete Grover-Heisenberg limit using a single qubit, manuscript (STOC 2027 submission; held version sha256 fd015276…c95c9a2), §3, p.11; §4, eqs. (4)–(7), pp.13–14; Protocol 1, p.12

import Mathlib
import Definitions.Def_MIPRE_LCS_Pauli

open Complex

namespace QubitFreqSensing

/-- The computational basis state `|0⟩` of the sensing qubit (Chen, Coladangelo, Li, Zhang,
*Sensing frequencies at the discrete Grover-Heisenberg limit using a single qubit*, manuscript
(STOC 2027 submission), Protocol 1, p.12: "Prepare the starting state G₀|0⟩"). -/
def ket0 : Fin 2 → ℂ := ![1, 0]

/-- The computational basis state `|1⟩`; measuring in the standard basis gives outcome `1` with
probability `|⟨1|ψ⟩|² = ‖ψ 1‖²`. -/
def ket1 : Fin 2 → ℂ := ![0, 1]

/-- **Propagator of the field `h(t) Z`** (Chen, Coladangelo, Li, Zhang, manuscript (STOC 2027
submission), §3, p.11; §4, p.13). The signal Hamiltonian is `H(t) = h(t) Z` with the scalar field
`h(t) = B cos(ωt + ϕ)` (signal present) or `h ≡ 0` (signal absent). Its propagator from absolute
time `a` to absolute time `b` is
`U_h(a, b) = diag(e^{-iΘ}, e^{iΘ}) = exp(-iΘ Z)`, `Θ = ∫_a^b h(t) dt`.

**Formalization Note** All `H(t)` are diagonal, so they commute and the time-ordered exponential is
the ordinary exponential of `-i ∫ H`; this closed form is the exact solution of
`i ∂_b U(a, b) = h(b) Z U(a, b)`, `U(a, a) = 1`, for continuous `h` (checked in the sanity file).
`Θ` is an interval integral, which Lean sets to `0` for a non-integrable `h`; the mission only uses
continuous fields (`B cos(ω t + ϕ)` and `0`). Time `t` is absolute, the protocol starting at
`t = 0`. -/
noncomputable def propagator (h : ℝ → ℝ) (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![Complex.exp (-Complex.I * ((∫ t in a..b, h t : ℝ) : ℂ)),
    Complex.exp (Complex.I * ((∫ t in a..b, h t : ℝ) : ℂ))]

/-- The single-qubit rotation `e^{iθY} = cos θ · I + i sin θ · Y` (`Y² = I`), with `Y` the Pauli
matrix `MIPRE.LCS.Pauli.Y = !![0, -i; i, 0]` (Chen, Coladangelo, Li, Zhang, manuscript (STOC 2027
submission), Protocol 1, p.12: `G₀ = e^{iσ₁πY/4}` and the undo gate `e^{-iσ₁πY/4} Y^{m-1}`; §7,
p.26). -/
noncomputable def expIY (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cos θ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * Real.sin θ) • MIPRE.LCS.Pauli.Y

end QubitFreqSensing


