-- Prove2me | Definitions.Def_OptLocalHamSim_Dph
-- name    : OptLocalHamSim_Dph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:32:40.513089+00:00
-- url     : https://prove2.me/theorems/853d8c3e-c889-4f6a-895a-10ff036297f9
-- title:
--   The phase-average gate $D_{\mathrm{ph}}(z)=\mathrm{diag}(e^{i(\phi+\theta)},e^{i(\phi-\theta)})$ and $|+\rangle$
-- statement:
--   For $z\in\mathbb C$ let $\phi:=\arg z\in(-\pi,\pi]$ ($\phi:=0$ at $z=0$) and $\theta:=\arccos|z|$. The **phase-average gate** is the diagonal one-qubit matrix
--
--   $$
--   D_{\mathrm{ph}}(z):=\begin{pmatrix}e^{i(\phi+\theta)}&0\\0&e^{i(\phi-\theta)}\end{pmatrix},
--   $$
--
--   and $|+\rangle:=(|0\rangle+|1\rangle)/\sqrt2$.
--
--   The circuit encodes each scalar coefficient factor of modulus at most one as the $|+\rangle$ matrix element of such a gate (eq. (12)).
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), §2.2, eq. (12), p.12

import Mathlib

namespace OptLocalHamSim

/-- **The phase-average gate** of eq. (12), p.12 (Shen, Wu, Yao, Yuan, Zhang, STOC 2027 submission,
held version, sha256 44a9768a…): for `z ∈ ℂ` with `|z| ≤ 1`, with `ϕ := arg z ∈ (−π, π]` (`ϕ := 0` at
zero) and `θ := arccos |z|`, `D_ph(z) := diag(e^{i(ϕ+θ)}, e^{i(ϕ−θ)})`.

**Formalization Note** `Complex.arg` takes values in `(−π, π]` with `arg 0 = 0`. The basis is
`false = |0⟩`, `true = |1⟩`. -/
noncomputable def Dph (z : ℂ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun b =>
    if b then Complex.exp (Complex.I * ((Complex.arg z - Real.arccos ‖z‖ : ℝ) : ℂ))
    else Complex.exp (Complex.I * ((Complex.arg z + Real.arccos ‖z‖ : ℝ) : ℂ))

/-- The state `|+⟩ := (|0⟩ + |1⟩)/√2` (p.12). -/
noncomputable def plusVec : Bool → ℂ := fun _ => ((1 / Real.sqrt 2 : ℝ) : ℂ)

end OptLocalHamSim


