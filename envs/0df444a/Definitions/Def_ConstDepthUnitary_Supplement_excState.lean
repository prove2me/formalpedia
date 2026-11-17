-- Prove2me | Definitions.Def_ConstDepthUnitary_Supplement_excState
-- name    : ConstDepthUnitary_Supplement_excState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:22:18.7732+00:00
-- url     : https://prove2.me/theorems/3551a8cb-a031-4958-becb-8d7e3569cdfb
-- title:
--   Single-excitation states $\psi_x$ of the $N$-mode harmonic oscillator
-- statement:
--   For $x\in[N]=\{0,\dots,N-1\}$, the **single-excitation state** $\psi_x\in L^2(\mathbb R^N)$ is the function
--   $$
--   \psi_x(v)=\sqrt{\frac{2}{\pi^{N/2}}}\;e^{-\frac12\|v\|_2^2}\;v_x ,\qquad v\in\mathbb R^N ,
--   $$
--   where $\|v\|_2$ is the Euclidean norm. It is the tensor product of the first excited Hermite function $h_1$ in register $x$ with the Gaussian ground state $h_0$ in every other register, a "one-hot" encoding of $x$ in the single-excitation sector of the $N$-mode quantum harmonic oscillator. The states $\psi_0,\dots,\psi_{N-1}$ are orthonormal in $L^2(\mathbb R^N)$ (Eq. (25)).
--
--   **Formalization Note** $\mathbb R^N$ is `EuclideanSpace ℝ (Fin N)` and $x$ ranges over `Fin N`. The function is real valued and cast to $\mathbb C$. The published `ConstDepthUnitary.psiHat` is the discretized grid version, not this.
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §4.3, Eq. (24), p.19

import Mathlib

namespace ConstDepthUnitary

namespace Supplement

/-- The single-excitation state `ψ_x(v) = √(2/π^{N/2}) · e^{−‖v‖²/2} · v_x` of the `N`-mode harmonic
oscillator, for `x ∈ [N]`: the first Hermite function in mode `x` and the Gaussian ground state in the
other modes.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §4.3, Eq. (24), p.19.

**Formalization Note** `ℝ^N` is `EuclideanSpace ℝ (Fin N)` and `‖v‖` its Euclidean norm. The function is
real valued, cast to `ℂ`. The family `(ψ_x)` is orthonormal in `L²(ℝ^N)` (Eq. (25)). -/
noncomputable def excState {N : ℕ} (x : Fin N) (v : EuclideanSpace ℝ (Fin N)) : ℂ :=
  ((Real.sqrt (2 / Real.pi ^ ((N : ℝ) / 2)) * Real.exp (-(‖v‖ ^ 2) / 2) * v x : ℝ) : ℂ)

end Supplement

end ConstDepthUnitary


