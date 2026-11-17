-- Prove2me | Definitions.Def_ConstDepthUnitary_Supplement_quadPhase
-- name    : ConstDepthUnitary_Supplement_quadPhase
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:22:02.900647+00:00
-- url     : https://prove2.me/theorems/520b08ba-236b-4ead-abda-b1b54e751285
-- title:
--   The diagonal quadratic-phase oracle $Q_S$
-- statement:
--   Let $N$ be a natural number and $S$ a real $N\times N$ matrix. The **diagonal quadratic-phase oracle** acts on $L^2(\mathbb R^N)$, the space of square-integrable functions of $N$ real registers $v=(v_0,\dots,v_{N-1})$, by
--   $$
--   Q_S:\ |v\rangle\mapsto e^{\frac12 i\, v^{T}Sv}\,|v\rangle ,
--   $$
--   that is, it multiplies a function $\psi:\mathbb R^N\to\mathbb C$ pointwise by the chirp $v\mapsto e^{\frac12 i\, v^TSv}$:
--   $$
--   (Q_S\psi)(v)=e^{\frac12 i\, v^{T}Sv}\,\psi(v),\qquad v^TSv=\sum_{i,j}v_iS_{ij}v_j .
--   $$
--
--   It is the oracle queried three times in the continuous three-query synthesis algorithm (Theorem 4.1). It has unit modulus, so it is unitary on $L^2(\mathbb R^N)$.
--
--   **Formalization Note** $\mathbb R^N$ is `EuclideanSpace ℝ (Fin N)`, as in the published continuous Fourier transform `ConstDepthUnitary.contF`. The factor $\tfrac12$ is the paper's (Eq. (21)). This is the continuous oracle; the published `ConstDepthUnitary.QHat` is its discretized grid version.
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §4.1, Eq. (21), p.18

import Mathlib

namespace ConstDepthUnitary

namespace Supplement

/-- The diagonal quadratic-phase oracle `Q_S : |v⟩ ↦ e^{(1/2) i vᵀ S v} |v⟩` on `L²(ℝ^N)`, acting on a
function `ψ : ℝ^N → ℂ` as multiplication by the chirp `v ↦ exp((1/2)·i·vᵀSv)`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §4.1, Eq. (21), p.18.

**Formalization Note** `ℝ^N` is `EuclideanSpace ℝ (Fin N)`, as in the published `ConstDepthUnitary.contF`;
the quadratic form is `vᵀSv = ∑ᵢ ∑ⱼ vᵢ Sᵢⱼ vⱼ`. The factor `1/2` is the paper's. -/
noncomputable def quadPhase {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (ψ : EuclideanSpace ℝ (Fin N) → ℂ)
    (v : EuclideanSpace ℝ (Fin N)) : ℂ :=
  Complex.exp ((1 / 2 : ℂ) * Complex.I * ((∑ i, ∑ j, v i * S i j * v j : ℝ) : ℂ)) * ψ v

end Supplement

end ConstDepthUnitary


