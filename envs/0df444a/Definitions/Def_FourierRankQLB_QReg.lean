-- Prove2me | Definitions.Def_FourierRankQLB_QReg
-- name    : FourierRankQLB_QReg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:38:12.084895+00:00
-- url     : https://prove2.me/theorems/99ac6df9-918d-41fc-bff7-d74d3e7ca793
-- title:
--   The register $L^2(Y,\nu)\otimes\mathbb C^2\otimes W$
-- statement:
--   For a measure space $(Y,\nu)$ of query labels and a workspace Hilbert space $W$, the Hilbert space
--   $$
--   L^2(Y,\nu)\otimes\mathbb C^2\otimes W
--   $$
--   of a query register, an answer bit and a workspace.
--
--   A finite grid $G$ of Definition 2.1 is $Y=G$ with counting measure, and the continuous register $L^2(\mathbb R^n)$ is $Y=\mathbb R^n$ with Lebesgue measure.
--
--   **Formalization Note** It is the Bochner space $L^2(Y,\nu;\mathbb C^2\otimes W)$, with $\mathbb C^2\otimes W$ written as the $\ell^2$ sum of two copies of $W$, one per answer bit.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Definitions 2.1–2.2, pp.13–14 and Appendix A, p.50

import Mathlib

open MeasureTheory

namespace FourierRankQLB

/-- The register `L²(Y, ν) ⊗ ℂ² ⊗ W` of a query label, an answer bit and a workspace `W`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Definitions 2.1–2.2, pp. 13–14 and Appendix A, p. 50.

**Formalization Note.** It is the Bochner space `L²(Y, ν; ℂ² ⊗ W)`, with `ℂ² ⊗ W` written
`PiLp 2 (fun _ : Bool => W)`: the two components of a value are its answer-bit branches. A finite
grid `G` is `Y = G` with counting measure, and `L²(ℝⁿ)` is `Y = ℝⁿ` with Lebesgue measure. -/
abbrev QReg {Y : Type} [MeasurableSpace Y] (ν : Measure Y) (W : Type) [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] : Type :=
  Lp (PiLp 2 fun _ : Bool => W) 2 ν

end FourierRankQLB


