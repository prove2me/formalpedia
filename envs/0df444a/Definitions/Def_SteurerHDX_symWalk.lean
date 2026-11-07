-- Prove2me | Definitions.Def_SteurerHDX_symWalk
-- name    : SteurerHDX_symWalk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:31:15.033454+00:00
-- url     : https://prove2.me/theorems/777c97f7-2c0d-49a9-9c44-b4c020f02312
-- title:
--   The symmetrized walk $D^{-1/2}WD^{-1/2}$
-- statement:
--   For a weighted graph with weights $W$ and degrees $D$, the matrix
--   $$S(x,y)=\frac{W(x,y)}{\sqrt{D(x)}\sqrt{D(y)}},\qquad S=D^{-1/2}WD^{-1/2}.$$
--   When $D>0$, $P=D^{-1}W=D^{-1/2}SD^{1/2}$ is similar to $S$, so $P$ and $S$ have the same eigenvalues with the same multiplicities; $S$ is symmetric when $W$ is. This auxiliary matrix is how the real spectrum of $P$ (Section 2.1) is accessed.
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Section 2.1, p.3

import Mathlib
import Definitions.Def_SteurerHDX_vdeg

namespace SteurerHDX

/-- **The symmetrized walk D^{-1/2} A D^{-1/2}.** Auxiliary for Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Section 2.1, p.3
("P is self-adjoint w.r.t. this inner product. So, by spectral theorem it has real eigenvalues").

**Formalization Note.** For positive degrees, P = D⁻¹A = D^{-1/2} S D^{1/2} with
S = D^{-1/2} A D^{-1/2}, so P and S have the same eigenvalues with the same multiplicities, and S
is a symmetric real matrix when A is. -/
noncomputable def symWalk {ι : Type*} [Fintype ι] (W : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun x y => W x y / (Real.sqrt (vdeg W x) * Real.sqrt (vdeg W y))

end SteurerHDX


