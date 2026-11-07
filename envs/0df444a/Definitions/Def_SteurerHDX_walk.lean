-- Prove2me | Definitions.Def_SteurerHDX_walk
-- name    : SteurerHDX_walk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:31:01.6226+00:00
-- url     : https://prove2.me/theorems/14a9d85b-a814-4463-9988-1d6ae9ab0ad0
-- title:
--   The simple random walk $P=D^{-1}W$
-- statement:
--   The transition matrix of the simple random walk on a weighted graph with weights $W$ is
--   $$P(x,y)=\frac{W(x,y)}{D(x)} ,\qquad\text{i.e. } P=D^{-1}W .$$
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Section 2.1, p.3

import Mathlib
import Definitions.Def_SteurerHDX_vdeg

namespace SteurerHDX

/-- **The simple random walk P = D⁻¹A.** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Section 2.1, p.3: "let P = D⁻¹A be the
transition probability matrix of the simple random walk on G". -/
noncomputable def walk {ι : Type*} [Fintype ι] (W : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun x y => W x y / vdeg W x

end SteurerHDX


