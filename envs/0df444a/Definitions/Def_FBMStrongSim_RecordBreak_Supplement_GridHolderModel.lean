-- Prove2me | Definitions.Def_FBMStrongSim_RecordBreak_Supplement_GridHolderModel
-- name    : FBMStrongSim_RecordBreak_Supplement_GridHolderModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:28:42.672797+00:00
-- url     : https://prove2.me/theorems/fedb65c2-ae3c-4f52-a726-26d80bee62a3
-- title:
--   Restricted homogeneous Hölder seminorm on a finite dyadic grid
-- statement:
--   For a path $z$ into a normed space, the restricted seminorm on $D_n$ is
--   $$H_\alpha(z\mid D_n)=\max_{0\le i<j\le2^n}\frac{\|z(t_i^n)-z(t_j^n)\|}{|t_i^n-t_j^n|^\alpha}.$$
--   The implementation takes the maximum over all ordered pairs, assigning zero to diagonal pairs. Symmetry and nonnegativity make this equivalent for $\alpha>0$. The grid always has at least two points, including $n=0$, and all quotients are finite. For a matrix-valued coefficient, apply it to the array of entries, so its norm is the maximum entry norm.
--
--   Differences from the source:
--   - generalization: the restricted seminorm of real or finite-vector paths → the restricted seminorm into any normed additive group; reason: specializing to the real and maximum-norm finite-vector paths gives the source settings
--   - encoding: the supremum over i<j on the finite dyadic grid → a finite maximum over all ordered pairs, with zero diagonal quotients; reason: the grid has at least two points even at n=0; symmetry and nonnegativity recover the same maximum for the positive exponents used by the theorems
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, p. 31, restricted α-Hölder norm

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Model

namespace FBMStrongSim.RecordBreak.Supplement

/-- The finite grid seminorm. Equal pairs contribute zero, hence do not affect the maximum.
It is finite for every path, and no unbounded real supremum is taken. -/
noncomputable def gridHolder {E : Type*} [NormedAddCommGroup E]
    (alpha : ℝ) (n : ℕ) (z : ℝ → E) : ℝ :=
  (Finset.univ : Finset (Fin (2 ^ n + 1) × Fin (2 ^ n + 1))).sup' (by simp)
    (fun ij => ‖z (dyadic n ij.1) - z (dyadic n ij.2)‖ /
      |dyadic n ij.1 - dyadic n ij.2| ^ alpha)

end FBMStrongSim.RecordBreak.Supplement


