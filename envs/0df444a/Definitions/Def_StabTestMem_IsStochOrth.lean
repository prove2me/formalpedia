-- Prove2me | Definitions.Def_StabTestMem_IsStochOrth
-- name    : StabTestMem_IsStochOrth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:09:16.389206+00:00
-- url     : https://prove2.me/theorems/0e238bdc-6217-4c36-99d6-dad55f681eee
-- title:
--   Stochastic orthogonal group $\mathcal O_t$
-- statement:
--   The **stochastic orthogonal group** $\mathcal O_t$ is the group of matrices $O\in\mathbb F_2^{t\times t}$ with $OO^{\top}=O^{\top}O=I$; equivalently $\langle x,y\rangle=\langle Ox,Oy\rangle$ for all $x,y\in\mathbb F_2^t$. It contains the permutation matrices.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Definition 2.8, p. 16

import Mathlib

namespace StabTestMem

/-- **The stochastic orthogonal group `O_t`.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Definition 2.8, p. 16: "The stochastic
orthogonal group O_t is the subgroup of matrices in F_2^{t×t} such that O O^⊤ = O^⊤ O = I."

`IsStochOrth O` is membership of the `t × t` matrix `O` over `F₂` in `O_t`. -/
def IsStochOrth {t : ℕ} (O : Matrix (Fin t) (Fin t) (ZMod 2)) : Prop :=
  O * O.transpose = 1 ∧ O.transpose * O = 1

end StabTestMem


