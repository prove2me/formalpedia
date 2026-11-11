-- Prove2me | Definitions.Def_StabTestMem_IsUpperTri
-- name    : StabTestMem_IsUpperTri
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:09:18.711069+00:00
-- url     : https://prove2.me/theorems/33f8f52b-cf8f-4c97-999a-885ec78f507e
-- title:
--   Upper-triangular matrices over $\mathbb F_2$
-- statement:
--   $A\in\mathbb F_2^{n\times n}$ is **upper triangular** if $A_{ij}=0$ whenever $j<i$. The diagonal is free; there are $2^{n(n+1)/2}$ such matrices, and each quadratic form $x^\top A'x$ over $\mathbb F_2$ is $x^\top Ax$ for exactly one of them.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), §3.2, p. 19; §5.2, p. 38

import Mathlib

namespace StabTestMem

/-- **Upper-triangular matrices over `F₂` (diagonal included).** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), §3.2, p. 19 ("Let A be
uniformly distributed over upper-triangular matrices in F_2^{n×n}") and §5.2, p. 38 ("f(x) = x^⊤Ax,
with A ∈ F_2^{n×n} an upper triangular matrix").

`IsUpperTri A`: `A_{ij} = 0` whenever `j < i`. The diagonal is free (it carries the linear part of
the quadratic form `x^⊤Ax`), so there are `2^{n(n+1)/2}` such matrices. -/
def IsUpperTri {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  ∀ i j : Fin n, j < i → A i j = 0

end StabTestMem


