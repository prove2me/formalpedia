-- Prove2me | Definitions.Def_PPSLattice_gadgetInv
-- name    : PPSLattice_gadgetInv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:50.617231+00:00
-- url     : https://prove2.me/theorems/929f2f72-6cc6-4a23-a0e3-e41c7935653e
-- title:
--   Bit decomposition $\mathbf G^{-1}(\mathbf P)$
-- statement:
--   For $\mathbf P\in\mathbb Z_q^{n\times c}$, $\mathbf G^{-1}(\mathbf P)\in\{0,1\}^{m\times c}\subseteq\mathbb Z_q^{m\times c}$ is the column-wise bit decomposition: entry $(ik+t,j)$ is bit $t$ of the representative in $[0,q)$ of $P_{ij}$, and rows $\ge nk$ are zero. Then $\mathbf G\mathbf G^{-1}(\mathbf P)=\mathbf P$; $\mathbf G^{-1}$ is not an inverse of $\mathbf G$.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, Gadget Matrix, p.16

import Mathlib
set_option autoImplicit false

namespace PPSLattice

/-- The **bit decomposition** `G^{-1}(P) ∈ Z_q^{m×c}` of a matrix `P ∈ Z_q^{n×c}`, column by column:
with `k = ⌈log₂ q⌉`, entry `(i·k + t, j)` (`t < k`, `i < n`) is bit `t` of the representative in `[0, q)` of
`P_{ij}`, and the rows `≥ n·k` are zero; so `G · G^{-1}(P) = P`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, Gadget Matrix, p.16 ("We write G^{-1} to denote the standard entry-wise bit decomposition
… GG^{-1}(a) = a … Output of G^{-1} is padded with 0s to match the dimensions. We often overload the
notation and write G^{-1}(A) where G^{-1} is performed for each column"). -/
def gadgetInv (q n m : ℕ) {c : ℕ} (P : Matrix (Fin n) (Fin c) (ZMod q)) :
    Matrix (Fin m) (Fin c) (ZMod q) :=
  Matrix.of fun r j =>
    if h : r.val < Nat.clog 2 q * n then
      if (P ⟨r.val / Nat.clog 2 q, Nat.div_lt_of_lt_mul h⟩ j).val.testBit (r.val % Nat.clog 2 q)
      then 1 else 0
    else 0

end PPSLattice


