-- Prove2me | Definitions.Def_PPSLattice_kronG
-- name    : PPSLattice_kronG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:33:35.386009+00:00
-- url     : https://prove2.me/theorems/41ada445-402b-4d02-b0c8-8761b1a985fe
-- title:
--   Kronecker product $\mathbf x^\top\otimes\mathbf G$
-- statement:
--   For a bit vector $\mathbf x\in\{0,1\}^\ell$, $\mathbf x^\top\otimes\mathbf G\in\mathbb Z_q^{n\times\ell m}$ has $x_k\mathbf G$ as its $k$-th block of $m$ columns. It appears in $(\mathbf B-\mathbf x^\top\otimes\mathbf G)\mathbf H_{f,x}$ and in $\mathbf A-\mathrm{encvec}(i)\otimes\mathbf G$.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, p.16–17; Figure 1, p.22

import Mathlib
import Definitions.Def_PPSLattice_gadget
set_option autoImplicit false

namespace PPSLattice

/-- The **Kronecker product** `x^⊤ ⊗ G ∈ Z_q^{n×ℓm}` of a bit vector `x ∈ {0,1}^ℓ` (a row) with the
gadget matrix `G ∈ Z_q^{n×m}`: its `k`-th block of `m` columns is `x_k · G`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, p.16 ("A ⊗ B to denote the Kronecker product"), Homomorphic Computation, p.17
("(B − x^⊤ ⊗ G)H_{f,x}"); Figure 1, p.22 ("encvec(i) ⊗ G").

**Formalization Note.** Column `(k, j)` of an `n × ℓm` matrix is column `k·m + j` (`finProdFinEquiv`),
so blocks are consecutive; the bits of `x` are its list entries, missing ones read `0`. -/
def kronG (q n m ell : ℕ) (x : List Bool) : Matrix (Fin n) (Fin (ell * m)) (ZMod q) :=
  Matrix.of fun i c =>
    (if x.getD (finProdFinEquiv.symm c).1 false then 1 else 0) * gadget q n m i (finProdFinEquiv.symm c).2

end PPSLattice


