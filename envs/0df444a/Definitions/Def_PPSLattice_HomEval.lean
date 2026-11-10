-- Prove2me | Definitions.Def_PPSLattice_HomEval
-- name    : PPSLattice_HomEval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:33:44.849432+00:00
-- url     : https://prove2.me/theorems/bbd1ac6b-61d9-4478-985a-c3ccb72c5076
-- title:
--   Lattice homomorphic computation: EvalF and EvalFX
-- statement:
--   The homomorphic computation machinery consists of two deterministic algorithms:
--
--   1. $\mathrm{EvalF}(\mathbf B,f)\to\mathbf B_f\in\mathbb Z_q^{n\times m}$ for $\mathbf B\in\mathbb Z_q^{n\times\ell m}$ and $f\in\mathcal F_{d,\ell}$;
--   2. $\mathrm{EvalFX}(\mathbf B,f,x)\to\mathbf H_{f,x}\in\mathbb Z_q^{\ell m\times m}$ for $x\in\{0,1\}^\ell$.
--
--   Functions are given by NAND circuits.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, Homomorphic Computation, p.16

import Mathlib
import Definitions.Def_RestrictedDec_Circuit
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- An implementation of the **lattice homomorphic computation** algorithms, for every `(q, n, m)` and
input length `ℓ`:
1. `evalF q n m ℓ B f`: `EvalF(B, f) → B_f ∈ Z_q^{n×m}` for `B ∈ Z_q^{n×ℓm}` and a circuit `f`;
2. `evalFX q n m ℓ B f x`: `EvalFX(B, f, x) → H_{f,x} ∈ Z_q^{ℓm×m}` for an input `x ∈ {0,1}^ℓ`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, Homomorphic Computation, p.16 ("provides two deterministic polynomial-time algorithms").

**Formalization Note.** The functions `f ∈ F_{d,ℓ}` are given by circuits (`RestrictedDec.Circuit`);
inputs are bit strings. -/
structure HomEval where
  evalF : (q n m ell : ℕ) → Matrix (Fin n) (Fin (ell * m)) (ZMod q) → RestrictedDec.Circuit →
    Matrix (Fin n) (Fin m) (ZMod q)
  evalFX : (q n m ell : ℕ) → Matrix (Fin n) (Fin (ell * m)) (ZMod q) → RestrictedDec.Circuit →
    List Bool → Matrix (Fin (ell * m)) (Fin m) (ZMod q)

end PPSLattice


