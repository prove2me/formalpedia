-- Prove2me | Definitions.Def_PPSLattice_BGGHomEval
-- name    : PPSLattice_BGGHomEval
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:35:36.951792+00:00
-- url     : https://prove2.me/theorems/38e27464-1965-4f95-b151-85ab5ab48b60
-- title:
--   Explicit BGG+ homomorphic evaluation for NAND circuits
-- statement:
--   This module gives the canonical BGG+ evaluation algorithms for NAND circuits. For every wire $w$, it maintains a public matrix $\mathbf B_w$ and an evaluation matrix $\mathbf H_w$. An input wire $k$ has the $k$-th block of $\mathbf B$ and the corresponding block-selector matrix. A NAND gate with input wires $a,b$ uses the recurrences
--   $$
--   \mathbf B_{\mathrm{out}}=\mathbf G-\mathbf B_a\mathbf G^{-1}(\mathbf B_b),\qquad
--   \mathbf H_{\mathrm{out}}=-\mathbf H_a\mathbf G^{-1}(\mathbf B_b)-x_a\mathbf H_b.
--   $$
--   `evalF` selects the output wire's public matrix and `evalFX` selects its evaluation matrix. References to unavailable wires read zero, matching `RestrictedDec.Circuit.eval`. When $n=0$, `evalFX` returns the zero matrix; all matrix identities are then vacuous and this also covers the otherwise degenerate norm bound $m=1$.
--
--   The second recurrence is the matrix form of the standard BGG+ ciphertext update: with $\mathbf C_w=\mathbf B_w-x_w\mathbf G$,
--   $$
--   \mathbf C_{\mathrm{out}}=\mathbf G-\mathbf C_a\mathbf G^{-1}(\mathbf B_b)-x_a\mathbf C_b
--   =\mathbf B_{\mathrm{out}}-(1-x_ax_b)\mathbf G.
--   $$
--
--   **Formalization Note.** Wires and consecutive matrix blocks are lists indexed by natural numbers, and `ZMod q` scalar multiplication implements multiplication by a bit. The construction is deterministic and does not use choice or any unproved hypothesis.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, Homomorphic Computation, pp.16–17; the NAND specialization of the standard GSW13/BGG+14 evaluation recurrence cited there.

import Mathlib
import Definitions.Def_PPSLattice_HomEval
import Definitions.Def_PPSLattice_gadgetInv
import Definitions.Def_PPSLattice_kronG
set_option autoImplicit false

namespace PPSLattice

/-- A Boolean bit as an element of `ZMod q`. -/
def bggBit {q : ℕ} (b : Bool) : ZMod q := if b then 1 else 0

/-- The `k`-th consecutive block of `m` columns, with missing blocks read as zero. -/
def bggInputBlock (q n m ell : ℕ) (B : Matrix (Fin n) (Fin (ell * m)) (ZMod q)) (k : ℕ) :
    Matrix (Fin n) (Fin m) (ZMod q) :=
  Matrix.of fun i j => if h : k < ell then B i (finProdFinEquiv (⟨k, h⟩, j)) else 0

/-- The public matrices associated with all input and gate wires. -/
def bggWireMatrices (q n m ell : ℕ) (B : Matrix (Fin n) (Fin (ell * m)) (ZMod q))
    (f : RestrictedDec.Circuit) : List (Matrix (Fin n) (Fin m) (ZMod q)) :=
  f.gates.foldl (fun ws g => ws ++
    [gadget q n m - (ws.getD g.1 0) * gadgetInv q n m (ws.getD g.2 0)])
    (List.ofFn fun k : Fin ell => bggInputBlock q n m ell B k.val)

/-- Boolean values of all input and gate wires. -/
def bggWireValues (ell : ℕ) (f : RestrictedDec.Circuit) (x : List Bool) : List Bool :=
  f.gates.foldl (fun ws g => ws ++ [!(ws.getD g.1 false && ws.getD g.2 false)]) x

/-- The block selector from `ell` blocks of `m` columns to its `k`-th block. -/
def bggSelector (q ell m : ℕ) (k : ℕ) : Matrix (Fin (ell * m)) (Fin m) (ZMod q) :=
  Matrix.of fun r j =>
    if (finProdFinEquiv.symm r).1.val = k ∧ (finProdFinEquiv.symm r).2 = j then 1 else 0

/-- Evaluation matrices associated with all wires. -/
def bggWireEvalMatrices (q n m ell : ℕ) (B : Matrix (Fin n) (Fin (ell * m)) (ZMod q))
    (f : RestrictedDec.Circuit) (x : List Bool) : List (Matrix (Fin (ell * m)) (Fin m) (ZMod q)) :=
  let Bs := bggWireMatrices q n m ell B f
  let xs := bggWireValues ell f x
  f.gates.foldl (fun Hs g => Hs ++
    [- (Hs.getD g.1 0) * gadgetInv q n m (Bs.getD g.2 0) -
      bggBit (q := q) (xs.getD g.1 false) • (Hs.getD g.2 0)])
    (List.ofFn fun k : Fin ell => bggSelector q ell m k.val)

/-- The explicit BGG+ NAND-circuit homomorphic evaluation algorithms. -/
def bggHomEval : HomEval where
  evalF q n m ell B f :=
    (bggWireMatrices q n m ell B f).getD (f.outs.headD 0) 0
  evalFX q n m ell B f x :=
    if n = 0 then 0 else
      (bggWireEvalMatrices q n m ell B f x).getD (f.outs.headD 0) 0

end PPSLattice


