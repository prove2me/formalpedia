-- Prove2me | Definitions.Def_MinrankTW_relOfBlocks
-- name    : MinrankTW_relOfBlocks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:50.338312+00:00
-- url     : https://prove2.me/theorems/3ce330a4-7d6b-46e1-b106-4d4c4988911a
-- title:
--   Linear relation of one side of a separated matrix
-- statement:
--   For blocks $A$ (interior rows $\times$ interior columns), $U$ (interior rows $\times$ boundary columns), $V$ (boundary rows $\times$ interior columns) and $W$ (boundary rows $\times$ boundary columns), with $a$ boundary columns and $c$ boundary rows,
--   $$
--   R=\{(x,y)\in\mathbb F^a\oplus\mathbb F^c : \exists x',\ Ax'+Ux=0,\ y=Vx'+Wx\},
--   $$
--   where $x'$ has one coordinate per column of $A$. The blocks may be rectangular. This is the relation $R_i$ of Lemma 1.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Lemma 1, p.10 (also Section 2.1, p.6)

import Mathlib

namespace MinrankTW

open Matrix

/-- The linear relation of one side of a separated matrix (Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), Lemma 1, p.10; also §2.1,
p.6): for blocks `A` (interior rows × interior columns), `U` (interior rows × boundary
columns), `V` (boundary rows × interior columns) and `W` (boundary rows × boundary columns),
`R = {(x, y) : ∃ x', A x' + U x = 0, y = V x' + W x}`, where `x'` has one coordinate per
column of `A`.

**Formalization Note** The blocks may be rectangular: interior rows `ι`, interior columns
`κ`, boundary columns `β` (the `x`-coordinates) and boundary rows `ρ` (the
`y`-coordinates). The relation is written as the image of the kernel of
`(x', x) ↦ A x' + U x` under `(x', x) ↦ (x, V x' + W x)`. -/
def relOfBlocks {F : Type*} [Field F] {ι κ β ρ : Type*} [Fintype κ] [Fintype β]
    (A : Matrix ι κ F) (U : Matrix ι β F) (V : Matrix ρ κ F) (W : Matrix ρ β F) :
    Submodule F ((β → F) × (ρ → F)) :=
  (LinearMap.ker ((A.mulVecLin).coprod (U.mulVecLin))).map
    ((LinearMap.snd F (κ → F) (β → F)).prod ((V.mulVecLin).coprod (W.mulVecLin)))

end MinrankTW


