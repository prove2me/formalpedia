-- Prove2me | Definitions.Def_CatalyticTreeEval_Main_BitRepresentation
-- name    : CatalyticTreeEval_Main_BitRepresentation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:26:56.110193+00:00
-- url     : https://prove2.me/theorems/4cfe6f68-b669-494c-be11-46b755b7ed82
-- title:
--   Valid-shift search and quotient-preserving catalytic ring blocks
-- statement:
--   For $d>0,m>1$, use $3d$ blocks of width $B=\lceil\log_2(3dm)\rceil+1$. Set $K=\lfloor2^B/m\rfloor$. A block $z$ is valid when $z<Km$. Exhaustive search returns the first shift $\Delta$ for which every $(z_i+\Delta)\bmod2^B$ is valid, returning failure if none is found.
--
--   For a valid shifted block $z=qm+r$, a residue update by $c\in\mathbb Z/m\mathbb Z$ is
--
--   $$z\longmapsto qm+(r+c\bmod m).$$
--
--   The quotient stays unchanged. The definitions do not presume that arbitrary initial blocks are valid or that the search succeeds. Success, charged simulation and exact restoration are obligations of the catalytic simulation theorem.
--
--   This is the concrete representation used to recover the original bits after ring-register restoration.
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Remark 3.3, printed p. 14 (PDF p. 16); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_Matching

set_option autoImplicit false

namespace CatalyticTreeEval.Main

/-- Remark 3.3: ceil(log₂(3dm))+1 for positive d and m>1. -/
def blockWidth (d m : ℕ) : ℕ := Nat.log 2 (3 * d * m - 1) + 2

def blockRange (d m : ℕ) : ℕ := 2 ^ blockWidth d m

def validBlock (d m z : ℕ) : Prop := z < (blockRange d m / m) * m

def shiftBlock (d m Δ z : ℕ) : ℕ := (z + Δ) % blockRange d m

/-- Exhaustive search, with failure represented as none rather than a presumed valid shift. -/
def findShift (d m : ℕ) (z : Fin (3 * d) → ℕ) : Option ℕ :=
  (List.range (blockRange d m)).find? fun Δ =>
    (List.finRange (3 * d)).all fun i => decide (shiftBlock d m Δ (z i) < (blockRange d m / m) * m)

/-- Modular register updates preserve the quotient of each valid binary block. -/
def updateBlock (m z : ℕ) (c : ZMod m) : ℕ :=
  z / m * m + ((z % m : ZMod m) + c).val

end CatalyticTreeEval.Main


