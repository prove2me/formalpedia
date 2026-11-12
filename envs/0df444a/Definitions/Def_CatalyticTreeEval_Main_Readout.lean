-- Prove2me | Definitions.Def_CatalyticTreeEval_Main_Readout
-- name    : CatalyticTreeEval_Main_Readout
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:31:40.490042+00:00
-- url     : https://prove2.me/theorems/909554de-2f7c-455f-85a0-6b1c2e543be2
-- title:
--   Packed full-label output family and decoding
-- statement:
--   For a valid frame, put $b=\lfloor\log_2m\rfloor$ and $E=\lceil\ell/b\rceil$. Pad the dimension to at least $E$. A label $y<2^\ell$ is represented by its consecutive $b$-bit blocks in the first $E$ coordinates, with zero remaining coordinates:
--
--   $$\operatorname{enc}(y)_c=\left\lfloor y/2^{cb}\right\rfloor\bmod2^b\quad(c<E).$$
--
--   Decoding sums coordinate values times $2^{cb}$ and discards padding above $\ell$ bits. The definitions are total, while their intended use requires the valid-frame assumptions ensuring $m>1$. On actual encoded labels every block is smaller than $m$.
--
--   This supplies a concrete output family for the complete root label. The machine theorem must still read the masked differences, emit every bit and perform the restoring second root run.
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Section 4.3, readout and restoration, printed p. 25 (PDF p. 27); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_Framework

set_option autoImplicit false

namespace CatalyticTreeEval.Main

def outputBlocks (F : Frame) : ℕ := (F.l + Nat.log 2 F.m - 1) / Nat.log 2 F.m

/-- The explicit packed output family of §4.3. -/
def readoutEncoding (F : Frame) (y : Label F.l) : Vec F.m (paddedDimension F) :=
  fun c => if c.val < outputBlocks F then
    ((y.val / 2 ^ (c.val * Nat.log 2 F.m) % 2 ^ Nat.log 2 F.m : ℕ) : ZMod F.m)
    else 0

/-- Decode packed low-order blocks; padding beyond the label is discarded. -/
def readoutDecode (F : Frame) (v : Vec F.m (paddedDimension F)) : Label F.l :=
  ⟨(∑ c, (v c).val * 2 ^ (c.val * Nat.log 2 F.m)) % 2 ^ F.l,
    Nat.mod_lt _ (by positivity)⟩


end CatalyticTreeEval.Main


