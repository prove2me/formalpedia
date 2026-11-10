-- Prove2me | Definitions.Def_NetworkSumSecure_Solvability_transformation
-- name    : NetworkSumSecure_Solvability_transformation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T05:04:14.230864+00:00
-- url     : https://prove2.me/theorems/c34a4731-e4f0-473b-b813-091213c06260
-- title:
--   Invertible private user-block transformations
-- statement:
--   For each user $i$, an invertible $F$-linear map $B_i$ acts on the $1+z_i$ message-and-key coordinates of that user. The resulting block-diagonal transformation $\widehat B$ acts by
--
--   $$(\widehat Bv)^{(i)}=B_i v^{(i)}.$$
--
--   An invertible linear map on these finite coordinate spaces is represented equivalently by its invertible matrix in the standard basis. Blocks never mix different users, and the private-key assignment remains $z$. This is the transformation interface for Theorem 6; it asserts no existence or feasibility property.
-- source:
--   Yang Bai, Xuan Guang, Lizhi Wang, STOC 2027 submission #1291 (October 2026), pp. 13–14 (PDF pp. 15–16), §4.2, block-diagonal transformation preceding Theorem 6

import Mathlib
import Definitions.Def_NetworkSumSecure_Solvability_algebra

namespace NetworkSumSecure.Solvability

/-! §4.2, printed pp.13–14 (PDF 15–16): invertible blocks act separately on users.
An invertible linear map of a finite coordinate space is its invertible matrix in
the standard basis. No change in the private-key assignment occurs. -/

variable {U F : Type} [Field F] {z : U → ℕ}

abbrev UserBlocks (F : Type) [Field F] (z : U → ℕ) :=
  (i : U) → (Option (Fin (z i)) → F) ≃ₗ[F] (Option (Fin (z i)) → F)

/-- Multiplication by the block-diagonal matrix B-hat, with blocks B_i. -/
def blockApply (B : UserBlocks F z) (v : Coord z → F) : Coord z → F :=
  fun c => B c.1 (fun d => v ⟨c.1, d⟩) c.2

end NetworkSumSecure.Solvability


