-- Prove2me | Definitions.Def_CookPvsNP_CompCleanup
-- name    : CookPvsNP_CompCleanup
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T08:46:55.181679+00:00
-- url     : https://prove2.me/theorems/fa0e5403-7d5e-48cc-a373-d6d44e6fc54a
-- title:
--   Finite terminal configuration of the Cook composite cleanup
-- statement:
--   The cleanup mask retains symbols until the first blank and replaces the remaining cells with blanks. The terminal configuration erases the first track from the output, clears administrative markers, and retains explicit blank padding. These are definitions only; the exact machine run and its output preservation are proved separately.
-- source:
--   New auxiliary result derived from Sneed's exact published Prove2Me definition CookPvsNP_comp_machine, id 9c26b5f3-2f9d-4c5d-9194-692cbc786b4a (2026-09-30), without changing its transitions. It supports the existing CookPvsNP.tm_compose_poly_witness for the scheduling-hardness mission. The underlying one-tape machine model is Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This particular representation and its equations are new formalization lemmas, not numbered claims of that paper.

import Definitions.Def_CookPvsNP_CompSecondFrame

set_option autoImplicit false

namespace CookPvsNP

/-- Keep symbols up to the first blank; retain the original list length using blanks. -/
def compCleanTail {Γ : Type} : Bool → List (Option Γ) → List (Option Γ)
  | _, [] => []
  | ended, b :: rest => (if ended then none else b) :: compCleanTail (ended || b.isNone) rest

def CompCell.finalMarker {Γ₁ Γ₂ : Type} (b : Option Γ₂) : Option (CompCell Γ₁ Γ₂) :=
  some ⟨none, b, false, false, false, false, true⟩

/-- The entire finite configuration produced by the final cleanup phase. -/
def compCleanCfg {Γ₁ Γ₂ Q₁ Q₂ : Type} (c : CompSecondFrame Γ₁ Γ₂ Q₂) :
    Cfg (CompCell Γ₁ Γ₂) (CompQ Q₁ Q₂) where
  state := .haltAccept
  left := (CompSecondFrame.encode (Q₁ := Q₁) c).left
  head := CompCell.secondSymbol c.head.2
  right := (compCleanTail c.head.2.isNone (c.right.map Prod.snd)).map CompCell.secondSymbol ++
    List.replicate (c.padding + 1) none

end CookPvsNP


