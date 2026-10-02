-- Prove2me | Definitions.Def_CookPvsNP_CompFrames
-- name    : CookPvsNP_CompFrames
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T08:12:04.634733+00:00
-- url     : https://prove2.me/theorems/70bebc73-0610-4a56-921d-b62177c808e7
-- title:
--   Finite first-phase configurations of the Cook composite machine
-- statement:
--   Cells store two optional tape symbols and the published administrative markers. The first-phase representation places a source configuration on track one, keeps track two blank, and appends a right-boundary sentinel just beyond its finite right list. It also names the unmarked cell and the boundary symbols used in the second phase. These are finite-data representations of the existing machine, with no correctness or time assumption.
-- source:
--   New auxiliary result derived from Sneed's exact published Prove2Me definition CookPvsNP_comp_machine, id 9c26b5f3-2f9d-4c5d-9194-692cbc786b4a (2026-09-30), without changing its transitions. It supports the existing CookPvsNP.tm_compose_poly_witness for the scheduling-hardness mission. The underlying one-tape machine model is Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This particular representation and its equations are new formalization lemmas, not numbered claims of that paper.

import Definitions.Def_CookPvsNP_comp_machine

set_option autoImplicit false

namespace CookPvsNP

/-- A cell with arbitrary track contents and no administrative markers. -/
def CompCell.plain {Γ₁ Γ₂ : Type} (a : Option Γ₁) (b : Option Γ₂) :
    Option (CompCell Γ₁ Γ₂) :=
  CompCell.pack ⟨a, b, false, false, false, false, false⟩

def CompCell.firstSymbol {Γ₁ Γ₂ : Type} (a : Option Γ₁) : Option (CompCell Γ₁ Γ₂) :=
  CompCell.plain a none

def CompCell.secondSymbol {Γ₁ Γ₂ : Type} (b : Option Γ₂) : Option (CompCell Γ₁ Γ₂) :=
  CompCell.plain none b

def CompCell.rightMarker {Γ₁ Γ₂ : Type} : Option (CompCell Γ₁ Γ₂) :=
  some { CompCell.blank with rightB := true }

def CompCell.leftMarker {Γ₁ Γ₂ : Type} (a : Option Γ₁) : Option (CompCell Γ₁ Γ₂) :=
  some { (CompCell.blank : CompCell Γ₁ Γ₂) with one := a, leftB := true }

/-- Exact first-phase representation, with a right sentinel after the finite source tape. -/
def compFirstCfg {Γ₁ Γ₂ Q₁ Q₂ : Type} (c : Cfg Γ₁ Q₁) :
    Cfg (CompCell Γ₁ Γ₂) (CompQ Q₁ Q₂) where
  state := .sim₁ c.state
  left := c.left.map CompCell.firstSymbol
  head := CompCell.firstSymbol c.head
  right := c.right.map CompCell.firstSymbol ++ [CompCell.rightMarker]

end CookPvsNP


