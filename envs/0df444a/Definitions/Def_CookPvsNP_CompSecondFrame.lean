-- Prove2me | Definitions.Def_CookPvsNP_CompSecondFrame
-- name    : CookPvsNP_CompSecondFrame
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T08:29:38.560886+00:00
-- url     : https://prove2.me/theorems/a2059740-a9c1-4e04-bebc-2766d3f73640
-- title:
--   Decorated finite second-phase configurations of the Cook composite machine
-- statement:
--   A second-phase configuration keeps both track values at every active cell, a left-boundary first-track value, old first-track data beyond that boundary, and explicit blank padding beyond the right boundary. Projection reads the second track as a source-machine configuration. The administrative update follows a source transition, moves the appropriate boundary when necessary, and preserves the old data. Encoding places this data into the original composite machine. The update is a finite description for proofs; its correspondence with machine transitions is a separate theorem.
-- source:
--   New auxiliary result derived from Sneed's exact published Prove2Me definition CookPvsNP_comp_machine, id 9c26b5f3-2f9d-4c5d-9194-692cbc786b4a (2026-09-30), without changing its transitions. It supports the existing CookPvsNP.tm_compose_poly_witness for the scheduling-hardness mission. The underlying one-tape machine model is Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This particular representation and its equations are new formalization lemmas, not numbered claims of that paper.

import Definitions.Def_CookPvsNP_CompFrames

set_option autoImplicit false

namespace CookPvsNP

/-- The second simulation keeps arbitrary first-track data, a left boundary with
old first-track garbage beyond it, and explicit blank padding beyond the right boundary. -/
structure CompSecondFrame (Γ₁ Γ₂ Q : Type) where
  state : Q
  left : List (Option Γ₁ × Option Γ₂)
  head : Option Γ₁ × Option Γ₂
  right : List (Option Γ₁ × Option Γ₂)
  leftMark : Option Γ₁
  garbage : List (Option Γ₁)
  padding : ℕ

def CompSecondFrame.source {Γ₁ Γ₂ Q : Type} (c : CompSecondFrame Γ₁ Γ₂ Q) : Cfg Γ₂ Q where
  state := c.state
  left := c.left.map Prod.snd
  head := c.head.2
  right := c.right.map Prod.snd

def CompSecondFrame.encode {Γ₁ Γ₂ Q₁ Q₂ : Type} (c : CompSecondFrame Γ₁ Γ₂ Q₂) :
    Cfg (CompCell Γ₁ Γ₂) (CompQ Q₁ Q₂) where
  state := .sim₂ c.state
  left := c.left.map (fun p => CompCell.plain p.1 p.2) ++
    CompCell.leftMarker c.leftMark :: c.garbage.map CompCell.firstSymbol
  head := CompCell.plain c.head.1 c.head.2
  right := c.right.map (fun p => CompCell.plain p.1 p.2) ++
    CompCell.rightMarker :: List.replicate c.padding none

/-- An administrative update of the frame corresponding to a source-machine step.
This is a finite-data description for proofs, not a replacement for the original machine. -/
def CompSecondFrame.step {Γ₁ Γ₂ : Type} (M : TM Γ₂)
    (c : CompSecondFrame Γ₁ Γ₂ M.Q) : CompSecondFrame Γ₁ Γ₂ M.Q :=
  if M.IsHalting c.source then c else
    match M.δ c.state c.head.2 with
    | (q, w, .left) =>
      match c.left with
      | [] => { c with
          state := q
          head := (c.leftMark, none)
          right := (c.head.1, w) :: c.right
          leftMark := c.garbage.headD none
          garbage := c.garbage.tail }
      | a :: left => { c with
          state := q
          left := left
          head := a
          right := (c.head.1, w) :: c.right }
    | (q, w, .right) =>
      match c.right with
      | [] => { c with
          state := q
          left := (c.head.1, w) :: c.left
          head := (none, none)
          padding := c.padding - 1 }
      | a :: right => { c with
          state := q
          left := (c.head.1, w) :: c.left
          head := a
          right := right }

end CookPvsNP


