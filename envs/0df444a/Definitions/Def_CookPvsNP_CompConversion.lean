-- Prove2me | Definitions.Def_CookPvsNP_CompConversion
-- name    : CookPvsNP_CompConversion
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T08:47:08.71535+00:00
-- url     : https://prove2.me/theorems/8ded5a31-e9e5-4484-819b-fae0174ea205
-- title:
--   Finite word configurations and converted second-machine frames
-- statement:
--   A word configuration consists of an encoded ordinary word followed by finitely many blanks. A converted frame stores the same word on both tracks through the intermediate embeddings, with the second machine's initial state, a left boundary, old first-track data, and blank padding. No assertion of reachability or runtime is included in these definitions.
-- source:
--   New auxiliary result derived from Sneed's exact published Prove2Me definition CookPvsNP_comp_machine, id 9c26b5f3-2f9d-4c5d-9194-692cbc786b4a (2026-09-30), without changing its transitions. It supports the existing CookPvsNP.tm_compose_poly_witness for the scheduling-hardness mission. The underlying one-tape machine model is Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This particular representation and its equations are new formalization lemmas, not numbered claims of that paper.

import Definitions.Def_CookPvsNP_CompSecondFrame

set_option autoImplicit false

namespace CookPvsNP

/-- A source configuration with an encoded output word and explicit trailing blanks. -/
def compWordCfg {I Γ Q : Type} (ι : I ↪ Γ) (q : Q) (left : List (Option Γ))
    (w : List I) (padding : ℕ) : Cfg Γ Q where
  state := q
  left := left
  head := (w.map (some ∘ ι)).headD none
  right := (w.map (some ∘ ι)).tail ++ List.replicate padding none

/-- Mark the origin of the second simulation without altering either track. -/
def CompCell.originSymbol {A B : Type} (a : Option A) (b : Option B) :
    Option (CompCell A B) := some ⟨a, b, false, false, false, true, false⟩

/-- The second-phase frame after translating the first source's output word. -/
def compConvertedFrame {I A B Q : Type} (ι₁ : I ↪ A) (ι₂ : I ↪ B) (q : Q)
    (left : List (Option A)) (w : List I) (padding : ℕ) : CompSecondFrame A B Q where
  state := q
  left := []
  head := (w.map (fun x => (some (ι₁ x), some (ι₂ x)))).headD (none, none)
  right := (w.map (fun x => (some (ι₁ x), some (ι₂ x)))).tail
  leftMark := left.headD none
  garbage := left.tail
  padding := padding

end CookPvsNP


