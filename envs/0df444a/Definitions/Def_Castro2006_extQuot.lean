-- Prove2me | Definitions.Def_Castro2006_extQuot
-- name    : Castro2006_extQuot
-- status  : Definition
-- author  : @LG
-- created : 2026-11-18T19:59:46.481819+00:00
-- url     : https://prove2.me/theorems/ecc95232-0b0a-43ad-addf-2d88f5bddebc
-- title:
--   Equivalence classes of extensions inducing a fixed action
-- statement:
--   The quotient of extensions inducing a fixed action by equivalence of extensions.

import Mathlib
import Definitions.Def_Castro2006_extClasses
open CategoryTheory

namespace Castro2006
variable {G N : Type} [Group G] [CommGroup N]

/-- Two extensions inducing `φ` are related when they are equivalent as extensions. -/
def ExtRel (φ : G →* MulAut N) (x y : ExtOf φ) : Prop :=
  letI := x.grp
  letI := y.grp
  Nonempty (x.S.Equiv y.S)

def extSetoid (φ : G →* MulAut N) : Setoid (ExtOf φ) where
  r := ExtRel φ
  iseqv := by
    constructor
    · intro x
      letI := x.grp
      exact ⟨GroupExtension.Equiv.refl x.S⟩
    · intro x y h
      letI := x.grp
      letI := y.grp
      obtain ⟨e⟩ := h
      exact ⟨e.symm⟩
    · intro x y z hxy hyz
      letI := x.grp
      letI := y.grp
      letI := z.grp
      obtain ⟨e₁⟩ := hxy
      obtain ⟨e₂⟩ := hyz
      exact ⟨e₁.trans e₂⟩

/-- Equivalence classes of extensions of `G` by `N` inducing the action `φ`. -/
def ExtClasses (φ : G →* MulAut N) : Type 1 := Quotient (extSetoid φ)

end Castro2006


