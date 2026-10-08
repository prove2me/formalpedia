-- Prove2me | Definitions.Def_LinearExtension_opP
-- name    : LinearExtension_opP
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-05T06:10:47.509547+00:00
-- url     : https://prove2.me/theorems/294e286e-429a-461a-8aa9-10aab12115c3
-- title:
--   The fibered product operation (x,s) ⋄ (y,t) = (x ⋄ y, αs + βt + c) for the linear-extension lemma

import Mathlib.Algebra.Group.Hom.Defs

/-!
# The fibered product operation for the linear-extension lemma

Given a base operation `opG` on `G`, fiber endomorphisms `α β : G → G → (M →+ M)`
and constants `c : G → G → M`, this is the componentwise operation

`(x, s) ⋄ (y, t) = (opG x y, α_{x,y} s + β_{x,y} t + c_{x,y})`

on `G × M` used in the blueprint Chapter 13 "no counterexamples via linear
extension" lemma.
-/

universe u v

namespace LinearExtension

variable {G : Type u} {M : Type v} [AddCommGroup M]

/-- The fibered product operation. -/
def opP (opG : G → G → G) (α β : G → G → (M →+ M)) (c : G → G → M)
    (p q : G × M) : G × M :=
  (opG p.1 q.1, α p.1 q.1 p.2 + β p.1 q.1 q.2 + c p.1 q.1)

@[simp] theorem opP_apply (opG : G → G → G) (α β : G → G → (M →+ M)) (c : G → G → M)
    (p q : G × M) :
    opP opG α β c p q = (opG p.1 q.1, α p.1 q.1 p.2 + β p.1 q.1 q.2 + c p.1 q.1) := rfl

end LinearExtension


