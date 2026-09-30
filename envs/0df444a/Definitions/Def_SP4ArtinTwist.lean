-- Prove2me | Definitions.Def_SP4ArtinTwist
-- name    : SP4ArtinTwist
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-08T02:03:05.774782+00:00
-- url     : https://prove2.me/theorems/3ce1c1e5-7dc9-4b16-9abd-790f981d6645
-- title:
--   The two-strand Artin action on group-valued pairs
-- statement:
--   For any group $G$, the Artin action is the permutation of $G\times G$ given by $A(a,b)=(aba^{-1},a)$. Its inverse is $A^{-1}(a,b)=(b,b^{-1}ab)$. Define the full-twist permutation by $T=A^2$. Integer powers of $T$ use this actual invertible action. This is an algebraic interface on pairs of group elements; no identification with a knot group, tangle complement, or covering space is included.
--
--   $$
--   A(a,b)=(aba^{-1},a),\qquad A^{-1}(a,b)=(b,b^{-1}ab),\qquad T=A^2.
--   $$
-- source:
--   Local research note, Cycle 9, Finite-cover counts in a fixed full-twist family, Proof: the displayed Artin generator, its square, and the paragraph deriving (ab)^30=1 for same-parity S5 images. Independent critical audit, Sections 1 and 3. Only these local group-algebra assertions are formalized; representation gluing and cover-count periodicity are excluded. Source note cycle9_twist_cover_periodicity.md, SHA-256 c4b995489cb5910bd0a9371cf5e6e272c56672116851a613c46eab69a5d82408.

import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Tactic.Group

set_option autoImplicit false

namespace SP4ArtinTwist

/-- The two-strand Artin action on a pair of elements of any group.
The inverse is `(a,b) ↦ (b,b⁻¹ab)`. -/
def artin (G : Type*) [Group G] : Equiv.Perm (G × G) where
  toFun p := (p.1 * p.2 * p.1⁻¹, p.1)
  invFun p := (p.2, p.2⁻¹ * p.1 * p.2)
  left_inv := by
    rintro ⟨a, b⟩
    apply Prod.ext <;> simp [mul_assoc]
  right_inv := by
    rintro ⟨a, b⟩
    apply Prod.ext <;> simp [mul_assoc]

/-- One full twist is two applications of the Artin generator. -/
def fullTwist (G : Type*) [Group G] : Equiv.Perm (G × G) := artin G ^ (2 : ℕ)

end SP4ArtinTwist


