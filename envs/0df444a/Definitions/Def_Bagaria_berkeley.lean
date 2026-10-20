-- Prove2me | Definitions.Def_Bagaria_berkeley
-- name    : Bagaria_berkeley
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-19T23:06:31.611907+00:00
-- url     : https://prove2.me/theorems/cdfae1fc-49b0-4ccd-a82c-4cca8458a272
-- title:
--   The Berkeley hierarchy: proto-Berkeley, Berkeley, and club Berkeley cardinals
-- statement:
--   The Berkeley hierarchy of large cardinals beyond Choice, the strongest forms known. A transitive set is a collection of elements of the universe closed under membership. An ordinal δ is a proto-Berkeley cardinal when every transitive set containing the code of δ carries a non-trivial elementary self-embedding with critical point below δ; δ is a Berkeley cardinal when the critical point can moreover be placed strictly between any given η below δ and δ itself. A club subset of δ is a set of ordinals below δ that is unbounded in δ and closed under the suprema of its bounded initial parts; δ is regular when every unbounded set of ordinals below δ has cardinality at least that of δ; δ is club Berkeley when it is regular and for every club C and every transitive set containing the code of δ, some non-trivial elementary self-embedding of the transitive set has critical point in C; and δ is limit club Berkeley when it is club Berkeley and a limit of Berkeley cardinals.
-- source:
--   Bagaria (2017), Large Cardinals beyond Choice, AILA XXVI slides, pp. 12-16, Definitions and Theorems

import Mathlib
import Definitions.Def_Bagaria_arena

universe v

/-!
# Large cardinals beyond Choice: the Berkeley hierarchy

Transitive sets of the universe and their elementary self-embeddings, the
proto-Berkeley, Berkeley, club Berkeley, and limit club Berkeley cardinals,
and the club and regularity notions on the ordinals (slides 12-16 of the
source).
-/

namespace Bagaria

namespace Universe

variable (U : Universe.{v})

/-- M is a transitive set of the universe: a collection of elements of the
carrier closed under the universe's membership (slide 12). -/
def isTransitiveSet (M : Set U.carrier) : Prop :=
  ∀ x : U.carrier, x ∈ M → ∀ y : U.carrier, U.mem y x → y ∈ M

/-- Membership on the elements of the set M, as a first-order structure on
the subtype of M (slide 12). -/
def memOn (M : Set U.carrier) :
    {x : U.carrier // x ∈ M} → {x : U.carrier // x ∈ M} → Prop :=
  fun x y => U.mem x.val y.val

/-- The critical point of a self-embedding of a transitive set: the least
ordinal whose code belongs to M and is moved by the embedding, while the
code of every smaller ordinal in M is fixed. -/
def critIsOn (M : Set U.carrier)
    (j : {x : U.carrier // x ∈ M} → {x : U.carrier // x ∈ M})
    (κ : Ordinal.{v}) : Prop :=
  ∃ hκ : U.ord κ ∈ M,
    j ⟨U.ord κ, hκ⟩ ≠ ⟨U.ord κ, hκ⟩ ∧
    ∀ ν : Ordinal.{v}, ν < κ → ∀ hν : U.ord ν ∈ M,
      j ⟨U.ord ν, hν⟩ = ⟨U.ord ν, hν⟩

/-- δ is a proto-Berkeley cardinal (slide 12): every transitive set that
contains the code of δ carries a non-trivial elementary self-embedding
whose critical point is below δ. -/
def protoBerkeley (δ : Ordinal.{v}) : Prop :=
  ∀ M : Set U.carrier, U.isTransitiveSet M → U.ord δ ∈ M →
    ∃ κ : Ordinal.{v}, ∃ j : {x : U.carrier // x ∈ M} → {x : U.carrier // x ∈ M},
      j ≠ id ∧ IsElementaryOf (U.memOn M) (U.memOn M) j ∧ U.critIsOn M j κ ∧ κ < δ

/-- δ is a Berkeley cardinal (slide 13): every transitive set that
contains the code of δ, and every ordinal η below δ, carry a non-trivial
elementary self-embedding of the transitive set whose critical point lies
strictly between η and δ. -/
def berkeley (δ : Ordinal.{v}) : Prop :=
  ∀ M : Set U.carrier, U.isTransitiveSet M → U.ord δ ∈ M →
    ∀ η : Ordinal.{v}, η < δ →
      ∃ κ : Ordinal.{v}, ∃ j : {x : U.carrier // x ∈ M} → {x : U.carrier // x ∈ M},
        j ≠ id ∧ IsElementaryOf (U.memOn M) (U.memOn M) j ∧ U.critIsOn M j κ ∧
          η < κ ∧ κ < δ

/-- C is a club subset of the ordinal δ: a set of ordinals below δ,
unbounded in δ, and closed under the suprema of its bounded initial parts
(slide 15). -/
def isClubIn (δ : Ordinal.{v}) (C : Set Ordinal.{v}) : Prop :=
  (∀ ν ∈ C, ν < δ) ∧
  (∀ ν : Ordinal.{v}, ν < δ → ∃ μ ∈ C, ν < μ) ∧
  (∀ α : Ordinal.{v}, α < δ →
    (∀ ν : Ordinal.{v}, ν < α → ∃ μ ∈ C, ν < μ ∧ μ < α) → α ∈ C)

/-- The ordinal δ is regular: every set of ordinals that is unbounded in
δ has cardinality at least that of δ (slide 15). -/
def isRegularOrdinal (δ : Ordinal.{v}) : Prop :=
  ∀ S : Set Ordinal.{v},
    (∀ ν ∈ S, ν < δ) →
    (∀ ν : Ordinal.{v}, ν < δ → ∃ μ ∈ S, ν < μ) →
      Cardinal.mk ↥(Set.Iio δ) ≤ Cardinal.mk ↥S

/-- δ is a club Berkeley cardinal (slide 15): δ is regular and for every
club C ⊆ δ and every transitive set containing the code of δ there is a
non-trivial elementary self-embedding of the transitive set whose
critical point lies in C. The club and regularity conditions are
self-contained ordinal notions, so they are used without the universe. -/
def clubBerkeley (δ : Ordinal.{v}) : Prop :=
  isRegularOrdinal δ ∧
  ∀ C : Set Ordinal.{v}, isClubIn δ C →
    ∀ M : Set U.carrier, U.isTransitiveSet M → U.ord δ ∈ M →
      ∃ κ : Ordinal.{v}, ∃ j : {x : U.carrier // x ∈ M} → {x : U.carrier // x ∈ M},
        j ≠ id ∧ IsElementaryOf (U.memOn M) (U.memOn M) j ∧ U.critIsOn M j κ ∧ κ ∈ C

/-- δ' is a Berkeley cardinal below δ: the ambient Berkeley property,
asserted of an ordinal strictly below δ (the form in which the goal states
the conclusion of slide 16). -/
def berkeleyBelow (δ δ' : Ordinal.{v}) : Prop :=
  δ' < δ ∧ U.berkeley δ'

/-- δ is a limit club Berkeley cardinal (slide 16): a club Berkeley
cardinal that is a limit of Berkeley cardinals. -/
def limitClubBerkeley (δ : Ordinal.{v}) : Prop :=
  U.clubBerkeley δ ∧
  ∀ ν : Ordinal.{v}, ν < δ → ∃ ε : Ordinal.{v}, ν < ε ∧ ε < δ ∧ U.berkeley ε

end Universe

end Bagaria


