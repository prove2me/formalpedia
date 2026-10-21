-- Prove2me | Definitions.Def_LeanTT2_spec
-- name    : LeanTT2_spec
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T02:15:16.018608+00:00
-- url     : https://prove2.me/theorems/6d723e72-e883-49f6-ba5b-80809876f1ef
-- title:
--   Inductive specifications and their W-type realizations
-- statement:
--   The W-oriented inductive-specification interface for the W-type reduction of thesis chapter 5. The structure IndSpec records an inductive definition in the form the reduction needs: a defining context, a number of constructors, and for each constructor a seed type packing its non-recursive arguments, a branching family over the seed into the universe indexing its recursive arguments, the constructor type as an element of the universe, together with the recursor's target type, a per-constructor step function, a smallness flag, and the typing axioms of these data. The structure Realizes records a W-type presentation of a specification: a seed type, a branching family, the realized type, the constructors, and the eliminator. The predicate RealizesOK states the correctness of a presentation: the seed is a type and the branching family is typed at the function type into the universe; the realized type is a type and is definitionally the W-type of the presentation; every constructor is typed at its specification type; every constructor's seed embeds into the seed type with branching definitionally equal to the constructor's family; the eliminator is typed at the function type from the realized type to the recursor target; the iota rule holds for every constructor on every argument; and small specifications realize to types whose propositional truncation is a proposition.
-- source:
--   M. Carneiro, The Type Theory of Lean, 2019, sections 2.6.1 and 5.1-5.4 (pp. 9, 27-32).

import Mathlib
import Definitions.Def_LeanTT2_frag

universe u

/-!
# The Type Theory of Lean, part II: inductive specifications and W-type realizations

The inductive-specification interface for the W-type reduction of Mario
Carneiro's thesis "The Type Theory of Lean" (Carnegie Mellon University,
2019), chapter 5. Thesis section 2.6.1 defines an inductive type by a
list of constructors, each carrying a telescope of arguments; thesis
section 5.1 (page 27) observes that the telescopes can be packed into
sigma types and the constructors into sums, leaving a single W-type
`W x : A. B` with its supremum constructor and recursor as the only
genuinely inductive datum. The structure `IndSpec` records an inductive
definition in the form needed for this reduction: per constructor a seed
type (the packed non-recursive telescope), a branching family into the
universe (the recursive arguments of the constructor), the constructor
type, a step function for the recursor, and the recursor's target type,
together with a flag marking specifications whose realized type must be
a subsingleton after truncation. The structure `Realizes` records a
W-type presentation of a specification, and the predicate `RealizesOK`
states that the presentation is correct: the presentation types are
types, the realized type is definitionally the W-type, the constructors
and eliminator are typed, every constructor's branching is covered, the
iota rule of thesis section 2.6.4 holds for every constructor, and small
specifications give propositions after truncation.
-/

namespace LeanTT2

/-- An inductive specification inside the fragment, in the W-oriented
form of thesis chapter 5: `n` constructors; constructor `i` carries the
seed type `SN i` (the packed non-recursive argument telescope of thesis
section 5.1, page 27) and the branching family `SR i : SN i → Univ` (the
recursive arguments of constructor `i`, indexed by the seed); `CTy i` is
the full constructor type as an element of the universe; `RecTy` is the
recursor's target type; `step i` is the recursor's step function for
constructor `i`; and `small` marks the specifications whose realized type
must be a subsingleton after propositional truncation (thesis section
5.3, page 31). The remaining fields are the typing axioms of these data.
-/
structure IndSpec (F : Frag.{u}) where
  /-- the defining context of the inductive definition -/
  Γ : F.Ctx
  /-- the defining context is valid -/
  hΓ : F.ok Γ
  /-- the number of constructors -/
  n : ℕ
  /-- the seed type of constructor i, packing its non-recursive arguments -/
  SN : Fin n → F.E
  /-- the branching family of constructor i: its recursive arguments,
  indexed by the seed -/
  SR : Fin n → F.E
  /-- the type of constructor i, as an element of the universe -/
  CTy : Fin n → F.E
  /-- the target type of the recursor, as an element of the universe -/
  RecTy : F.E
  /-- the recursor's step function for constructor i -/
  step : Fin n → F.E
  /-- whether the realized type must be a subsingleton after truncation -/
  small : Bool
  /-- the seed types are types -/
  hSN : ∀ i, F.isType Γ (SN i)
  /-- the branching families are type families over the seeds -/
  hSR : ∀ i, F.ty Γ (SR i) (F.piT (SN i) F.Univ)
  /-- the constructor types are elements of the universe -/
  hCTy : ∀ i, F.ty Γ (CTy i) F.Univ
  /-- the recursor target is an element of the universe -/
  hRecTy : F.ty Γ RecTy F.Univ
  /-- the step functions map constructor arguments to the target type -/
  hstep : ∀ i, F.ty Γ (step i) (F.piT (CTy i) RecTy)

/-- A W-type realization of an inductive specification: a seed type `A`
aggregating the constructors' seeds, a branching family `B : A → Univ`,
the realized inductive type `W` (definitionally the W-type `wT A B` of
the fragment), the constructors, and the eliminator. -/
structure Realizes (F : Frag.{u}) (Sp : IndSpec F) where
  /-- the seed type of the W-presentation -/
  A : F.E
  /-- the branching family of the W-presentation -/
  B : F.E
  /-- the realized inductive type -/
  W : F.E
  /-- the constructors of the realized type -/
  ctor : Fin Sp.n → F.E
  /-- the eliminator (recursor) of the realized type -/
  elim : F.E

/-- The correctness predicate for a W-type realization (thesis sections
5.2 to 5.4, pages 29 to 32): the presentation types are types, the
realized type is definitionally the W-type `wT A B`, every constructor
is typed at its specification type, every constructor's branching is
covered by the presentation, the eliminator is typed at the recursor
type, the iota rule of thesis section 2.6.4 (page 12) holds for every
constructor, and small specifications produce propositions after
truncation. -/
def RealizesOK (F : Frag.{u}) (Sp : IndSpec F) (R : Realizes F Sp) : Prop :=
  F.isType Sp.Γ R.A ∧
  F.ty Sp.Γ R.B (F.piT R.A F.Univ) ∧
  F.isType Sp.Γ R.W ∧
  F.deq Sp.Γ R.W (F.wT R.A R.B) ∧
  (∀ i, F.ty Sp.Γ (R.ctor i) (Sp.CTy i)) ∧
  (∀ i, ∃ c, F.ty Sp.Γ c (F.piT (Sp.SN i) R.A) ∧
    ∀ a, F.deq Sp.Γ (F.app R.B (F.app c a)) (F.app (Sp.SR i) a)) ∧
  F.ty Sp.Γ R.elim (F.piT R.W Sp.RecTy) ∧
  (∀ (i : Fin Sp.n) (x : F.E),
    F.red Sp.Γ (F.app R.elim (F.app (R.ctor i) x)) (F.app (Sp.step i) x)) ∧
  (Sp.small = true → F.isProp Sp.Γ (F.truncT R.W))

end LeanTT2


