-- Prove2me | Definitions.Def_Kyprianou_Ch06_RegularityAtFirstEntrance
-- name    : Kyprianou_Ch06_RegularityAtFirstEntrance
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:00:51.250048+00:00
-- url     : https://prove2.me/theorems/32d456b4-f346-4e12-97b9-f6dcdf961cad
-- title:
--   Definition 6.4: regular and irregular entrance at time zero
-- statement:
--   For a real Lévy process started at a point x, define the first strictly positive time of entry into a target open or closed B. The point is regular for B when the probability of an immediate entry (entrance time zero) is one, and irregular when that probability is zero. The first entrance is infinity if no entry occurs.
-- source:
--   Kyprianou (2006), first edition, Definition 6.4, printed p. 142; physical two-up PDF p. 76.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- The product-sum sigma algebra for a type with one cemetery element. -/
instance {α : Type} [MeasurableSpace α] :
    MeasurableSpace (Option α) :=
  MeasurableSpace.comap
    (fun x : Option α =>
      match x with
      | none => (Sum.inl () : Unit ⊕ α)
      | some a => Sum.inr a)
    inferInstance

/-- The strict-initiating-time entrance time into B for a process X
started at spatial point x. The empty infimum is infinity. -/
noncomputable def firstEntranceTime
    {Omega : Type} (X : NNReal → Omega → Real)
    (x : Real) (B : Set Real) (omega : Omega) : WithTop NNReal :=
  sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
    {t : NNReal | 0 < t ∧ x + X t omega ∈ B})

/-- Definition 6.4: regularity is an almost-sure zero strictly-positive
entrance time for the process started at x. -/
def IsRegularFor
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : NNReal → Omega → Real)
    (x : Real) (B : Set Real) : Prop :=
  P {omega : Omega | firstEntranceTime X x B omega = 0} = 1

/-- Definition 6.4: irregularity means zero probability of immediate
entry, not merely the negation of full-probability regularity. -/
def IsIrregularFor
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : NNReal → Omega → Real)
    (x : Real) (B : Set Real) : Prop :=
  P {omega : Omega | firstEntranceTime X x B omega = 0} = 0

end Kyprianou.Ch06


