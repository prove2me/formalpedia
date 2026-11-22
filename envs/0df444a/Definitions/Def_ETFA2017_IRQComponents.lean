-- Prove2me | Definitions.Def_ETFA2017_IRQComponents
-- name    : ETFA2017_IRQComponents
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T20:32:17.878297+00:00
-- url     : https://prove2.me/theorems/5036edd6-34d6-4271-ac1c-5a01e49c8adc
-- title:
--   The twelve components of the regular interrupt model
-- statement:
--   The generators in Figures 3–4 and the restrictions in Figures 8–10 and 11(a–f,h) share an eleven-event alphabet. Each participating component must have an outgoing edge. All components start and are marked at their local state zero.
-- source:
--   D. B. de Oliveira, R. S. de Oliveira, T. Cucinotta and L. Abeni, ETFA 2017, Automata-Based Modeling of Interrupts in the Linux PREEMPT RT Kernel.  https://retis.santannapisa.it/~tommaso/publications/ETFA-2017.pdf#page=7

import Definitions.Def_RamadgeWonham_Shared_Generator

/-! IRQ components of de Oliveira et al., ETFA 2017, Figures 3–4, 8–10 and 11. -/

namespace ETFA2017

open RamadgeWonham.Shared

/-- Table II's eleven events for one IRQ vector on one CPU. -/
inductive IRQEvent where
  | irq | irqEntry | irqExit | nmiEntry | nmiExit | disableIRQ | enableIRQ
  | localDisable | localEnable | hwDisable | otherHwDisable
  deriving DecidableEq, Repr

/-- Names refer to the panels as printed; S-numbers are local to each diagram. -/
inductive IRQDiagram where
  | hardware | handler | localMask | vectorMask | hwEntry
  | a | b | c | d | e | f | h
  deriving DecidableEq, Repr

/-- For a label in the diagram's alphabet, list every source/target pair with that label.
An absent label is outside the alphabet and stutters in parallel composition. -/
def IRQDiagram.edges : IRQDiagram → IRQEvent → Option (List (Nat × Nat))
  | .hardware, .irq => some [(0, 0)]
  | .handler, .irqEntry => some [(0, 1)]
  | .handler, .irqExit => some [(1, 0)]
  | .localMask, .localDisable | .localMask, .hwDisable | .localMask, .otherHwDisable =>
      some [(0, 1)]
  | .localMask, .localEnable => some [(1, 0)]
  | .vectorMask, .disableIRQ => some [(0, 1)]
  | .vectorMask, .enableIRQ => some [(1, 0)]
  | .hwEntry, .localEnable => some [(0, 0), (2, 0)]
  | .hwEntry, .hwDisable => some [(0, 2)]
  | .hwEntry, .irqEntry | .hwEntry, .irqExit => some [(2, 2)]
  | .a, .irq => some [(0, 2)]
  | .a, .hwDisable => some [(2, 0)]
  | .b, .localEnable => some [(0, 0)]
  | .b, .hwDisable => some [(0, 2)]
  | .b, .irqEntry => some [(2, 1)]
  | .b, .irqExit => some [(1, 0)]
  | .c, .irq => some [(0, 1)]
  | .c, .irqExit => some [(1, 0)]
  | .d, .hwDisable => some [(0, 0)]
  | .d, .disableIRQ => some [(0, 1)]
  | .d, .enableIRQ => some [(1, 0)]
  | .e, .nmiEntry => some [(0, 1)]
  | .e, .nmiExit => some [(1, 0)]
  | .e, .irq => none
  | .e, _ => some [(0, 0)]
  | .f, .disableIRQ | .f, .enableIRQ => some [(0, 0)]
  | .f, .localEnable => some [(0, 0), (2, 0)]
  | .f, .hwDisable => some [(0, 1)]
  | .f, .irqEntry => some [(1, 0)]
  | .f, .irqExit => some [(0, 2)]
  | .h, .irq => some [(0, 2), (1, 5), (3, 4), (6, 7)]
  | .h, .irqEntry => some [(2, 0)]
  | .h, .disableIRQ => some [(0, 3), (1, 6), (5, 7)]
  | .h, .enableIRQ => some [(3, 0), (4, 2), (6, 1), (7, 5)]
  | .h, .localDisable => some [(0, 1), (3, 6), (4, 7)]
  | .h, .otherHwDisable => some [(0, 1), (2, 5), (3, 6), (4, 7)]
  | .h, .localEnable => some [(0, 0), (1, 0), (2, 2), (3, 3), (4, 4), (5, 2), (6, 3), (7, 4)]
  | _, _ => none

/-- Partial local step, lifted to the union alphabet. -/
def IRQDiagram.step (diagram : IRQDiagram) (e : IRQEvent) (q : Nat) : Option Nat :=
  match diagram.edges e with
  | none => some q
  | some pairs => pairs.lookup q

/-- Coordinate order of the synchronous product. Each component's sole marker is S0. -/
def irqDiagrams : List IRQDiagram :=
  [.hardware, .handler, .localMask, .vectorMask, .hwEntry, .a, .b, .c, .d, .e, .f, .h]

/-- Initially each component is at the state with the incoming initial arrow. -/
def initialComponents : List Nat := List.replicate irqDiagrams.length 0

/-- Simultaneously take all participating transitions on an event. A malformed product
coordinate list gives no successor. -/
def stepDiagrams (e : IRQEvent) : List IRQDiagram → List Nat → Option (List Nat)
  | [], [] => some []
  | diagram :: ds, q :: qs => do
    let r ← diagram.step e q
    let rs ← stepDiagrams e ds qs
    return r :: rs
  | _, _ => none

/-- Transition in the synchronous product of the published IRQ components. -/
def componentStep (e : IRQEvent) := stepDiagrams e irqDiagrams

/-- The joint marker is the tuple of the individual markers. -/
def componentMarked (qs : List Nat) : Bool := qs == initialComponents

/-- The generator whose reachable part is compared with Figure 11(g). -/
def irqComponents : Generator IRQEvent where
  Q := List Nat
  δ := componentStep
  q0 := initialComponents
  Qm := {qs | componentMarked qs = true}

/-- A hardware mask reserves the local interrupt line until handler return. The local mask
is S1 in Figure 8; Figure 11(b) is waiting for handler entry (S2) or return (S1). -/
def irqReserved (q : List Nat) : Prop :=
  q[2]? = some 1 ∧ (q[6]? = some 2 ∨ q[6]? = some 1)

end ETFA2017


