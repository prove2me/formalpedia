-- Prove2me | Definitions.Def_ETFA2017_IRQFigure
-- name    : ETFA2017_IRQFigure
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T20:33:09.02481+00:00
-- url     : https://prove2.me/theorems/822165a7-8b3c-443a-98c5-f953ede872c4
-- title:
--   The 38-state regular interrupt automaton in Figure 11(g)
-- statement:
--   The partial transition function is transcribed directly from the printed graph. The 38 states are labeled q0 through q37, with q0 as the initial and sole marked state. The handler-active predicate identifies the interval from handler entry to return.
-- source:
--   D. B. de Oliveira, R. S. de Oliveira, T. Cucinotta and L. Abeni, ETFA 2017, Automata-Based Modeling of Interrupts in the Linux PREEMPT RT Kernel.  https://retis.santannapisa.it/~tommaso/publications/ETFA-2017.pdf#page=7

import Definitions.Def_ETFA2017_IRQComponents

/-! The final IRQ automaton in Figure 11(g), ETFA 2017, page 7. The transition
table was read from the arrows and labels in the PDF vector graphic independently
of the component diagrams. Missing entries are undefined. -/

namespace ETFA2017

open RamadgeWonham.Shared

/-- The partial transition function on the 38 printed state labels. -/
def figureStep (e : IRQEvent) (q : Fin 38) : Option (Fin 38) :=
  match q.val, e with
  | 0, .disableIRQ => some 13
  | 0, .irq => some 29
  | 0, .localDisable => some 7
  | 0, .otherHwDisable => some 3
  | 0, .nmiEntry => some 5
  | 1, .irq => some 24
  | 1, .nmiExit => some 36
  | 2, .disableIRQ => some 10
  | 2, .irqExit => some 25
  | 2, .nmiEntry => some 4
  | 3, .disableIRQ => some 28
  | 3, .irq => some 9
  | 3, .localEnable => some 0
  | 3, .nmiEntry => some 6
  | 4, .nmiExit => some 2
  | 5, .irq => some 32
  | 5, .nmiExit => some 0
  | 6, .irq => some 11
  | 6, .nmiExit => some 3
  | 7, .disableIRQ => some 34
  | 7, .irq => some 14
  | 7, .localEnable => some 0
  | 7, .nmiEntry => some 8
  | 8, .irq => some 18
  | 8, .nmiExit => some 7
  | 9, .disableIRQ => some 12
  | 9, .localEnable => some 29
  | 9, .nmiEntry => some 11
  | 10, .enableIRQ => some 2
  | 10, .irqExit => some 36
  | 10, .nmiEntry => some 15
  | 11, .nmiExit => some 9
  | 12, .enableIRQ => some 9
  | 12, .localEnable => some 33
  | 12, .nmiEntry => some 16
  | 13, .enableIRQ => some 0
  | 13, .irq => some 33
  | 13, .localDisable => some 34
  | 13, .otherHwDisable => some 28
  | 13, .nmiEntry => some 17
  | 14, .disableIRQ => some 20
  | 14, .localEnable => some 29
  | 14, .nmiEntry => some 18
  | 15, .nmiExit => some 10
  | 16, .nmiExit => some 12
  | 17, .irq => some 35
  | 17, .nmiExit => some 13
  | 18, .nmiExit => some 14
  | 19, .localEnable => some 29
  | 19, .nmiEntry => some 21
  | 20, .enableIRQ => some 14
  | 20, .localEnable => some 33
  | 20, .nmiEntry => some 22
  | 21, .nmiExit => some 19
  | 22, .nmiExit => some 20
  | 23, .localEnable => some 33
  | 23, .nmiEntry => some 24
  | 24, .nmiExit => some 23
  | 25, .irq => some 19
  | 25, .localEnable => some 0
  | 25, .nmiEntry => some 26
  | 26, .irq => some 21
  | 26, .nmiExit => some 25
  | 27, .irqEntry => some 2
  | 27, .nmiEntry => some 30
  | 28, .enableIRQ => some 3
  | 28, .irq => some 12
  | 28, .localEnable => some 13
  | 28, .nmiEntry => some 31
  | 29, .hwDisable => some 27
  | 29, .otherHwDisable => some 9
  | 29, .nmiEntry => some 32
  | 30, .nmiExit => some 27
  | 31, .irq => some 16
  | 31, .nmiExit => some 28
  | 32, .nmiExit => some 29
  | 33, .enableIRQ => some 29
  | 33, .localDisable => some 20
  | 33, .otherHwDisable => some 12
  | 33, .nmiEntry => some 35
  | 34, .enableIRQ => some 7
  | 34, .irq => some 20
  | 34, .localEnable => some 13
  | 34, .nmiEntry => some 37
  | 35, .nmiExit => some 33
  | 36, .irq => some 23
  | 36, .localEnable => some 13
  | 36, .nmiEntry => some 1
  | 37, .irq => some 22
  | 37, .nmiExit => some 34
  | _, _ => none

/-- Figure 11(g) starts in q0, its only marked state. -/
def irqFigure : Generator IRQEvent where
  Q := Fin 38
  q0 := 0
  δ := figureStep
  Qm := {0}

/-- In these four Figure 11(g) states, the vector has entered its handler and has yet
to exit. An intervening NMI can suspend the handler in this interval. -/
def inIRQHandler (q : Fin 38) : Bool := q.val ∈ [2, 4, 10, 15]

end ETFA2017


