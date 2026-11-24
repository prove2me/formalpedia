-- Prove2me | Definitions.Def_ETFA2017_Checker
-- name    : ETFA2017_Checker
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-24T06:37:18.906424+00:00
-- url     : https://prove2.me/theorems/9c67c98a-eb4c-471c-bef4-5744a1100896
-- title:
--   Per-CPU and per-vector routing, finite trace checking, and hidden events
-- statement:
--   Each CPU has an NMI model and one IRQ model per vector. Shared events are routed to all affected instances. The checker stops at the first blocked event and returns its zero-based index. The optional observation semantics erases hardware requests.
-- source:
--   D. B. de Oliveira, R. S. de Oliveira, T. Cucinotta and L. Abeni, ETFA 2017, Automata-Based Modeling of Interrupts in the Linux PREEMPT RT Kernel.  https://retis.santannapisa.it/~tommaso/publications/ETFA-2017.pdf#page=4

import Definitions.Def_ETFA2017_NMI
import Definitions.Def_ETFA2017_IRQComponents
import Definitions.Def_CassandrasLafortune_Parallel
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

/-! Routing and trace validation for the per-CPU interrupt models of ETFA 2017,
Section III and Tables I–II. The input is a finite total ordering of modeled events. -/

namespace ETFA2017

open RamadgeWonham.Shared

/-- The source CPU and vector identify which copies of the generators see an event.
Global masks apply to the same vector on every CPU. -/
inductive SystemEvent (cpus vectors : Nat) where
  | nmiRequest (cpu : Fin cpus)
  | nmiEntry (cpu : Fin cpus)
  | nmiExit (cpu : Fin cpus)
  | irqRequest (cpu : Fin cpus) (vector : Fin vectors)
  | irqEntry (cpu : Fin cpus) (vector : Fin vectors)
  | irqExit (cpu : Fin cpus) (vector : Fin vectors)
  | hwDisable (cpu : Fin cpus) (vector : Fin vectors)
  | localDisable (cpu : Fin cpus)
  | localEnable (cpu : Fin cpus)
  | disableIRQ (vector : Fin vectors)
  | enableIRQ (vector : Fin vectors)
  deriving DecidableEq

variable {cpus vectors : Nat}

/-- The observation extension hides the two hardware-request events described in Section III.
The remaining events, their routing information and their relative order are retained. -/
def recorded : SystemEvent cpus vectors → Bool
  | .nmiRequest _ | .irqRequest _ _ => false
  | _ => true

/-- Each CPU has one NMI slot and one IRQ slot per vector. -/
abbrev Slot (cpus vectors : Nat) := Fin cpus × Option (Fin vectors)

def Slot.Alphabet (s : Slot cpus vectors) : Type :=
  match s.2 with
  | none => NMIEvent
  | some _ => IRQEvent

def slotModel (N : Generator NMIEvent) (I : Generator IRQEvent) :
    (s : Slot cpus vectors) → Generator s.Alphabet
  | (_, none) => N
  | (_, some _) => I

def nmiView (cpu : Fin cpus) : SystemEvent cpus vectors → Option NMIEvent
  | .nmiRequest c => if c = cpu then some .request else none
  | .nmiEntry c => if c = cpu then some .entry else none
  | .nmiExit c => if c = cpu then some .exit else none
  | _ => none

/-- The same hardware mask is the triggering vector's own mask and every other local
vector's other-IRQ mask. Handler events are specific to the triggering vector. -/
def irqView (cpu : Fin cpus) (vector : Fin vectors) : SystemEvent cpus vectors → Option IRQEvent
  | .irqRequest c v => if c = cpu ∧ v = vector then some .irq else none
  | .irqEntry c v => if c = cpu ∧ v = vector then some .irqEntry else none
  | .irqExit c v => if c = cpu ∧ v = vector then some .irqExit else none
  | .hwDisable c v =>
      if c = cpu then some (if v = vector then .hwDisable else .otherHwDisable) else none
  | .localDisable c => if c = cpu then some .localDisable else none
  | .localEnable c => if c = cpu then some .localEnable else none
  | .nmiEntry c => if c = cpu then some .nmiEntry else none
  | .nmiExit c => if c = cpu then some .nmiExit else none
  | .disableIRQ v => if v = vector then some .disableIRQ else none
  | .enableIRQ v => if v = vector then some .enableIRQ else none
  | .nmiRequest _ => none

def route : (s : Slot cpus vectors) → SystemEvent cpus vectors → Option s.Alphabet
  | (c, none) => nmiView c
  | (c, some v) => irqView c v

variable {ι E : Type} {A : ι → Type}

/-- A simultaneous transition in a finite family of partial deterministic generators. -/
def routedSystem [Fintype ι] (G : (i : ι) → Generator (A i)) (view : (i : ι) → E → Option (A i)) :
    Generator E where
  Q := (i : ι) → (G i).Q
  q0 i := (G i).q0
  δ e q :=
    let next i := CassandrasLafortune.localStep (G i) (q i) (view i e)
    if ok : ∀ i, (next i).isSome = true then some (fun i ↦ (next i).get (ok i)) else none
  Qm := {q | ∀ i, q i ∈ (G i).Qm}

def interruptSystem (N : Generator NMIEvent) (I : Generator IRQEvent) :
    Generator (SystemEvent cpus vectors) :=
  routedSystem (slotModel N I) route

/-- The checker executes one event at a time and returns the zero-based index of its first
undefined transition. Its state argument retains all component endpoints on success. -/
def scanTrace {α : Type} (G : Generator α) (q : G.Q) (offset : Nat) : List α → Except Nat G.Q
  | [] => .ok q
  | e :: es =>
      match G.δ e q with
      | none => .error offset
      | some r => scanTrace G r (offset + 1) es

def checkTrace (N : Generator NMIEvent) (I : Generator IRQEvent) (w : List (SystemEvent cpus vectors)) :=
  let G := interruptSystem N I
  scanTrace G G.q0 0 w

/-- A path in the observational model may take unrecorded hardware steps without consuming
a visible letter. It may also stop before or after any finite number of silent steps. -/
inductive Observes {α : Type} (G : Generator α) (visible : α → Bool) :
    G.Q → List α → G.Q → Prop
  | done (q) : Observes G visible q [] q
  | silent {q r t e obs} : G.δ e q = some r → visible e = false →
      Observes G visible r obs t → Observes G visible q obs t
  | seen {q r t e obs} : G.δ e q = some r → visible e = true →
      Observes G visible r obs t → Observes G visible q (e :: obs) t

end ETFA2017


