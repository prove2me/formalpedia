-- Prove2me | Definitions.Def_IntMul_WideNormalizedProduct
-- name    : IntMul_WideNormalizedProduct
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T16:08:16.907817+00:00
-- url     : https://prove2.me/theorems/31322d80-5fa0-40a3-8c42-3d766b4b7571
-- title:
--   Complete physical product normalization at arbitrary sufficient coefficient precision
-- statement:
--   A fixed sixteen-tape machine composes actual carry/output product recovery, physical desired-width countdown preparation and exact output-width conversion. Its explicit input frame contains prepared convolution coefficients at declared sufficient precision, a zero carry and retained width word. Coefficient generation, loading and descriptor preparation are separate stages. Full correctness and clock are separate theorem obligations.
-- source:
--   Physical product normalization generalized to arbitrary sufficient coefficient precision. Written by Codex.

import Definitions.Def_IntMul_WideCarryProduct
import Definitions.Def_IntMul_WidthPreparation
import Definitions.Def_IntMul_FixedOutputWidth
import Definitions.Def_IntMul_FixedTapeExtension

set_option maxHeartbeats 1000000
set_option Elab.async false

namespace IntMul.WideNormalizedProduct
open TapeCopy (Sym)

noncomputable abbrev productNative : MultitapeTM := FixedTapeExtension.machine WideCarryProduct.machine
noncomputable abbrev widthNative : MultitapeTM := FixedTapeExtension.machine FixedOutputWidth.machine
abbrev State := Option (productNative.K ⊕ (WidthPreparation.State ⊕ widthNative.K))

noncomputable def productState (q : productNative.K) : State :=
  if q=none then none else some (.inl q)
def preparationState (q : WidthPreparation.State) : State :=
  if q=.halt then none else some (.inr (.inl q))
noncomputable def widthState (q : widthNative.K) : State :=
  if q=none then none else some (.inr (.inr q))

/-- Literal native actions on the same sixteen tapes. Every descriptor copy
and width-return transition is executed; no loading or cursor reset is added. -/
noncomputable def transition (q : State) (a : Fin 16 → Sym) :
    State × (Fin 16 → Sym × Move) :=
  match q with
  | none => (none,fun i => (a i,.stay))
  | some (.inl q) =>
      let r := productNative.δ q a
      (productState r.1,r.2)
  | some (.inr (.inl q)) =>
      let r := WidthPreparation.machine.δ q a
      (preparationState r.1,r.2)
  | some (.inr (.inr q)) =>
      let r := widthNative.δ q a
      (widthState r.1,r.2)

noncomputable abbrev subroutine : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := State
  qStart := productState productNative.qStart
  qHalt := none
  start_ne_halt := by
    have h : productNative.qStart≠none := productNative.start_ne_halt
    simp only [productState,if_neg h]
    exact Option.some_ne_none _
  k := 16
  two_le_k := by decide
  δ := transition
  start_preserved := by
    intro q a i hi
    cases q with
    | none =>
        change a i=Sym.start ∧ Move.stay≠Move.left
        exact ⟨hi,by decide⟩
    | some s =>
        cases s with
        | inl q => exact productNative.start_preserved q a i hi
        | inr s =>
            cases s with
            | inl q => exact WidthPreparation.machine.start_preserved q a i hi
            | inr q => exact widthNative.start_preserved q a i hi
  start_only_at_start := by
    intro q a i hi
    cases q with
    | none => exact hi
    | some s =>
        cases s with
        | inl q => exact productNative.start_only_at_start q a i hi
        | inr s =>
            cases s with
            | inl q => exact WidthPreparation.machine.start_only_at_start q a i hi
            | inr q => exact widthNative.start_only_at_start q a i hi
  halt_fixed := by intro a;rfl
  input_readonly := by
    intro q a
    cases q with
    | none => rfl
    | some s =>
        cases s with
        | inl q => exact productNative.input_readonly q a
        | inr s =>
            cases s with
            | inl q => exact WidthPreparation.machine.input_readonly q a
            | inr q => exact widthNative.input_readonly q a

inductive Phase | product | prepare | width deriving DecidableEq
instance : Fintype Phase where
  elems := {.product,.prepare,.width}
  complete := by intro q;cases q <;> simp

noncomputable def dispatch (q : Phase) (_a : Fin 16 → Sym) : Option (Phase × State) :=
  match q with
  | .product => some (.prepare,preparationState .advance)
  | .prepare => some (.width,widthState widthNative.qStart)
  | .width => none

noncomputable abbrev machine : MultitapeTM := FiniteCaller.machine subroutine Phase .product dispatch

noncomputable def productView (c : productNative.Cfg) : subroutine.Cfg where
  state := productState c.state
  cells := c.cells
  head := c.head
noncomputable def preparationView (c : WidthPreparation.machine.Cfg) : subroutine.Cfg where
  state := preparationState c.state
  cells := c.cells
  head := c.head
noncomputable def widthView (c : widthNative.Cfg) : subroutine.Cfg where
  state := widthState c.state
  cells := c.cells
  head := c.head

noncomputable def productBase (base : machine.Cfg) (d : List Bool) : productNative.Cfg where
  state := productNative.qHalt
  cells := Function.update base.cells 15 (productNative.tapeOf (d.map productNative.bitSym))
  head := Function.update base.head 15 0

noncomputable def productIncoming (base : machine.Cfg) (pre x y z l d : List Bool) : productNative.Cfg :=
  FixedTapeExtension.embed WideCarryProduct.machine (productBase base d) (WideCarryProduct.initialFrame pre x y z l)
noncomputable def productFinal (base : machine.Cfg) (pre x y z l d : List Bool) : productNative.Cfg :=
  FixedTapeExtension.embed WideCarryProduct.machine (productBase base d) (WideCarryProduct.finalFrame pre x y z l)

/-- Complete coefficient frame plus one retained desired-output-width word.
Coefficient generation, coefficient loading and descriptor construction are
explicit caller obligations. This native input bank may be compiled to a
writable physical bank by the accepted banked simulation. -/
noncomputable def initialFrame (base : machine.Cfg) (pre x y z l d : List Bool) : machine.Cfg :=
  FiniteCaller.embed subroutine Phase .product .product dispatch
    (productView (productIncoming base pre x y z l d))

noncomputable def finalFrame (base : machine.Cfg) (pre x y z l d : List Bool) : machine.Cfg where
  state := none
  cells := Function.update (Function.update (Function.update (productFinal base pre x y z l d).cells
    1 (machine.tapeOf ((bin (FixedOutputWidth.width d) (val x*val y)).map machine.bitSym)))
      3 (WidthPreparation.descriptorTape d)) 4 (WidthPreparation.descriptorTape d)
  head := Function.update (Function.update (Function.update (productFinal base pre x y z l d).head
    1 (FixedOutputWidth.width d+1)) 3 (d.length+1)) 4 (d.length+1)

end IntMul.WideNormalizedProduct


