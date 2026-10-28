-- Prove2me | Definitions.Def_BitDFT_MachineSequence
-- name    : BitDFT_MachineSequence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:21:52.349665+00:00
-- url     : https://prove2.me/theorems/3b822b38-2647-4277-9faf-62668c698b2d
-- title:
--   Sequential finite controllers with a stationary one-step handoff
-- statement:
--   Finite controllers share a specified tape layout and alphabet. Their sequential composition uses a disjoint sum of finite states. It executes the first controller until its exit state, switches to the second entry state in one transition without changing any cell or head, and then executes the second controller. The resulting object is an actual multitape Turing machine preserving the marker, read-only input, and frozen-halt invariants. This construction composes already-compatible controllers; adapting different alphabets and allocating tape banks remain separate tasks.
-- source:
--   Original finite-controller composition for the BitDFT machine construction, using the existing IntMul.MultitapeTM model.

import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Data.Fintype.Sum

namespace BitDFT.MachineSequence
open IntMul

/-- A finite controller using an existing machine's alphabet and tape layout. -/
structure Controller (M : MultitapeTM) where
  K : Type
  [finite : Fintype K]
  entry : K
  exit : K
  distinct : entry ≠ exit
  transition : K → (Fin M.k → M.Sym) → K × (Fin M.k → M.Sym × Move)
  marker : ∀ q a i, a i = M.startSym →
    ((transition q a).2 i).1 = M.startSym ∧ ((transition q a).2 i).2 ≠ .left
  noMarker : ∀ q a i, a i ≠ M.startSym → ((transition q a).2 i).1 ≠ M.startSym
  frozen : ∀ a, transition exit a = (exit, fun i => (a i, .stay))
  readonly : ∀ q a, ((transition q a).2 M.inTape).1 = a M.inTape

attribute [instance] Controller.finite

abbrev Controller.machine {M : MultitapeTM} (P : Controller M) : MultitapeTM where
  Sym := M.Sym
  blank := M.blank
  startSym := M.startSym
  zero := M.zero
  one := M.one
  sep := M.sep
  syms_distinct := M.syms_distinct
  K := P.K
  qStart := P.entry
  qHalt := P.exit
  start_ne_halt := P.distinct
  k := M.k
  two_le_k := M.two_le_k
  δ := P.transition
  start_preserved := P.marker
  start_only_at_start := P.noMarker
  halt_fixed := P.frozen
  input_readonly := P.readonly

def native (M : MultitapeTM) : Controller M where
  K := M.K
  entry := M.qStart
  exit := M.qHalt
  distinct := M.start_ne_halt
  transition := M.δ
  marker := M.start_preserved
  noMarker := M.start_only_at_start
  frozen := M.halt_fixed
  readonly := M.input_readonly

/-- The handoff takes one stationary transition and preserves every tape cell and head. -/
noncomputable def sequence {M : MultitapeTM} (P Q : Controller M) : Controller M := by
  classical
  exact {
    K := Sum P.K Q.K
    entry := .inl P.entry
    exit := .inr Q.exit
    distinct := by simp
    transition := fun q a => match q with
      | .inl p => if p = P.exit then (.inr Q.entry, fun i => (a i, .stay))
          else (.inl (P.transition p a).1, (P.transition p a).2)
      | .inr q => (.inr (Q.transition q a).1, (Q.transition q a).2)
    marker := by
      intro q a i hi
      cases q with
      | inl p =>
        by_cases hp : p = P.exit
        · simp [hp, hi]
        · simpa [hp] using P.marker p a i hi
      | inr q => exact Q.marker q a i hi
    noMarker := by
      intro q a i hi
      cases q with
      | inl p =>
        by_cases hp : p = P.exit
        · simpa [hp] using hi
        · simpa [hp] using P.noMarker p a i hi
      | inr q => exact Q.noMarker q a i hi
    frozen := by intro a; simp [Q.frozen]
    readonly := by
      intro q a
      cases q with
      | inl p =>
        by_cases hp : p = P.exit
        · simp [hp]
        · simpa [hp] using P.readonly p a
      | inr q => exact Q.readonly q a }

def leftCfg {M : MultitapeTM} (P Q : Controller M) (c : P.machine.Cfg) :
    (sequence P Q).machine.Cfg := ⟨.inl c.state, c.cells, c.head⟩

def rightCfg {M : MultitapeTM} (P Q : Controller M) (c : Q.machine.Cfg) :
    (sequence P Q).machine.Cfg := ⟨.inr c.state, c.cells, c.head⟩

def handoff {M : MultitapeTM} (P Q : Controller M) (c : P.machine.Cfg) :
    Q.machine.Cfg := ⟨Q.entry, c.cells, c.head⟩

end BitDFT.MachineSequence


