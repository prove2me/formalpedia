-- Prove2me | Definitions.Def_IntMul_FiniteCaller
-- name    : IntMul_FiniteCaller
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T19:38:45.332972+00:00
-- url     : https://prove2.me/theorems/637e7b4c-078b-4fcb-aa11-f26102b4ab35
-- title:
--   Literal finite-state caller with one-transition dispatch
-- statement:
--   A generic actual finite multitape caller compiler. Its state consists of finite caller state and subroutine state, plus one global halt state. It copies each nonterminal subroutine transition exactly and dispatches at subroutine halt using only caller state and scanned symbols. A dispatch preserves every tape and head position and costs one actual transition. No tapes or alphabet symbols are added, no head resets occur, and the caller sees no numeric lengths or positions. Correct bounded simulation is a separate theorem.
-- source:
--   The campaign MultitapeTM conventions and exact machine model, published definition 47ff1689-4e87-4af2-9406-674787e32429. Original finite-table compiler and interface formalization, Written by Codex.

import Definitions.Def_IntMul_MultitapeModel

/-!
# A literal finite-state caller for multitape subroutines

Every nonterminal subroutine transition is copied verbatim. At a subroutine
halt, one charged transition dispatches using finite caller state and scanned
symbols, preserving all tape contents and head positions.
-/

namespace IntMul.FiniteCaller

/-- Dispatch sees only finite caller state and currently scanned symbols.
`none` means global halt; `some (e,q)` resumes at subroutine state `q` with
caller state `e`. -/
noncomputable def transition (M : MultitapeTM) (E : Type) [Fintype E]
    (dispatch : E → (Fin M.k → M.Sym) → Option (E × M.K))
    (q : Option (E × M.K)) (a : Fin M.k → M.Sym) :
    Option (E × M.K) × (Fin M.k → M.Sym × Move) := by
  classical
  exact match q with
  | none => (none, fun i => (a i, .stay))
  | some (e,q) =>
      if q = M.qHalt then
        (dispatch e a, fun i => (a i, .stay))
      else
        let r := M.δ q a
        (some (e,r.1), r.2)

/-- One actual finite multitape machine, with the original alphabet and
physical tapes and a finite caller/subroutine product of states. -/
noncomputable abbrev machine (M : MultitapeTM) (E : Type) [Fintype E] (initial : E)
    (dispatch : E → (Fin M.k → M.Sym) → Option (E × M.K)) : MultitapeTM where
  Sym := M.Sym
  blank := M.blank
  startSym := M.startSym
  zero := M.zero
  one := M.one
  sep := M.sep
  syms_distinct := M.syms_distinct
  K := Option (E × M.K)
  qStart := some (initial,M.qStart)
  qHalt := none
  start_ne_halt := Option.some_ne_none _
  k := M.k
  two_le_k := M.two_le_k
  δ := transition M E dispatch
  start_preserved := by
    classical
    intro q a i hi
    cases q with
    | none => simp [transition, hi]
    | some eq =>
        rcases eq with ⟨e,q⟩
        by_cases hq : q = M.qHalt
        · simp [transition, hq, hi]
        · simpa [transition, hq] using M.start_preserved q a i hi
  start_only_at_start := by
    classical
    intro q a i hi
    cases q with
    | none => simpa [transition] using hi
    | some eq =>
        rcases eq with ⟨e,q⟩
        by_cases hq : q = M.qHalt
        · simpa [transition, hq] using hi
        · simpa [transition, hq] using M.start_only_at_start q a i hi
  halt_fixed := by intro a; rfl
  input_readonly := by
    classical
    intro q a
    cases q with
    | none => rfl
    | some eq =>
        rcases eq with ⟨e,q⟩
        by_cases hq : q = M.qHalt
        · simp [transition, hq]
        · simpa [transition, hq] using M.input_readonly q a

/-- Embedding preserves every physical tape and head; it only records a finite
caller state alongside the subroutine state. -/
def embed (M : MultitapeTM) (E : Type) [Fintype E] (initial e : E)
    (dispatch : E → (Fin M.k → M.Sym) → Option (E × M.K)) (c : M.Cfg) :
    (machine M E initial dispatch).Cfg where
  state := some (e,c.state)
  cells := c.cells
  head := c.head

/-- Complete configuration after the one charged dispatch transition. -/
def returned (M : MultitapeTM) (E : Type) [Fintype E] (initial e : E)
    (dispatch : E → (Fin M.k → M.Sym) → Option (E × M.K)) (c : M.Cfg) :
    (machine M E initial dispatch).Cfg where
  state := dispatch e (fun i => c.cells i (c.head i))
  cells := c.cells
  head := c.head

end IntMul.FiniteCaller


