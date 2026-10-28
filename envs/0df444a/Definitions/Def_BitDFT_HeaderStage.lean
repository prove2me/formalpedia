-- Prove2me | Definitions.Def_BitDFT_HeaderStage
-- name    : BitDFT_HeaderStage
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:30:05.47422+00:00
-- url     : https://prove2.me/theorems/d0536c70-98b7-4a77-ae80-a5446a4809f3
-- title:
--   A composable parser that stops after reading a binary field
-- statement:
--   A controller adapter changes a specified internal state into a frozen exit state while preserving all other transitions. Applied to the four-tape binary header reader at its copying state, it supplies a finite parsing stage that stops immediately after decoding the first field. It retains the decoded bits and clears its unary counter without copying the remaining vector. It uses the same alphabet and tape layout as the reader and can be joined to subsequent compatible stages by BitDFT_MachineSequence.
-- source:
--   Uses the finite header-reader definition and the verified controller-composition interface. The stopping adapter preserves the marker, read-only-input and frozen-exit invariants by construction.

import Definitions.Def_BitDFT_HeaderReader
import Definitions.Def_BitDFT_MachineSequence

namespace BitDFT.MachineSequence
open IntMul

/-- Turn an internal stage boundary into a controller exit, without changing earlier steps. -/
noncomputable def stopAt (M : MultitapeTM) (boundary : M.K)
    (hne : M.qStart ≠ boundary) : Controller M := by
  classical
  exact {
    K := M.K
    entry := M.qStart
    exit := boundary
    distinct := hne
    transition := fun q a => if q = boundary then (q, fun i => (a i, .stay)) else M.δ q a
    marker := by
      intro q a i hi
      by_cases hq : q = boundary
      · simp [hq, hi]
      · simpa [hq] using M.start_preserved q a i hi
    noMarker := by
      intro q a i hi
      by_cases hq : q = boundary
      · simpa [hq] using hi
      · simpa [hq] using M.start_only_at_start q a i hi
    frozen := by intro a; simp
    readonly := by
      intro q a
      by_cases hq : q = boundary
      · simp [hq]
      · simpa [hq, MultitapeTM.inTape] using M.input_readonly q a }

def stopCfg (M : MultitapeTM) (boundary : M.K) (hne : M.qStart ≠ boundary)
    (c : M.Cfg) : (stopAt M boundary hne).machine.Cfg :=
  ⟨c.state, c.cells, c.head⟩

end BitDFT.MachineSequence

namespace BitDFT.HeaderReader
/-- The parser as a composable finite controller: stop before copying the remaining vector. -/
noncomputable def stage : MachineSequence.Controller machine :=
  MachineSequence.stopAt machine State.copy (by decide)

end BitDFT.HeaderReader


