-- Prove2me | Definitions.Def_IntMul_PreparedBankedCall
-- name    : IntMul_PreparedBankedCall
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T14:04:16.427289+00:00
-- url     : https://prove2.me/theorems/57265764-67f6-44b1-a74e-ef901497ec2c
-- title:
--   Prepared-state banked child execution and physical global-output return with retained input
-- statement:
--   For any fixed multitape machine, the literal accepted banked-caller table may be entered at a physically prepared child configuration in writable offset-one work banks. The true caller input and all saved work-bank prefixes are retained. Global output is supplied empty at its first payload cursor. Child execution, halt dispatch, actual output-bank rewind and bit-by-bit return to global output are performed by the finite transition table. Creating the supplied bank configuration and empty output remains an explicit caller obligation; correctness and the complete charged clock are separate theorem obligations.
-- source:
--   Original generalization of the accepted physical banked caller to arbitrary prepared child configurations, required to relocate coefficient-based product recovery onto writable banks. Written by Codex.

import Definitions.Def_IntMul_BankedCall

namespace IntMul.PreparedBankedCall

open IntMul.BankedCall (Phase State transition rawTransition)

/-- The exact accepted banked caller table, entered at a prepared child state.
The physical coefficient/input banks must already exist; no global setup is
asserted free. Global input is read-only throughout simulation and return. -/
noncomputable abbrev machine (M : MultitapeTM) : MultitapeTM :=
  {BankedCall.machine M with
    qStart := .inr M.qStart
    start_ne_halt := by simp}

/-- Global output is physically supplied empty at its first payload cursor.
All other global data and heads are the saved caller frame. -/
noncomputable def bankBase (M : MultitapeTM) (base : (machine M).Cfg) :
    (BankedSimulation.machine M).Cfg where
  state := M.qHalt
  cells := Function.update base.cells ⟨1,by change 1 < M.k+2;omega⟩ ((machine M).tapeOf [])
  head := Function.update base.head ⟨1,by change 1 < M.k+2;omega⟩ 1

def bankTape (M : MultitapeTM) (saved : ℕ → Option M.Sym) (w : List M.Sym) (p : ℕ) : Option M.Sym :=
  if p=0 then saved p else some (M.tapeOf w (p-1))

/-- The supplied child configuration occupies writable work banks at offset
one. Global input remains the original saved caller input. All local markers,
payloads and cursors are explicit incoming physical obligations. -/
noncomputable def runningFrame (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg) : (machine M).Cfg where
  state := .inr c.state
  cells := (BankedSimulation.embed M (bankBase M base) (fun _ => 1) c).cells
  head := (BankedSimulation.embed M (bankBase M base) (fun _ => 1) c).head

noncomputable def returnOutputFrame (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg)
    (pos : ℕ) : (machine M).Cfg where
  state := .inl .rewindOutput
  cells := (runningFrame M base c).cells
  head := fun i => if i.val=3 then pos else (runningFrame M base c).head i

noncomputable def copyOutputFrame (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg)
    (w : List Bool) (j : ℕ) : (machine M).Cfg where
  state := .inl .copyOutput
  cells := fun i => if i.val=1 then (machine M).tapeOf ((w.take j).map (machine M).bitSym)
    else (runningFrame M base c).cells i
  head := fun i => if i.val=1 then j+1 else if i.val=3 then j+2 else (runningFrame M base c).head i

noncomputable def finalFrame (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg)
    (w : List Bool) : (machine M).Cfg where
  state := .inl .halt
  cells := (copyOutputFrame M base c w w.length).cells
  head := (copyOutputFrame M base c w w.length).head

end IntMul.PreparedBankedCall


