-- Prove2me | Definitions.Def_DetANN_RelocCall
-- name    : DetANN_RelocCall
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:44:40.283678+00:00
-- url     : https://prove2.me/theorems/44a462d6-ea5c-4a2b-b3a0-a61e7638ad7f
-- title:
--   Host-anchored relocation frames for ANN preprocessing and query calls
-- statement:
--   For a host state $r$, `Frame.atHost` is the relocation frame with the specified register bounds, memory base $b$, window radius $R$ and work offset $c$. Its coin-cursor offset is $0$, and its outside-window real and integer memories are exactly $r$'s current memories. Consequently, a host state anchored in this way needs no outside-window preservation hypotheses at call entry.
--
--   The constructor `Frame.sim_atHost` proves the simulation relation from the renamed-register and pointer equations, the base-pointer equation, the two memory equations on $|z|\le R$, cursor and work equations, running hypotheses, and the relocated program-counter equation. It is the generic entry adapter for `DetANN.reloc_sim_timed_cells`; the ANN input and query specializations are provided separately.
-- source:
--   Original PNormReg relocation-library interface written for Feng--Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission, §7.4, p.19; uses PNormRegLib_Simulation and reloc_sim_timed_cells for relocated opaque Lemma 3.3 calls.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_PNormRegLib_Simulation

namespace PNormRegLib
namespace Frame

open PNormReg

/-- A relocation frame whose outside-window memories are exactly those of the current host state.
The coin-cursor offset is zero and the work offset is the explicitly supplied `c`. -/
def atHost (nR nQ : ℕ) (b R : ℤ) (c : ℕ) (r : State) : Frame where
  nR := nR
  nQ := nQ
  b := b
  R := R
  k := 0
  c := c
  M := r.core.mem
  IM := r.integerMemory

/-- Construct the simulation relation in an `atHost` frame from its renamed-register, base,
window-memory, counter, running and program-counter equations. No outside-window equations are
required: they hold by definition of the frame. -/
theorem sim_atHost (p : RelocParams) (nR nQ : ℕ) (b R : ℤ) (c : ℕ) (r v : State)
    (hreg : ∀ i < nR, r.core.regs (p.roff + i) = v.core.regs i)
    (hptr : ∀ q < nQ, r.core.ptrs (p.qoff + q) = v.core.ptrs q)
    (hbase : r.core.ptrs p.base = b)
    (hmem : ∀ z, |z| ≤ R → r.core.mem (b + z) = v.core.mem z)
    (hint : ∀ z, |z| ≤ R → r.integerMemory (b + z) = v.integerMemory z)
    (hcursor : r.cursor = v.cursor) (hwork : r.work = c + 2 * v.work)
    (hr : r.halted = false) (hv : v.halted = false)
    (hpc : r.core.pc = p.cOff + 2 * v.core.pc) :
    Sim p (atHost nR nQ b R c r) r v := by
  refine ⟨⟨hreg, hptr, hbase, hmem, hint, ?_, ?_, ?_, ?_⟩, hr, hv, hpc⟩
  · intro y hy
    rfl
  · intro y hy
    rfl
  · simpa [atHost] using hcursor
  · exact hwork

end Frame
end PNormRegLib


