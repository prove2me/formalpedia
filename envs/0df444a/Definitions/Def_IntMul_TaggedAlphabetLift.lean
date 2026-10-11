-- Prove2me | Definitions.Def_IntMul_TaggedAlphabetLift
-- name    : IntMul_TaggedAlphabetLift
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T16:54:01.990952+00:00
-- url     : https://prove2.me/theorems/dcefc903-91d9-460d-aefb-0106e5beb8f7
-- title:
--   Alphabet-compatible same-tape compiler for global-marker routines and interior banks
-- statement:
--   For any finite multitape machine M, a finite compiler embeds its ordinary alphabet into the tagged alphabet used by interior work banks. The global start marker maps to the distinguished outer marker, while all other symbols are tagged. The compiled transition retains the same states and number of tapes, decodes scanned symbols, executes one native transition, and protects the global marker. Exact step simulation, standard initial configurations, input retention, and output preservation are separate theorem obligations.
-- source:
--   Original alphabet-compatible literal finite transition compiler. Written by Codex.

import Definitions.Def_IntMul_BankedSimulation
namespace IntMul.AlphabetLift
noncomputable def encode (M : MultitapeTM) (s : M.Sym) : Option M.Sym := by
  classical
  exact if s=M.startSym then none else some s
noncomputable def transition (M : MultitapeTM) (q : M.K) (a : Fin M.k → Option M.Sym) :
    M.K × (Fin M.k → Option M.Sym × Move) :=
  let r := M.δ q (fun i => BankedSimulation.decode M (a i))
  (r.1,fun i => BankedSimulation.protect M (a i) (r.2 i).1 (r.2 i).2)
noncomputable abbrev machine (M : MultitapeTM) : MultitapeTM where
  Sym := Option M.Sym
  blank := some M.blank
  startSym := none
  zero := some M.zero
  one := some M.one
  sep := some M.sep
  syms_distinct := (BankedSimulation.machine M).syms_distinct
  K := M.K
  qStart := M.qStart
  qHalt := M.qHalt
  start_ne_halt := M.start_ne_halt
  k := M.k
  two_le_k := M.two_le_k
  δ := transition M
  start_preserved := by
    intro q a i hi
    simp only [transition];rw [hi];simp only [BankedSimulation.protect]
    split <;> simp_all
  start_only_at_start := by
    intro q a i hi
    simp only [transition]
    cases hs : a i with
    | none => exact False.elim (hi hs)
    | some s => simp [BankedSimulation.protect]
  halt_fixed := by
    intro a
    simp only [transition,M.halt_fixed]
    congr 1;funext i;cases a i <;> rfl
  input_readonly := by
    intro q a
    change (BankedSimulation.protect M (a M.inTape)
      ((M.δ q (fun i => BankedSimulation.decode M (a i))).2 M.inTape).1 _).1=a M.inTape
    simp only [MultitapeTM.inTape]
    rw [M.input_readonly]
    cases ha : a ⟨0,by have := M.two_le_k;omega⟩ <;> simp [ha,BankedSimulation.decode,BankedSimulation.protect]
noncomputable def embed (M : MultitapeTM) (c : M.Cfg) : (machine M).Cfg where
  state := c.state
  cells := fun i p => encode M (c.cells i p)
  head := c.head
end IntMul.AlphabetLift


