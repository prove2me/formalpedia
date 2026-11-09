-- Prove2me | Definitions.Def_HSElemKernel_haltSteps
-- name    : HSElemKernel_haltSteps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:23:12.989726+00:00
-- url     : https://prove2.me/theorems/40e029d9-6ea2-4760-b7a9-4c4774a2ef7f
-- title:
--   Number of executed steps until the first halt
-- statement:
--   For a RAM program $P$, an initial memory and a coin tape, **haltSteps** is the number of instructions executed before the run first halts (and $0$ if it never halts). It measures "time linear in the encoding length" in Lemma 2.4 with unit cost per instruction.
--
--   **Formalization Note** The runs are those of the published RAM `TimeSpaceMA_RAM` (`SoftmaxAttnFD.run`); its bit cost `SoftmaxAttnFD.cost` charges bit lengths and cannot even read an input in linear bit cost.
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Lemma 2.4, p.5

import Mathlib
import Definitions.Def_SoftmaxAttnFD_Machine

namespace HSElemKernel

open Classical in
/-- The number of executed steps of `P` from memory `mem` on tape `τ` until the first halt
(`0` if the run never halts) (Sheng–Xiao, arXiv:2609.06512, held version sha256 aca9c70e…,
Lemma 2.4, p.5, "in time linear in the encoding length").

**Formalization Note** This is the unit-cost step count on the published RAM
(`TimeSpaceMA_RAM`, run by `SoftmaxAttnFD.run`); the log-cost `SoftmaxAttnFD.cost` charges bit
lengths and cannot even read an input in linear bit cost. -/
noncomputable def haltSteps (P : TimeSpaceMA.Program) (mem : ℕ → ℕ) (τ : ℕ → Bool) : ℕ :=
  if h : ∃ T, (SoftmaxAttnFD.run P mem τ T).halted = true then Nat.find h else 0

end HSElemKernel


