-- Prove2me | Definitions.Def_MultiSelectPandora_RawSSDP_MAX
-- name    : MultiSelectPandora_RawSSDP_MAX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:16:32.610926+00:00
-- url     : https://prove2.me/theorems/8c5b0305-01a2-4f38-b853-e5e6961b94d9
-- title:
--   $\mathrm{MAX}$ of a table
-- statement:
--   $\mathrm{MAX}:=\max_{I\in V}\mathrm{DP}_1(I,A)$, the same quantity when the starting state may be chosen arbitrarily.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), p.8 (PDF p.9)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawSSDP
import Definitions.Def_MultiSelectPandora_RawSSDP_dp
import Definitions.Def_MultiSelectPandora_RawSSDP_OPT

namespace MultiSelectPandora

/-- **`MAX := max_{I ∈ V} DP_1(I, A)`.** Beyhaghi–Han–Luqman manuscript, p.8 (PDF p.9).

**Formalization Note.** A `Finset.fold max` with base `OPT`; on a valid program the initial state is a state, so the base changes
nothing ("`MAX ≥ OPT`", p.8). -/
noncomputable def RawSSDP.MAX (S : RawSSDP) : ℝ :=
  (Finset.range S.L).fold max S.OPT fun st => S.dp S.T st ∅

end MultiSelectPandora


