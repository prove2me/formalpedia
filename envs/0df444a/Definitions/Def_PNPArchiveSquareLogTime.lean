-- Prove2me | Definitions.Def_PNPArchiveSquareLogTime
-- name    : PNPArchiveSquareLogTime
-- status  : Definition
-- author  : @xwh
-- created : 2026-10-23T08:40:11.247082+00:00
-- url     : https://prove2.me/theorems/a3121fd8-dc8c-4b12-8608-a246c5cfdad1
-- title:
--   The fixed square-log deterministic-time class
-- statement:
--   Define ℓ(n)=⌈log₂(n+2)⌉ and the class T₂ of Boolean decision functions computed by one fixed deterministic finite-control stack machine in at most C·2^(a·ℓ(n)²) steps for fixed positive integers a,C. The runtime argument is the actual encoded input length, using the same published canonical bitstring encodings as PvsNP.P and PvsNP.NP. The union varies the fixed multiplier a, not the power 2 of the logarithm. This definition asserts no NP inclusion and no complexity separation. It formalizes the class in archive round79 equation(10); equivalence with the archive native model is described mathematically, not proved here.
-- source:
--   https://github.com/liushuijixiang/p-vs-np-research-archive/blob/88a23d510593dc27272d302390f5cf7549b72fc8/rounds/round-79/report-extracted.md — §§1–4, equation (10); mathematical formulation transcribed from the report, with machine-model comparison explicitly documented.

import Definitions.Def_PvsNP_complexity_classes
import Mathlib.Data.Nat.Log

/-!+# Archive R79's fixed square-log deterministic-time class

R79 equation (10) proposes inclusion of this class in NP. This is a stronger
research route sufficient for P≠NP, not a restatement of P≠NP itself.
The archive's native decoder is not reconstructed here. We use the already
published finite-stack model and its canonical encodings explicitly.
-/

set_option autoImplicit false

namespace PNPArchive

def squareLogClock (a n : ℕ) : ℕ :=
  2 ^ (a * (Nat.clog 2 (n + 2)) ^ 2)

/-- The time class unions over fixed positive integers `a,C` and fixed
machines, all selected before quantifying over input lengths. `n` measures
the actual encoded input supplied to the machine. -/
def SquareLogTime : PvsNP.DecisionComplexityClass :=
  { f | ∃ machine : Turing.TM2ComputableInTime
        (PvsNP.BitstringEncoding.bitEncode : List Bool → List Bool)
        (PvsNP.BitstringEncoding.bitEncode : Bool → List Bool) f,
      ∃ a C : ℕ, 0 < a ∧ 0 < C ∧
        ∀ n, machine.time n ≤ C * squareLogClock a n }

end PNPArchive


