-- Prove2me | Definitions.Def_QMCLeafB_fam33_m4
-- name    : QMCLeafB_fam33_m4
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:42:27.785184+00:00
-- url     : https://prove2.me/theorems/bf2bbb2e-f4ae-4a1c-a269-2a0606666a97
-- title:
--   QMCLeafB fam33_m4
-- statement:
--   # `Check_fam33_m4` — the `Sound31` interface with the base case removed
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_sound31
/-
# `Check_fam33_m4` — the `Sound31` interface with the base case removed

`Sound31.solution_of_runPartsFamily` asks for a record family

    B : ∀ (G) (t), RunParts o G t (P G)

at **every** input, including `n ≤ 1`.  But `soundEpsOnBracket_of_family` splits on `2 ≤ G.n` and
settles the `n ≤ 1` stratum with `VerdictSound.soundAt_of_le_one`, which reads **no** record.  So the
`n ≤ 1` half of `B` is never consumed: it is a spurious obligation on the producer.

It is also an expensive one, because both banked record builders require `2 ≤ G.n`:
`Inst31SubM3.runParts_of_member` and `QMCLeafB.RefutedM3.runParts_of_emptyBody`.  At `n ≤ 1` there
are no edges, so `Rq = 0`, `eps = 0` and `dqShallow = 1` (the fallback), and the two constructions
have to be redone from scratch.

This file re-keys the interface to the stratum the stroke actually reads:

    B : ∀ (G), 2 ≤ G.n → ∀ (t), RunParts o G t (P G)

and the same verbatim `SolutionStatement` follows.  The residual is strictly weaker than phase 33's.

Import cone: `Check_sound31` + `Check_fal30_m4` (published `Definitions/` side only; no
`Check_EngineIterates`, so this file is outside the `Check_asm2_m8` collision class).
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Round33M4b

open QuantumMaxCutEnergy
open QMCLeafB.FinalStroke

/-- **`SoundεOnBracket` from a record family restricted to `2 ≤ n`.** -/
theorem soundEpsOnBracket_of_family_ge2 {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (B : ∀ (G : QuantumMaxCutEnergy.Input), 2 ≤ G.n → ∀ t : ℚ,
      QMCLeafB.FinalStroke.RunParts o G t (P G))
    (hKm : ∀ (G : QuantumMaxCutEnergy.Input), 2 ≤ G.n → 0 < (P G).K * (P G).m) :
    QMCLeafB.FinishLine.SoundεOnBracket o := by
  rw [QMCLeafB.VerdictSound.soundEpsOnBracket_iff]
  intro G t hlo hhi
  by_cases hn : 2 ≤ G.n
  · exact QMCLeafB.Sound31.soundAt_of_runParts (P G) hn (B G hn t) (hKm G hn)
  · exact QMCLeafB.VerdictSound.soundAt_of_le_one o (by omega) t hlo hhi

#print axioms QMCLeafB.Round33M4b.soundEpsOnBracket_of_family_ge2

/-- **THE STROKE, with the base case removed**: `SolutionStatement` from a `Automatic.Poly` bit plus
a `RunParts` family on the `2 ≤ n` stratum only. -/
theorem solution_of_runPartsFamily_ge2 (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (ho : OAI.MetricKMedian.Binary.Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (B : ∀ (G : QuantumMaxCutEnergy.Input), 2 ≤ G.n → ∀ t : ℚ,
      QMCLeafB.FinalStroke.RunParts o G t (P G))
    (hKm : ∀ (G : QuantumMaxCutEnergy.Input), 2 ≤ G.n → 0 < (P G).K * (P G).m) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinishLine.solution_of_bracket_verdict o
    (soundEpsOnBracket_of_family_ge2 B hKm) ho

#print axioms QMCLeafB.Round33M4b.solution_of_runPartsFamily_ge2

/-- **Consistency with the banked interface**: the phase-33 hypothesis implies the new one, so
nothing already produced is lost. -/
def family_ge2_of_family {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (B : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.FinalStroke.RunParts o G t (P G)) :
    ∀ (G : QuantumMaxCutEnergy.Input), 2 ≤ G.n → ∀ t : ℚ,
      QMCLeafB.FinalStroke.RunParts o G t (P G) :=
  fun G _ t => B G t

#print axioms QMCLeafB.Round33M4b.family_ge2_of_family

end QMCLeafB.Round33M4b


