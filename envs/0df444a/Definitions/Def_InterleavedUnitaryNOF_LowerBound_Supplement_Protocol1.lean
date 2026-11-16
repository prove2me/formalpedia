-- Prove2me | Definitions.Def_InterleavedUnitaryNOF_LowerBound_Supplement_Protocol1
-- name    : InterleavedUnitaryNOF_LowerBound_Supplement_Protocol1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:46:03.429453+00:00
-- url     : https://prove2.me/theorems/e2dd267f-9576-47a2-8005-3af954b5a04c
-- title:
--   Protocol 1: local gates, independent runs and strict threshold
-- statement:
--   Use the unchanged published bit-string decoder at dimension $2^q$. For a visible input matrix $U$, use its polar replacement if its own Frobenius near-unitarity check passes, and the identity otherwise. This makes every gate table total using only the acting player's view. The controlled gate is
--
--   $$\operatorname{ctrl}(V)=|0\rangle\langle0|\otimes I+|1\rangle\langle1|\otimes V.$$
--
--   Bob initializes a fresh one-clean-qubit register and applies the Hadamard to the control. The ten subsequent controlled gates use, chronologically, $E_2,D_2,C_2,B_2,A_2,E_1,D_1,C_1,B_1,A_1$, acted on by Bob, Alice, Charlie, Alice, Charlie, Bob, Alice, Charlie, Alice, Charlie. The register is transferred between each adjacent pair of these ten gates. Charlie measures the fixed projectors $|+\rangle\langle+|\otimes I$ and $|-\rangle\langle-|\otimes I$.
--
--   In $L$ independent runs, encode these outcomes as $\omega_i=1$ and $-1$. Charlie outputs one precisely when
--
--   $$\frac1L\sum_{i=1}^L\omega_i>\frac12.$$
--
--   For the default error the source sets $L=100$. This construction contains no assumed success condition; validity and promise correctness are conclusions of Theorem 1.2.
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), Protocol 1, pp.8–9; §2 input representation, p.7

import Mathlib
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_Supplement_Polar
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_Supplement_Quantum

namespace InterleavedUnitaryNOF.LowerBound.Supplement

/-- A total local operation: malformed matrices use the identity. This tests
only the matrix visible to the acting player, never the global IUP promise. -/
noncomputable def localPolar {m : ℕ} (U : Mat m) : Mat m := by
  classical
  exact if nearUnitary U then polar U else 1

/-- |0><0| tensor I + |1><1| tensor U. -/
noncomputable def controlled {q : ℕ} (U : Mat (2^q)) : QMat q :=
  fun i j => if i.1 = j.1 then
    if i.1 then U i.2 j.2 else (1 : Mat (2^q)) i.2 j.2 else 0

noncomputable def hadamard (q : ℕ) : QMat q :=
  fun i j => if i.2 = j.2 then
    if i.1 && j.1 then -(1 / (Real.sqrt 2 : ℂ)) else 1 / (Real.sqrt 2 : ℂ)
    else 0

/-- Outcome true corresponds to |+><+| tensor I; false to |-><-| tensor I. -/
noncomputable def plusProjector (q : ℕ) : QMat q :=
  fun i j => if i.2 = j.2 then 1/2 else 0

/-- Protocol 1, p.8. The ten chronological gates are E₂,D₂,C₂,B₂,A₂,
E₁,D₁,C₁,B₁,A₁. Left multiplication of column states reverses this list to
the published word A₁B₁C₁D₁E₁A₂B₂C₂D₂E₂. -/
noncomputable def protocol1Run (n q : ℕ) : QuantumRun (Bits n) (Bits n) (Bits n) where
  q := q
  initialOwner := .bob
  gates := [
    .bob (fun _ _ => hadamard q),
    .bob (fun _ z => controlled (localPolar (decodeMatrix (2^q) z 1))),
    .alice (fun y _ => controlled (localPolar (decodeMatrix (2^q) y 3))),
    .charlie (fun x _ => controlled (localPolar (decodeMatrix (2^q) x 3))),
    .alice (fun y _ => controlled (localPolar (decodeMatrix (2^q) y 2))),
    .charlie (fun x _ => controlled (localPolar (decodeMatrix (2^q) x 2))),
    .bob (fun _ z => controlled (localPolar (decodeMatrix (2^q) z 0))),
    .alice (fun y _ => controlled (localPolar (decodeMatrix (2^q) y 1))),
    .charlie (fun x _ => controlled (localPolar (decodeMatrix (2^q) x 1))),
    .alice (fun y _ => controlled (localPolar (decodeMatrix (2^q) y 0))),
    .charlie (fun x _ => controlled (localPolar (decodeMatrix (2^q) x 0)))]
  finalOwner := .charlie
  projector := plusProjector q

/-- L independent runs and the source's strict threshold for the average of
the ±1 outcomes. The default witness uses L=100. -/
noncomputable def protocol1 (n q L : ℕ) : QuantumProtocol (Bits n) (Bits n) (Bits n) where
  run := protocol1Run n q
  repetitions := L
  output := fun ω => decide (((∑ i : Fin L, if ω i then (1 : ℝ) else -1) / L) > 1/2)

end InterleavedUnitaryNOF.LowerBound.Supplement


