-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P37
-- name    : QAlgorithms_Papers_Independent_Support50_P37
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T21:50:00.94499+00:00
-- url     : https://prove2.me/theorems/a176aeaa-6939-4523-b8c3-e62d3ca3f5e4
-- title:
--   Definitions for Bidirectional coherent classical communication
-- statement:
--   The objects the formalized statements of *Bidirectional coherent classical communication* (arXiv:quant-ph/0412126) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Communication`: PDF p.2: the three distinct communication resources; direction is specified separately.
--   - `communicationResource`: PDF p.2: a single forward bit, coherent bit, or qubit, with the source's channel action.
--   - `outputTask`: PDF p.2, Eq.(1): independent forward/backward output blocks and output EPR pairs. The tensor ordering groups registers by owner. A zero-copy block has singleton ports.
--   - `inputBudget`: PDF p.2: the complete consumed-resource budget. Only the selected communication kind in each direction is available; EPR pairs and every use of U are separately counted.
--   - `AchievesBidirectional`: PDF p.2, Eq.(1) and signed-rate paragraph: simultaneous signed achievability. Negative rates supply calls, nonnegative rates require outputs, with no external input of a zero-rate resource. The accepted rateConstraint bounds inputs by n*(-rate+delta) or outputs below by n*(rate-delta). All resource counts and the actual sequential protocol precede every normalized input and reference in ErrorOn. Local CPTP operations include free local ancillas and discarding; no shared state, feedback, or catalyst is free. The same error bound applies jointly to both outputs and the produced EPR pairs.
--   - `averageSuccess`: PDF pp.3,5, Eq.(4) and note [14] on p.12: uniform average joint decoding success. Inputs are normalized computational-basis projectors. Alice's decoded output is b, Bob's is a; the mean runs over all 2^(mf+mb) independent, equiprobable message pairs.
--   - `AchievesAverageClassical`: PDF pp.3–7 and note [14] on p.12: the E=0 input hypothesis with average error. The finite protocol uses only U and free local operations, with no supplied EPR pair, side communication, shared random seed, or catalyst. Its schedule and maps are fixed before both messages. Local measurements are included in the final local CPTP maps; these maps can be purified, retaining their local environments, as in Eq.(5). Message lengths approach the two nonnegative rates as in the paragraph above Eq.(4).
-- source:
--   Bidirectional coherent classical communication, arXiv:quant-ph/0412126v3, https://arxiv.org/abs/quant-ph/0412126v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P34

/-! Harrow–Leung, quant-ph/0412126v3. The six stated nodes use actual finite
sequential protocols. The signed RSP-region claim is deferred in HARD.md.
Compilation is pending the batch mechanical handoff. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P37

open QAlgorithms.Papers.Independent.Support21.P19
open QAlgorithms.Papers.Independent.Renew46.P34 (rateConstraint)

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2: the three distinct communication resources; direction is specified separately. -/
inductive Communication where
  | classical | coherent | quantum
  deriving DecidableEq

/-- PDF p.2: a single forward bit, coherent bit, or qubit, with the source's channel action. -/
def communicationResource : Communication → Resource
  | .classical => cbitChannel 2
  | .coherent => cobitChannel 2
  | .quantum => qubitChannel 2

/-- PDF p.2, Eq.(1): independent forward/backward output blocks and output EPR pairs.
The tensor ordering groups registers by owner. A zero-copy block has singleton ports. -/
def outputTask (forward backward : Communication) (mf mb eo : ℕ) : Resource :=
  tensorResources
    (tensorResources (resourceTensorCopies (communicationResource forward) mf)
      (resourceTensorCopies (reverse (communicationResource backward)) mb))
    (resourceTensorCopies (entangled 2) eo)

/-- PDF p.2: the complete consumed-resource budget. Only the selected communication
kind in each direction is available; EPR pairs and every use of U are separately counted. -/
def inputBudget (forward backward : Communication) (n ei fi bi : ℕ) : Kind → ℕ
  | .main => n
  | .ebit => ei
  | .qubitF => if forward = .quantum then fi else 0
  | .qubitB => if backward = .quantum then bi else 0
  | .cobitF => if forward = .coherent then fi else 0
  | .cobitB => if backward = .coherent then bi else 0
  | .cbitF => if forward = .classical then fi else 0
  | .cbitB => if backward = .classical then bi else 0

/-- PDF p.2, Eq.(1) and signed-rate paragraph: simultaneous signed achievability.
Negative rates supply calls, nonnegative rates require outputs, with no external input
of a zero-rate resource. The accepted rateConstraint bounds inputs by n*(-rate+delta)
or outputs below by n*(rate-delta). All resource counts and the actual sequential
protocol precede every normalized input and reference in ErrorOn. Local CPTP operations
include free local ancillas and discarding; no shared state, feedback, or catalyst is free.
The same error bound applies jointly to both outputs and the produced EPR pairs. -/
def AchievesBidirectional (U : Resource) (forward backward : Communication)
    (C1 C2 E : ℝ) : Prop :=
  ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n ≥ n0,
    ∃ fi bi ei mf mb eo : ℕ,
      rateConstraint fi mf n C1 delta ∧ rateConstraint bi mb n C2 delta ∧
      rateConstraint ei eo n E delta ∧
      let target := outputTask forward backward mf mb eo
      ∃ v : Kind → ℕ, (∀ k, v k ≤ inputBudget forward backward n ei fi bi k) ∧
      ∃ F : Superop (Fin target.ai × Fin target.bi) (Fin target.ao × Fin target.bo),
        Sequential (D := Unit) (library U) target.ai target.bi target.ao target.bo v
          (fun _ => F) ∧ ErrorOn F target.map (fun _ => True) eps

/-- PDF pp.3,5, Eq.(4) and note [14] on p.12: uniform average joint decoding success.
Inputs are normalized computational-basis projectors. Alice's decoded output is b,
Bob's is a; the mean runs over all 2^(mf+mb) independent, equiprobable message pairs. -/
def averageSuccess {mf mb : ℕ}
    (F : Superop (Fin (2^mf) × Fin (2^mb)) (Fin (2^mb) × Fin (2^mf))) : ℝ :=
  (∑ a : Fin (2^mf), ∑ b : Fin (2^mb),
    (F (Matrix.single (a,b) (a,b) 1) (b,a) (b,a)).re) /
      ((2 : ℝ)^mf * (2 : ℝ)^mb)

/-- PDF pp.3–7 and note [14] on p.12: the E=0 input hypothesis with average error.
The finite protocol uses only U and free local operations, with no supplied EPR pair,
side communication, shared random seed, or catalyst. Its schedule and maps are fixed
before both messages. Local measurements are included in the final local CPTP maps;
these maps can be purified, retaining their local environments, as in Eq.(5).
Message lengths approach the two nonnegative rates as in the paragraph above Eq.(4). -/
def AchievesAverageClassical (U : Resource) (C1 C2 : ℝ) : Prop :=
  0 ≤ C1 ∧ 0 ≤ C2 ∧
    ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n ≥ n0,
      ∃ mf mb : ℕ,
        (n : ℝ)*(C1-delta) ≤ mf ∧ (mf : ℝ) ≤ n*C1 ∧
        (n : ℝ)*(C2-delta) ≤ mb ∧ (mb : ℝ) ≤ n*C2 ∧
        ∃ v : Kind → ℕ, (∀ k, v k ≤ budget n 0 0 0 0 0 0 0 k) ∧
        ∃ F : Superop (Fin (2^mf) × Fin (2^mb)) (Fin (2^mb) × Fin (2^mf)),
          Sequential (D := Unit) (library U) (2^mf) (2^mb) (2^mb) (2^mf) v
            (fun _ => F) ∧ 1-eps ≤ averageSuccess F

/-- PDF p.2: the zero-copy target still has nonempty physical ports. -/
example : (outputTask .coherent .quantum 0 0 0).ai = 1 ∧
    (outputTask .coherent .quantum 0 0 0).bo = 1 := by
  constructor <;> rfl

/-- PDF p.2: an unassisted budget forbids both backward communication and supplied EPR pairs. -/
example (n : ℕ) : inputBudget .classical .coherent n 0 0 0 .cbitB = 0 ∧
    inputBudget .classical .coherent n 0 0 0 .ebit = 0 := by
  simp [inputBudget]

/-- PDF p.2: zero rate cannot borrow an external input, including at zero block length. -/
example (used produced : ℕ) (delta : ℝ) :
    rateConstraint used produced 0 0 delta ↔ used = 0 := by
  simp [rateConstraint]

/-- PDF p.2: coherent transmission retains off-diagonal terms, unlike a dephasing cbit. -/
example : communicationResource .coherent = cobitChannel 2 ∧
    communicationResource .classical = cbitChannel 2 := by
  constructor <;> rfl

/-- PDF pp.3,5: the empty message pair is a singleton, with success one under identity. -/
example : averageSuccess (mf := 0) (mb := 0) (fun M => M) = 1 := by
  simp [averageSuccess, Matrix.single_apply]

end QAlgorithms.Papers.Independent.Support50.P37


