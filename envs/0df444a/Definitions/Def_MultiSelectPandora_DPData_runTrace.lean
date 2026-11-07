-- Prove2me | Definitions.Def_MultiSelectPandora_DPData_runTrace
-- name    : MultiSelectPandora_DPData_runTrace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:12:26.995944+00:00
-- url     : https://prove2.me/theorems/90bcb421-7b09-4865-a520-fa4cc8849bf2
-- title:
--   One execution along a fixed sequence
-- statement:
--   Given a sequence of actions and realized positions and a starting state, this returns the final state and the total reward of the corresponding execution on $J$. It expresses the pathwise statements of Claim 3.1 and Lemma 3.26.
--
--   **Formalization Note** An out-of-range position is a no-op with reward $0$. The sequence is not required to use each box once.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Claim 3.1, p.7 (PDF p.8); Lemma 3.26, p.16 (PDF p.17)

import Mathlib
import Definitions.Def_MultiSelectPandora_DPData
import Definitions.Def_MultiSelectPandora_DPData_openGain
import Definitions.Def_MultiSelectPandora_DPData_claimGain
import Definitions.Def_MultiSelectPandora_DPAct
import Definitions.Def_MultiSelectPandora_insertTop

namespace MultiSelectPandora

/-- **One execution along a fixed sequence of actions and realizations**: the final state and the total reward.
Beyhaghi–Han–Luqman manuscript, Claim 3.1, p.7 (PDF p.8), and Lemma 3.26, p.16 (PDF p.17).

**Formalization Note.** An out-of-range position is a no-op with reward `0`. The trace does not check that a box is used
once: the results about traces hold without that. -/
noncomputable def DPData.runTrace {n : ℕ} {s : Fin n → ℕ} (J : DPData n s) {k : ℕ} :
    List (DPAct n × ℕ) → (Fin k → ℝ) → (Fin k → ℝ) × ℝ
  | [], α => (α, 0)
  | (.openBox i, j) :: tr, α =>
    if hj : j < s i then
      let r := J.runTrace tr (insertTop α (J.x i ⟨j, hj⟩))
      (r.1, J.openGain α i ⟨j, hj⟩ + r.2)
    else J.runTrace tr α
  | (.claim i, _) :: tr, α =>
    let r := J.runTrace tr (insertTop α (J.b i))
    (r.1, J.claimGain α i + r.2)
  | (.stop, _) :: tr, α => J.runTrace tr α

end MultiSelectPandora


