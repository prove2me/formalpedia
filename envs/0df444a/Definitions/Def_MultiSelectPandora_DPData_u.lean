-- Prove2me | Definitions.Def_MultiSelectPandora_DPData_u
-- name    : MultiSelectPandora_DPData_u
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:13:13.504341+00:00
-- url     : https://prove2.me/theorems/396fe19e-88ed-4080-a2ad-aa21c4b29e02
-- title:
--   The expected total reward $u(\pi,J)$
-- statement:
--   The expected total reward of a policy $\pi$ on $J$, from the state $0$, with horizon $T=n$: the expected sum of the marginal rewards.
--
--   **Formalization Note** An action on a box already used is invalid: the process halts with no further reward, as repeating *end* would. This is the expected sum of the rewards and not a telescoped expression, since on $I^{SL}$ the telescoping of Claim 3.1 fails (p.15).
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §3.1, p.7 (PDF p.8); Definition 3.23, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_MultiSelectPandora_DPData
import Definitions.Def_MultiSelectPandora_DPData_openGain
import Definitions.Def_MultiSelectPandora_DPData_claimGain
import Definitions.Def_MultiSelectPandora_DPPolicy
import Definitions.Def_MultiSelectPandora_insertTop

namespace MultiSelectPandora

/-- **The expected total reward `u(π, J)`, from the state `0`.** Beyhaghi–Han–Luqman manuscript, §3.1, p.7 (PDF p.8), and
Definition 3.23, p.15 (PDF p.16): "`u(π, J)` denotes the expected total reward of `π` on `J`".

**Formalization Note.** The horizon is `T = n`. A closed action on a box already used is invalid: the process then halts
with no further reward, which is what repeating `end` gives. This is the expected sum of the rewards, not a telescoped
expression: on `I^SL` the telescoping fails (p.15, PDF p.16). -/
noncomputable def DPData.u {n : ℕ} {s : Fin n → ℕ} (J : DPData n s) (k : ℕ) (π : DPPolicy n) : ℝ :=
  go n Finset.univ (0 : Fin k → ℝ) []
where
  /-- the recursion on the steps left, with the unused boxes, the state and the history -/
  go : ℕ → Finset (Fin n) → (Fin k → ℝ) → List (DPAct n × ℕ) → ℝ
    | 0, _, _, _ => 0
    | m + 1, U, α, h =>
      match π h with
      | .openBox i =>
        if i ∈ U then
          ∑ j : Fin (s i), J.prob i j *
            (J.openGain α i j + go m (U.erase i) (insertTop α (J.x i j)) (h ++ [(.openBox i, j.val)]))
        else 0
      | .claim i =>
        if i ∈ U then J.claimGain α i + go m (U.erase i) (insertTop α (J.b i)) (h ++ [(.claim i, 0)])
        else 0
      | .stop => go m U α (h ++ [(.stop, 0)])

end MultiSelectPandora


