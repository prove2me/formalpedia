-- Prove2me | Definitions.Def_MultiSelectPandora_ruleValue
-- name    : MultiSelectPandora_ruleValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:08:42.645854+00:00
-- url     : https://prove2.me/theorems/95b3a1fd-59f1-4583-94b8-d48c809d3e35
-- title:
--   The expected utility of a rule
-- statement:
--   The expected utility of a rule from $(U,\alpha)$, counting the entries of $\alpha$: on "stop" it is $\sum_j\alpha_j$, and on opening $i$ it is
--   $$-c_i+\sum_j\mathrm{prob}_{ij}\,V\big(U\setminus\{i\},\mathrm{top}_k(\alpha\cup\{\mathrm{val}_{ij}\})\big).$$
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.3, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_insertTop

namespace MultiSelectPandora

/-- **The expected utility of a rule from `(U, α)`, counting the entries of `α`.** Beyhaghi–Han–Luqman manuscript, §2.3, p.6
(PDF p.7).

**Formalization Note.** `go` recurses on a fuel equal to `|U|`. -/
noncomputable def ruleValue (I : Inst) {k : ℕ} (rule : Finset (Fin I.n) → (Fin k → ℝ) → Option (Fin I.n))
    (U : Finset (Fin I.n)) (α : Fin k → ℝ) : ℝ :=
  go U.card U α
where
  /-- the recursion, with fuel `|U|` -/
  go : ℕ → Finset (Fin I.n) → (Fin k → ℝ) → ℝ
    | 0, _, α => ∑ j, α j
    | m + 1, U, α =>
      match rule U α with
      | none => ∑ j, α j
      | some i => -I.c i + ∑ j, I.prob i j * go m (U.erase i) (insertTop α (I.val i j))

end MultiSelectPandora


