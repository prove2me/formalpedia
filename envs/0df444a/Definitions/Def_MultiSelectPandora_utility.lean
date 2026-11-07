-- Prove2me | Definitions.Def_MultiSelectPandora_utility
-- name    : MultiSelectPandora_utility
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:05:30.600659+00:00
-- url     : https://prove2.me/theorems/5fa46b51-7443-48ff-b4e7-99b7de652a89
-- title:
--   The expected utility $u(\pi,I)$
-- statement:
--   The expected utility of a policy is the expectation of the total value of the selected boxes minus the total inspection cost,
--   $$u=\sum_{i\in M}(A_iv_i-I_ic_i).$$
--   It is computed by recursion along the policy's decision tree. If $\pi(h)$ opens an unopened box $i$, the utility to come is
--   $$-c_i+\sum_j\mathrm{prob}_{ij}\,u(h,(i,j));$$
--   if $\pi(h)$ stops with $|S|\le k$, it is the stop value of $S$; on an invalid action it is $0$.
--
--   **Formalization Note** An invalid action scores what `stop ∅` scores, so it can only hurt. The recursion runs on a fuel starting at $n$, which is the number of unopened boxes along valid play.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.1, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_History
import Definitions.Def_MultiSelectPandora_Action
import Definitions.Def_MultiSelectPandora_Policy
import Definitions.Def_MultiSelectPandora_stopValue

namespace MultiSelectPandora

/-- **The expected utility `u(π, I)`.** Beyhaghi–Han–Luqman manuscript, §2.1, p.5 (PDF p.6): the total value of the
selected boxes minus the total inspection cost, in expectation.

**Formalization Note.** `go m h` is the utility still to come from history `h` with `m` openings left; `utility` starts
it at `I.n`, so the recursion is on the number of unopened boxes along valid play. Opening box `i` costs `c i` and branches
on its positions, independently of the past (the product form of independence). An invalid action scores `0`, which
`stop ∅` also scores, so it can only hurt. -/
noncomputable def utility (I : Inst) (k : ℕ) (π : Policy I.n) : ℝ := go I.n []
where
  /-- utility to come, with `m` openings left -/
  go : ℕ → History I.n → ℝ
    | 0, h =>
      match π h with
      | .stop S => if S.card ≤ k then stopValue I h S else 0
      | _ => 0
    | m + 1, h =>
      match π h with
      | .openBox i =>
        if h.lookup i = none then
          -I.c i + ∑ j : Fin (I.s i), I.prob i j * go m (h ++ [(i, j.val)])
        else 0
      | .stop S => if S.card ≤ k then stopValue I h S else 0
      | .invalid => 0

end MultiSelectPandora


