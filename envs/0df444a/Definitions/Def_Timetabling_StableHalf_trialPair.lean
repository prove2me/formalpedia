-- Prove2me | Definitions.Def_Timetabling_StableHalf_trialPair
-- name    : Timetabling_StableHalf_trialPair
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:29:44.134309+00:00
-- url     : https://prove2.me/theorems/97616e1d-f913-4d89-8dd1-654d23a47684
-- title:
--   A decision and its reverse, examined together
-- statement:
--   For a partial assignment $a$ and an open pair $j$, two trials are started from $a$: the decision $x_j$ and the reverse decision $\bar x_j$. They are run **interleaved**, one scan step each, starting with $x_j$:
--
--   1. as soon as one trial is done with assignment $a'$, the result is $a'$ (that decision becomes *permanent*);
--   2. once one trial has failed, the other continues alone;
--   3. if both fail, the result is *failure*: no timetable can exist.
--
--   This is the paper's rule "we go back to the last decision and we reverse it (if the reverse decision has not been examined yet). If the reverse decision has been examined previously, then no timetable can exist [...] then we consider the last decision as permanent".
--
--   **Formalization Note** The page examines the reverse decision after the first one fails and does not specify how the steps of the two trials are ordered; this definition fixes the interleaved order. Interleaving bounds the work spent on a failed trial by the work of its successful twin, which is what makes the total cost $O(n^2)$. The fuel $4(n+1)^2$ is more than twice the length of a trial, so it is never exhausted.
-- source:
--   de Werra (1985), proof of Proposition 2.4, p. 155, "In such a case, we go back to the last decision and we reverse it (if the reverse decision has not been examined yet) ... then we consider the last decision as permanent". D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_StableHalf_propStep

namespace Timetabling.StableHalf

/-- **A decision and its reverse, examined together.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), proof of Proposition 2.4, p. 155:
"we go back to the last decision and we reverse it (if the reverse decision has not been examined
yet). If the reverse decision has been examined previously, then no timetable can exist [...] If
we have taken all implications into account and there are still some teachers whose schedule is
not fixed, then we consider the last decision as permanent".

For an open pair `j`, the two trials "choose `(j, true)`" and "choose `(j, false)`" are started
from `a` and run **interleaved, one `propStep` each, starting with `(j, true)`**:

* as soon as one trial is `done a'`, the result is `some a'` (its assignment becomes permanent);
* when one trial has failed, the other continues alone;
* when both have failed, the result is `none` (no timetable can exist).

**Formalization Note.** The page examines the reverse decision after the first one fails; the
order of the two trials' steps is not specified there, and the interleaving fixes it. It is what
bounds a failed trial by the cost of its successful twin. The fuel `4 (n + 1)^2` exceeds twice the
length `n (2n + 1) + 1` of one trial plus one, so it is never exhausted (exhaustion would also
return `none`). -/
def trialPair {n : ℕ} (adj : Fin n × Bool → Fin n × Bool → StateM ℕ Bool)
    (a : Fin n → Option Bool) (j : Fin n) : StateM ℕ (Option (Fin n → Option Bool)) :=
  go (4 * (n + 1) ^ 2) (.running (Function.update a j (some true)) [(j, true)] 0)
    (.running (Function.update a j (some false)) [(j, false)] 0) true
where
  /-- Run the two trials `t₁`, `t₂` with fuel; `turn = true` means `t₁` moves next. -/
  go : ℕ → Trial n → Trial n → Bool → StateM ℕ (Option (Fin n → Option Bool))
    | _, .done a', _, _ => pure (some a')
    | _, _, .done a', _ => pure (some a')
    | _, .failed, .failed, _ => pure none
    | 0, _, _, _ => pure none
    | f + 1, t₁@(.running _ _ _), .failed, _ => do
      let t ← propStep adj t₁
      go f t .failed false
    | f + 1, .failed, t₂@(.running _ _ _), _ => do
      let t ← propStep adj t₂
      go f .failed t true
    | f + 1, t₁@(.running _ _ _), t₂@(.running _ _ _), turn =>
      if turn then do
        let t ← propStep adj t₁
        go f t t₂ false
      else do
        let t ← propStep adj t₂
        go f t₁ t true

end Timetabling.StableHalf


