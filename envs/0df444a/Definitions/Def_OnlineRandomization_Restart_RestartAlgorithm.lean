-- Prove2me | Definitions.Def_OnlineRandomization_Restart_RestartAlgorithm
-- name    : OnlineRandomization_Restart_RestartAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T08:12:20.45598+00:00
-- url     : https://prove2.me/theorems/85d19e44-3ab0-4e1e-a42f-c822c3188b99
-- title:
--   The set $R_H$ and the restart algorithm built from an algorithm $A_H$
-- statement:
--   Fix a request-answer game $F$ with off-line optimum $c$ and a real number $H$.
--
--   The set $R_H$ consists of all request sequences $r$ such that every proper prefix $r' \ne r$ of $r$ has $c(r') \le H$. It is closed under taking prefixes.
--
--   Given a deterministic online algorithm $A_H$, the **restart algorithm** processes the requests one at a time, keeping a *current segment* (initially empty). On a new request $x$: if the current segment is nonempty and appending $x$ to it produces a sequence outside $R_H$, the current segment is closed and a new segment $(x)$ is started; otherwise $x$ is appended to the current segment. The algorithm answers $x$ as $A_H$ would answer the current segment, that is, it simulates $A_H$ and, as soon as the request sequence is no longer in $R_H$, starts over as if it had received no previous requests.
--
--   The closed segments followed by the final current segment form the decomposition
--
--   $$r = r(1)\, r(2) \cdots r(t)$$
--
--   of the request sequence ($t = 0$ for the empty sequence). When $f_0 \le H$, every one-request sequence lies in $R_H$, and $r(1)$ is the longest prefix of $r$ in $R_H$, $r(2)$ the longest prefix in $R_H$ of the remaining suffix, and so on.
--
--   **Formalization Note** The construction is written as a left fold over the request list with state (closed segments, current segment); `currentSegment F H r` is the current segment after reading $r$, `segments F H r` the decomposition, and `restart F H AH` the algorithm answering `AH (currentSegment F H r)` on the requests $r$. Membership in $R_H$ is decided classically. The rule "start a new segment only when the current one is nonempty" makes the construction total; under $f_0 \le H$, the condition of Theorem 4.1, it coincides with the page's greedy decomposition into longest prefixes in $R_H$.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript pp. 17-18, §4, proof of Theorem 4.1 (definition of R_H and of the algorithm)

import Mathlib
import Definitions.Def_OnlineRandomization_Restart_Model

namespace OnlineRandomization.Restart

open Classical in
/-- p. 17: `r ∈ R_H` iff every proper prefix `r'` of `r` (`r' ≠ r`) has `c(r') ≤ H`. -/
def InRH {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ) (r : List R) : Prop :=
  ∀ r' : List R, r' <+: r → r' ≠ r → F.opt r' ≤ H

open Classical in
/-- p. 18: one step of the restart rule on a new request `x`. The state is
`(closed segments, current segment)`. If the current segment is nonempty and appending `x`
leaves `R_H`, the current segment is closed and a new one starts with `x` ("the algorithm
starts over, as if it had not received any previous requests"); otherwise `x` is appended to
the current segment. -/
noncomputable def restartStep {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (s : List (List R) × List R) (x : R) : List (List R) × List R :=
  if s.2 ≠ [] ∧ ¬ InRH F H (s.2 ++ [x]) then (s.1 ++ [s.2], [x]) else (s.1, s.2 ++ [x])

/-- The state of the restart rule after reading the requests `r` in order. -/
noncomputable def restartState {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (r : List R) : List (List R) × List R :=
  r.foldl (restartStep F H) ([], [])

/-- The current segment after the requests `r`: the requests received since the last restart. -/
noncomputable def currentSegment {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (r : List R) : List R :=
  (restartState F H r).2

/-- p. 18: the decomposition `r = r(1) r(2) ⋯ r(t)` of a request sequence into segments
(the closed segments followed by the current one; `[]` for `r = []`). -/
noncomputable def segments {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (r : List R) : List (List R) :=
  if (restartState F H r).2 = [] then (restartState F H r).1
  else (restartState F H r).1 ++ [(restartState F H r).2]

/-- p. 18: the restart algorithm built from `A_H`: on requests `r_1, …, r_i` it answers as
`A_H` answers the current segment, i.e. it simulates `A_H` and starts over whenever the
request sequence leaves `R_H`. -/
noncomputable def restart {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (AH : DetAlg R A) : DetAlg R A :=
  fun r => AH (currentSegment F H r)

end OnlineRandomization.Restart


