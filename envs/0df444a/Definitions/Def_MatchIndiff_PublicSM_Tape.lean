-- Prove2me | Definitions.Def_MatchIndiff_PublicSM_Tape
-- name    : MatchIndiff_PublicSM_Tape
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:25:44.70079+00:00
-- url     : https://prove2.me/theorems/38b032b0-8825-462f-a4d8-b95786392a10
-- title:
--   Comparison requests, the two-bit answer code, public procedures, the mutual-pair mask and the student-local transcript check (§D.8.1)
-- statement:
--   **Mutual-pair mask (p. 99).** The public pair positions are the $m_Q$ pairs $(d,h)$ with $d$ acceptable to $h$, listed in fixed school-then-student identifier order. A certificate first publishes one acceptability bit per public pair; student $d$ checks every bit in its own row, so joint acceptance makes the published set exactly the actual set $E$ of mutually acceptable pairs.
--
--   **Comparison requests and tapes.** A comparison request names one student $d$ and two schools $h,g$; its answer is whether $h\succ_d g$, $h\sim_d g$ or $g\succ_d h$, encoded in two bits ($00$, $01$, $10$) with the fourth code forbidden. A *public procedure* decides, from the mutual-pair graph and the answers so far, which request comes next or that it stops. A comparison tape is the sequence of consecutive answers. Every student replays the same public procedure; it checks an answer against its actual report exactly when it is the named student, and otherwise continues using that answer; it rejects a missing answer, an invalid code or an unused suffix.
--
--   **Formalization Note.** `Procedure n m` is a function from the mutual-pair graph `E : Fin n → Fin m → Bool` and the list of previous answers to `Option (Fin n × Fin m × Fin m)` (`none` = stop); all other public data, including fixed choice rules, are inside it. `replay` reads two bits per request and succeeds only if the procedure stops exactly when the tape is consumed. `tapeCheck Q proc d r board` is student `d`'s check of the bit string `board` = mask (first $m_Q$ bits, `pubPairs` order) followed by the tape, using only its own row `r`. `trueAns r h g` compares `rk r (some h)` with `rk r (some g)`; `IsTrueRun` says an answer list is the execution on the actual data.
-- source:
--   Zhang, Zhao, Xu, Xi, Zhao, Structural Complexity of Matching with Indifferences, STOC 2027 submission (manuscript sha256 22dfb437…), p. 99 (§D.8.1, mutual-pair mask, comparison requests and tapes)

import Mathlib
import Definitions.Def_MatchIndiff_PublicSM_Model

namespace MatchIndiff.PublicSM

/-- The answer to a comparison request `(d, h, g)` (§D.8.1, p. 99): `h ≻_d g`, `h ∼_d g` or
`g ≻_d h`. -/
inductive Ans
  | better
  | tie
  | worse
  deriving DecidableEq

/-- The true answer of student row `r` to the comparison of schools `h` and `g`. -/
def trueAns {m : ℕ} (r : Fin m → ℕ) (h g : Fin m) : Ans :=
  if rk r (some h) < rk r (some g) then Ans.better
  else if rk r (some h) = rk r (some g) then Ans.tie else Ans.worse

/-- The two-bit code of an answer: `00` for `h ≻ g`, `01` for `h ∼ g`, `10` for `g ≻ h`; the
fourth code `11` is forbidden. -/
def decodeAns : Bool → Bool → Option Ans
  | false, false => some Ans.better
  | false, true => some Ans.tie
  | true, false => some Ans.worse
  | true, true => none

/-- A deterministic public procedure making comparison requests: given the mutual-pair graph
`E` (`E d h = true` iff `d` and `h` are mutually acceptable) and the answers received so far, it
names the next request `(d, h, g)` (student `d`, schools `h`, `g`) or stops (`none`). All other
public data (priorities, orders, a displayed matching, fixed choice rules) are fixed inside. -/
def Procedure (n m : ℕ) : Type :=
  (Fin n → Fin m → Bool) → List Ans → Option (Fin n × Fin m × Fin m)

/-- The public pair positions in fixed school-then-student identifier order: the pairs `(h, d)`
with `d` acceptable to `h` (there are `m_Q` of them). -/
def pubPairs {n m : ℕ} (Q : Fin m → Fin n → ℕ) : List (Fin m × Fin n) :=
  (List.finRange m).flatMap (fun h => ((List.finRange n).filter (fun d => Q h d ≠ 0)).map (h, ·))

/-- The mutual-pair graph read from a mask: `d` and `h` are mutual iff `(h, d)` is a public pair
whose mask bit is `1`. -/
def maskE {n m : ℕ} (Q : Fin m → Fin n → ℕ) (mask : List Bool) : Fin n → Fin m → Bool :=
  fun d h => ((pubPairs Q).zip mask).any (fun x => x.1 == (h, d) && x.2)

/-- The actual mutual-pair graph `E`: `d` acceptable to `h` and `h` acceptable to `d`. -/
def trueE {n m : ℕ} (Q : Fin m → Fin n → ℕ) (P : Fin n → Fin m → ℕ) : Fin n → Fin m → Bool :=
  fun d h => decide (Q h d ≠ 0) && decide (P d h ≠ 0)

/-- Public replay of a comparison tape: starting from the answers `acc`, ask the procedure for
the next request, read its two-bit answer from the tape, and continue. Returns the full answer
list when the procedure stops exactly when the tape is consumed; `none` on a missing answer, an
invalid code or an unused suffix. -/
def replay {n m : ℕ} (next : List Ans → Option (Fin n × Fin m × Fin m)) :
    List Ans → List Bool → Option (List Ans)
  | acc, tape =>
    match next acc, tape with
    | none, [] => some acc
    | none, _ :: _ => none
    | some _, b₁ :: b₂ :: rest =>
        match decodeAns b₁ b₂ with
        | some a => replay next (acc ++ [a]) rest
        | none => none
    | some _, _ => none

/-- The check of student `d` with row `r` on a transcript certificate `board` = mask bits (one per
public pair) followed by a comparison tape (§D.8.1, p. 99): its own mask entries are correct, the
public replay (with the graph read from the mask) succeeds and consumes the tape exactly, and every
recorded answer to a request naming `d` is `d`'s true answer. -/
def tapeCheck {n m : ℕ} (Q : Fin m → Fin n → ℕ) (proc : Procedure n m) (d : Fin n)
    (r : Fin m → ℕ) (board : List Bool) : Bool :=
  let mask := board.take (pubPairs Q).length
  let tape := board.drop (pubPairs Q).length
  let E := maskE Q mask
  decide (mask.length = (pubPairs Q).length) &&
    (List.finRange m).all (fun h => decide (Q h d ≠ 0) → (E d h == decide (r h ≠ 0))) &&
    match replay (proc E) [] tape with
    | none => false
    | some ans =>
        (List.finRange ans.length).all fun k =>
          match proc E (ans.take k) with
          | some (d', h, g) => d' != d || ans.get k == trueAns r h g
          | none => true

/-- `ans` is the execution of the procedure on the actual data: every answer is the true answer
of the named student, the procedure requests at every prefix and stops after the last answer. -/
def IsTrueRun {n m : ℕ} (proc : Procedure n m) (E : Fin n → Fin m → Bool)
    (P : Fin n → Fin m → ℕ) (ans : List Ans) : Prop :=
  (∀ (k : Fin ans.length), ∃ d h g, proc E (ans.take k) = some (d, h, g) ∧
      ans.get k = trueAns (P d) h g) ∧
    proc E ans = none

end MatchIndiff.PublicSM


