-- Prove2me | Definitions.Def_EntangledPIR_clientStep
-- name    : EntangledPIR_clientStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:11:17.800026+00:00
-- url     : https://prove2.me/theorems/f9ebcff4-d9b9-4fd6-9670-ea4679ba213c
-- title:
--   The client of Protocol 1, one round at a time
-- statement:
--   The client of Protocol 1. Its input in a round is the public parameters, the index $x$, its random string and the messages of the servers in the earlier rounds. With the masks $a_{i,j}$, positions $t$ and $r_1,\dots,r_\lambda$ read from the random string:
--
--   1. Round 0: it sends all $a_{i,j}$ to A and to B the masks $b_{i,j}=a_{i,j}$ for $j\ne t_i$, and $b_{i,t_i}=a_{i,t_i}\oplus y_i$.
--   2. Round 1: on a well-formed report $e$ it sends $t$ to B; otherwise it sends the fixed abort message to both.
--   3. Round 2: it accepts if $f_{i,j}=e_{i,j}$ on every trap, in the prescribed format, and sends its decision to B; on abort it also sends the abort message to A.
--   4. Round 3: on a well-formed answer $(K,v)$ it sends $t$ and $K$ to A; otherwise the abort message.
--   5. Afterwards it outputs $u\oplus v$ on a well-formed $u$, and otherwise aborts.
--
--   Unexpected messages are ignored, and after an abort it sends nothing.
--
--   **Formalization Note** The database does not occur, so the client is the same for every database. One function for all $n,m,\lambda$ gives uniformity. The list of steps is Figure 4 with its messages grouped in four rounds, so A reports before $t$ leaves the client, and A gets $t$ only with $K$, only on acceptance.
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Protocol 1, p.26; Figure 4, p.25; A.1, p.53

import Definitions.Def_EntangledPIR_table
import Definitions.Def_EntangledPIR_serialize

/-!
Mantri, *Private Information Retrieval from Two Entangled Servers*, manuscript (Nov. 2026), Protocol 1,
p.26, A.1, p.53: the client.
-/

namespace EntangledPIR

/-- The input of one step of the client: the public parameters, the index `x`, the random string
`tape`, and the messages `srv` of the servers in the earlier rounds, a pair (message of A, message of B)
per round. The round is `srv.length`. The database does not occur, so the client is the same for every
database (p.10). -/
structure ClientInput where
  /-- index length -/
  n : ℕ
  /-- record length -/
  m : ℕ
  /-- security parameter -/
  lam : ℕ
  /-- the index -/
  x : List Bool
  /-- the random string -/
  tape : List Bool
  /-- the messages of the servers in the earlier rounds -/
  srv : List (List Bool × List Bool)

/-- What the client does in a round: its message to A, its message to B (empty lists stand for no
message), and, after the last round, its output (`none` for abort and for all earlier rounds). -/
structure ClientOutput where
  /-- the message to A -/
  toA : List Bool
  /-- the message to B -/
  toB : List Bool
  /-- the output, or abort -/
  out : Option (List Bool)

/-- The number of rounds of the schedule. -/
def numRounds : ℕ := 4

/-- The fixed abort message of step 3(d), and the decision bit "abort" of step 3(c). -/
def abortMsg : List Bool := [false]

/-- The decision bit "accept" of step 3(c). -/
def acceptMsg : List Bool := [true]

section Tape
variable (n lam : ℕ) (tape : List Bool)

/-- `r_1, …, r_λ` read from the random string. -/
def tapeR : Fin lam → Bits (queryLen n lam) :=
  fun s => chunk tape (s.val * queryLen n lam) (queryLen n lam)

/-- The positions `t ∈ [4]^k` read from the random string (two uniform bits each). -/
def tapeT : Fin (shareCount n lam) → Fin 4 :=
  parsePos _ (tape.drop (lam * queryLen n lam))

/-- The masks `a_{i,j}` read from the random string. -/
def tapeA : CopyIdx (shareCount n lam) → Bits (queryLen n lam) :=
  parseMat _ _ (tape.drop (lam * queryLen n lam + 2 * shareCount n lam))

/-- The masks of step 1(c): `b_{i,j} = a_{i,j}` for `j ≠ t_i`, and `b_{i,t_i} = a_{i,t_i} ⊕ y_i`. -/
noncomputable def clientB (x : Bits n) :
    CopyIdx (shareCount n lam) → Bits (queryLen n lam) :=
  fun c => if c.2 = tapeT n lam tape c.1
    then bxor (tapeA n lam tape c) (queries lam x (tapeR n lam tape) c.1)
    else tapeA n lam tape c

end Tape

/-- The index read from its list. -/
def listBits (n : ℕ) (l : List Bool) : Bits n := chunk l 0 n

/-- `A` reported well-formed outcomes (`4kd` bits). -/
def reportOk (k d : ℕ) (e : List Bool) : Bool := decide (e.length = 4 * k * d)

/-- **The client of Protocol 1**, p.26, one round at a time, with the schedule (0-based rounds):

* round 0: steps 1(a–c), masks `a` to A and `b` to B; A answers `e` (step 2);
* round 1: step 3(a), `t` to B, after a well-formed report, otherwise it aborts, sending the fixed
  abort message to both; B answers `f` (step 3(b));
* round 2: steps 3(c–d), it accepts if `f_{i,j} = e_{i,j}` on every trap in the prescribed format, and
  sends the decision to B, and on abort also the abort message to A; B answers `K, v` (step 4);
* round 3: step 5(a), `t, K` to A, if `K, v` is well-formed, otherwise the abort message to A; A answers
  `u` (step 5(b));
* after round 3: step 5(c), it outputs `u ⊕ v`, if the answer `u` is well-formed, and otherwise aborts.

Messages of a server that the schedule does not expect are ignored, and after an abort it sends
nothing. **Formalization Note.** The client's whole computation is this function of its input. One
function for all `n, m, λ` gives uniformity, and the database does not occur in it. -/
noncomputable def clientStep (inp : ClientInput) : ClientOutput :=
  let k := shareCount inp.n inp.lam
  let d := queryLen inp.n inp.lam
  let t := tapeT inp.n inp.lam inp.tape
  let a := tapeA inp.n inp.lam inp.tape
  let b := clientB inp.n inp.lam inp.tape (listBits inp.n inp.x)
  match inp.srv with
  | [] => ⟨serMat a, serMat b, none⟩
  | [m0] =>
    if reportOk k d m0.1 then ⟨[], serPos t, none⟩ else ⟨abortMsg, abortMsg, none⟩
  | [m0, m1] =>
    if reportOk k d m0.1 then
      if m1.2 = serTraps t (parseMat k d m0.1) then ⟨[], acceptMsg, none⟩
      else ⟨abortMsg, abortMsg, none⟩
    else ⟨[], [], none⟩
  | [m0, m1, m2] =>
    if reportOk k d m0.1 ∧ m1.2 = serTraps t (parseMat k d m0.1) then
      if m2.2.length = k * d + inp.m then ⟨serPos t ++ m2.2.take (k * d), [], none⟩
      else ⟨abortMsg, [], none⟩
    else ⟨[], [], none⟩
  | [m0, m1, m2, m3] =>
    if reportOk k d m0.1 ∧ m1.2 = serTraps t (parseMat k d m0.1) ∧
        m2.2.length = k * d + inp.m ∧ m3.1.length = inp.m then
      ⟨[], [], some (List.zipWith xor m3.1 (m2.2.drop (k * d)))⟩
    else ⟨[], [], none⟩
  | _ => ⟨[], [], none⟩

end EntangledPIR


