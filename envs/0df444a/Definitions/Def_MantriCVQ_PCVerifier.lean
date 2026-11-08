-- Prove2me | Definitions.Def_MantriCVQ_PCVerifier
-- name    : MantriCVQ_PCVerifier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:21.716607+00:00
-- url     : https://prove2.me/theorems/909445a2-35f6-4bbf-85ce-5feff9a93a20
-- title:
--   Public-coin verifiers with a fixed schedule
-- statement:
--   A **public-coin verifier** consists of a schedule and a decision machine. The schedule gives, for an input $w$, the number of slots $S(w)$, the first speaker, and the length of each slot. It is bounded by a polynomial in $|w|$ and computed in polynomial time with no oracle. Slots alternate between the two parties. The verifier's message in its slot is a uniform string of the slot's length, and there is no other randomness. After the last slot, the verifier accepts iff an oracle machine $D$, run on the input and the transcript under a polynomial clock, accepts.
--
--   This is the paper's standard fixed-schedule form. The verifier is classical and polynomial-time by construction, and it is public-coin because its messages are uniform strings and its decision is a function of the transcript and the oracle answers.
--
--   **Formalization Note** Every slot counts as one message, including a slot of length $0$. A run of $D$ that has not halted when the clock expires rejects.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3.1, p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_tup

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ

/-- A public-coin verifier in the fixed-schedule form of §3.1 (Mantri, arXiv:2610.37635 (PDF sha256
d1fab777…1d0b33), §3.1, p. 14 (PDF p. 16): "the verifier's messages are independent uniformly random
strings whose lengths, together with the alternating schedule, are determined by the input. There is
no additional private randomness. The final decision is a deterministic function of the transcript
and the oracle answers").

The schedule on an input `w` is a number of slots `S w`, the first speaker, and the length
`len w i` of each slot `i < S w`. It is computed in polynomial time with no oracle. The decision is
made after the last slot by the oracle machine `D`, run under the polynomial clock `qD`; a run that
has not halted when the clock expires rejects, so the verifier is polynomial-time by construction.

**Formalization Note** Every slot counts as one message, including a slot of length `0` (§3.1:
"Every slot counts as one message, including a slot containing the empty string"). -/
structure PCVerifier where
  /-- the number of slots on an input -/
  S : Str → ℕ
  /-- whether the prover speaks first -/
  proverFirst : Str → Bool
  /-- the length of a slot -/
  len : Str → ℕ → ℕ
  /-- a polynomial bound on the schedule -/
  schedBound : Polynomial ℕ
  S_le : ∀ w, S w ≤ schedBound.eval w.length
  len_le : ∀ w i, i < S w → len w i ≤ schedBound.eval w.length
  /-- the schedule is computable in polynomial time, with no oracle -/
  sched_poly : PolyTimeComputable fun w =>
    encNat (S w) ++ [proverFirst w] ++
      encStr ((List.range (S w)).map fun i => encNat (len w i))
  /-- the decision machine -/
  D : OTM
  /-- the clock of the decision machine -/
  qD : Polynomial ℕ

/-- Whether slot `i` on input `w` belongs to the prover: the slots alternate, starting with the
first speaker. -/
def PCVerifier.proverSlot (V : PCVerifier) (w : Str) (i : ℕ) : Bool :=
  (i % 2 == 0) == V.proverFirst w

/-- The verifier's final decision on the input `w` and the transcript `tr`: `D` is run on the encoded
pair under its clock, with oracle `O`. -/
def PCVerifier.decides (V : PCVerifier) (O : Oracle) (w : Str) (tr : List Str) : Prop :=
  V.D.result O (tup (w :: tr)) (V.qD.eval (tup (w :: tr)).length) = some true

end MantriCVQ


