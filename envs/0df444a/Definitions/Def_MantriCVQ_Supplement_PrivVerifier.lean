-- Prove2me | Definitions.Def_MantriCVQ_Supplement_PrivVerifier
-- name    : MantriCVQ_Supplement_PrivVerifier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:02:49.541207+00:00
-- url     : https://prove2.me/theorems/9f6a32c7-5dd6-4d20-bb37-5584acba108b
-- title:
--   Private-coin polynomial-time verifier, prover strategies, acceptance probability and slot count
-- statement:
--   A **polynomial-time verifier with private coins** relative to an oracle $O$, in the alternating-slot model of §3.1. On input $w$ the verifier draws $r(|w|)$ private uniform bits, decides the first speaker with an oracle machine, and before each slot runs a second oracle machine on the input, the coins and the transcript so far, under a clock polynomial in $|w|$. The machine either continues (and its output is the verifier's message when the slot is the verifier's) or stops with a decision. A run that does not halt in time rejects, and a verifier that wants to continue past a polynomial slot cap $s(|w|)$ rejects. Slots alternate between the parties, and every slot, empty or not, is a message.
--
--   A **prover strategy** maps the input and the transcript so far to a probability distribution on the next message; it has no computational bound and does not see the coins. The **acceptance probability** of $V$ on $w$ against a strategy $\sigma$ is the average over the coins of the probability that the interaction ends in acceptance. The **number of slots used** with coins $r$ and a deterministic prover is the number of slots before the decision; the number of messages of $V$ on $w$ is the maximum of this over coins and provers.
--
--   This is the class of verifiers quantified over in Theorem 1.6.
--
--   **Formalization Note** The first speaker, the number of slots, the message lengths and the time of the decision are all adaptive. The clock depends on $|w|$ only, so the verifier is polynomial-time whatever the length of the prover's messages. Every polynomial-time private-coin verifier has this form, since its state before a slot is computable from the input, the coins and the transcript within its time bound. The published `BQPNotInIP.OracleSep.PrivateVerifier` and `GPTIP632.Classical.IPVerifier` fix the schedule (verifier first, a fixed number of rounds, fixed message lengths), which would cover fewer verifiers, and `MantriCVQ.PCVerifier` is public-coin only.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3.1, p. 14 (PDF p. 16); Theorem 1.6, p. 5 (PDF p. 7); App. B.2–B.3, pp. 52–53 (PDF pp. 54–55)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_tup

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ.Supplement

/-- A prover strategy for a verifier whose messages have no prescribed length: given the input and
the transcript so far, a probability distribution on the prover's next message (any bit string).

**Formalization Note** No computational restriction is imposed, and the prover does not see the
verifier's coins. As for the published `MantriCVQ.Strategy`, a classical or quantum prover with
private memory that exchanges classical messages induces such a strategy (the conditional law of its
next message given the transcript), and the acceptance probability depends on the prover only through
these laws. -/
abbrev PStrategy := (w : Str) → (hist : List Str) → PMF Str

/-- A polynomial-time verifier with private coins, relative to an oracle, in the alternating-slot model
of §3.1 (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3.1, p. 14 (PDF p. 16): "a randomized
polynomial-time verifier with query access to `O` exchanges classical messages with a prover … The
parties speak in alternating communication slots, with either party allowed to speak first … Every slot
counts as one message, including a slot containing the empty string … The number of messages on an
input is the maximum number of slots over all provers and random strings"; Theorem 1.6, p. 5 (PDF p. 7):
"with private coins allowed").

On an input `w` the verifier draws `coins(|w|)` private uniform bits `r`. The first speaker is decided
by the oracle machine `first` on `(w, r)`. Before every slot, and at the end, the oracle machine `M` is
run on `(w, r, transcript so far)` under the clock `clock(|w|)`: if it halts in its accepting state the
interaction continues, and the string on its work tape is the verifier's message if the slot is the
verifier's (it is ignored at a prover slot, where the prover speaks); if it halts in its rejecting state
the verifier stops with the decision given by the first bit of its work tape; if it has not halted when
the clock expires the verifier rejects. After `cap(|w|)` slots a verifier that still wants to continue
rejects.

**Formalization Note** Nothing is fixed in advance: the first speaker, the number of slots, the
message lengths and the time of the decision may depend on the input, the coins, the transcript and
the oracle answers. The clock depends on `|w|` only, so each of the at most `cap(|w|) + 2` runs takes
polynomial time in `|w|` whatever the length of the prover's messages (a long message is read only up
to the clock), and the verifier is polynomial-time by construction. Every polynomial-time private-coin
verifier is of this form: its state before a slot is a function of the input, the coins and the
transcript, computed within its time bound, and its number of slots is at most its running time. -/
structure PrivVerifier where
  /-- the number of private random bits on an input of length `n` -/
  coins : Polynomial ℕ
  /-- the slot cap -/
  cap : Polynomial ℕ
  /-- the machine deciding the first speaker (accepting state: the prover speaks first) -/
  first : OTM
  /-- the machine computing the verifier's next action -/
  M : OTM
  /-- the clock of both machines, in the input length -/
  clock : Polynomial ℕ

namespace PrivVerifier

/-- Whether slot `i` belongs to the prover, on input `w` with coins `r`: the slots alternate, starting
with the first speaker. -/
def proverSlot (V : PrivVerifier) (O : Oracle) (w r : Str) (i : ℕ) : Bool :=
  (i % 2 == 0) == (V.first.result O (tup [w, r]) (V.clock.eval w.length) == some true)

/-- The verifier's action after the transcript `tr`: `Sum.inl b` stops with the decision `b`,
`Sum.inr m` continues, with `m` the verifier's message if the next slot is its own. -/
def act (V : PrivVerifier) (O : Oracle) (w r : Str) (tr : List Str) : Bool ⊕ Str :=
  match V.M.result O (tup (w :: r :: tr)) (V.clock.eval w.length) with
  | some true => Sum.inr (V.M.output O (tup (w :: r :: tr)) (V.clock.eval w.length))
  | some false => Sum.inl ((V.M.output O (tup (w :: r :: tr)) (V.clock.eval w.length)).headD false)
  | none => Sum.inl false

/-- The probability of acceptance with coins `r` from the transcript `tr`, with `k` slots left before
the cap: the expectation under the strategy at a prover slot, the verifier's own message at a verifier
slot, and the decision when the verifier stops (rejection when it would exceed the cap). -/
noncomputable def acceptFrom (V : PrivVerifier) (O : Oracle) (σ : PStrategy) (w r : Str) :
    ℕ → List Str → ℝ
  | 0, tr =>
    match V.act O w r tr with
    | Sum.inl b => if b then 1 else 0
    | Sum.inr _ => 0
  | k + 1, tr =>
    match V.act O w r tr with
    | Sum.inl b => if b then 1 else 0
    | Sum.inr m =>
      if V.proverSlot O w r tr.length = true then
        ∑' x : Str, (σ w tr x).toReal * acceptFrom V O σ w r k (tr ++ [x])
      else acceptFrom V O σ w r k (tr ++ [m])

/-- The probability that `V` accepts `w` relative to `O` when the prover plays `σ`: the average over
the uniform coins. -/
noncomputable def acceptProb (V : PrivVerifier) (O : Oracle) (σ : PStrategy) (w : Str) : ℝ :=
  ((2 : ℝ) ^ V.coins.eval w.length)⁻¹ *
    ∑ r : Bits (V.coins.eval w.length), V.acceptFrom O σ w (List.ofFn r) (V.cap.eval w.length) []

/-- The number of slots used before the decision, from the transcript `tr` with `k` slots left before
the cap, when the coins are `r` and the prover sends `prv tr` after the transcript `tr`. -/
def slotsFrom (V : PrivVerifier) (O : Oracle) (w r : Str) (prv : List Str → Str) :
    ℕ → List Str → ℕ
  | 0, tr => tr.length
  | k + 1, tr =>
    match V.act O w r tr with
    | Sum.inl _ => tr.length
    | Sum.inr m =>
      slotsFrom V O w r prv k (tr ++ [if V.proverSlot O w r tr.length = true then prv tr else m])

/-- The number of slots (messages, empty ones included) of the interaction on input `w` with coins `r`
and the deterministic prover `prv`. The number of messages of `V` on `w` is the maximum of this over
`r` and `prv`; a randomized prover's runs are runs of deterministic provers, so this maximum is also the
maximum over all provers. -/
def slotsUsed (V : PrivVerifier) (O : Oracle) (w r : Str) (prv : List Str → Str) : ℕ :=
  V.slotsFrom O w r prv (V.cap.eval w.length) []

end PrivVerifier

end MantriCVQ.Supplement


