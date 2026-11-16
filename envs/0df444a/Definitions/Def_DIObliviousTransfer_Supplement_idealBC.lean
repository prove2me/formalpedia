-- Prove2me | Definitions.Def_DIObliviousTransfer_Supplement_idealBC
-- name    : DIObliviousTransfer_Supplement_idealBC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:14:18.476005+00:00
-- url     : https://prove2.me/theorems/0c2e6c37-a7f5-489b-865d-b4febbd954af
-- title:
--   Definition 10 — ideal bit commitment with simulation for both parties, and its honest interfaces
-- statement:
--   Definition 10 of the paper asks for a **bit commitment with simulation for both parties**: a correct bit commitment with a commitment receipt and one opening attempt, after which the session closes, such that (i) for every QPT committer one QPT simulator extracts a bit $b^*$ by the receipt, the real and simulated states (omitting $b^*$) are computationally indistinguishable, and every accepted opening has value $b^*$ except with negligible probability; and (ii) for every QPT receiver one QPT simulator runs the commitment phase without the honest bit and, given the bit only at the opening, simulates the opening and the receiver's continuing state. The guarantees include rejection and withholding and permit sequential completed phases and delayed opening.
--
--   This module fixes the ideal functionality $\mathcal F_{\mathrm{BC}}$ that turns Definition 10 into a realization statement, with Alice the committer and Bob the receiver.
--
--   1. **Commit.** On Alice's command $(0, m)$ with $m$ a one-bit string, and only as her first command, $\mathcal F_{\mathrm{BC}}$ stores the bit and releases to the adversary only the receipt (the tag and the record length $1$). Both parties receive the receipt when the adversary delivers.
--   2. **Open.** On Alice's command $(1)$ after a commitment, $\mathcal F_{\mathrm{BC}}$ releases the stored bit $b$ to the adversary and, on delivery, gives the opening $(1, b)$ to both parties. Afterwards no command is accepted, and once the opening is delivered the session is closed.
--   3. **Rejection and withholding.** Any other command (a second commitment, an opening before a commitment, any command from Bob, a command while a delivery is pending) aborts the session. The adversary may abort at any time, and then every honest party receives $\bot$; it may also withhold delivery.
--
--   A corrupt committer submits its commitment itself. The submitted bit is the extracted $b^*$: it is fixed before the receipt can be delivered, and the only opening the functionality can deliver has value $b^*$. Against a corrupt receiver the simulator sees only the receipt, and sees the bit only when the committer opens.
--
--   The module also fixes the honest interfaces around $\mathcal F_{\mathrm{BC}}$:
--
--   - the prescribed **receiver**, which waits for the receipt, waits for the opening and outputs the opened bit;
--   - the canonical **committer**, which commits to its input and then opens;
--   - the class of honest **committer callers**: classical controllers that flip coins and issue the commit command and, whenever they decide (possibly never), the open command, perform no interparty message or device operation of their own, and stop with output $\bot$ as soon as a call or wait returns $\bot$ (rejection is terminal abort).
--
--   **Formalization Note** The functionality is a deterministic classical state machine of the base mission's type `Func`. Commands are encoded as `pack [0, m]` and `pack [1]`; the receipt is `pack [0, 1]` and the opening `pack [1, [b]]`. The phases are recorded as $0$ (nothing committed), $1$ (committed), $2$ (opening issued) and $3$ (closed).
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Definition 10, p.22 (PDF p.24); Protocol 9, 'Rejection is terminal abort', p.53 (PDF p.55)

import Mathlib
import Definitions.Def_DIObliviousTransfer_Realizes

namespace DIObliviousTransfer

namespace Supplement

/-!
Batra, Chen, Jain, Zhang, *Robust and Leakage-Resilient Device-Independent Oblivious Transfer in
MiniQCrypt*, arXiv:2610.01421 (held version, sha256 8334c039…), §2.7.2, Definition 10, p.22
(PDF p.24): bit commitment with simulation for both parties.

"A correct bit commitment has a commitment receipt and one opening attempt, after which the session
closes. It is simulation-secure if, uniformly over the admissible auxiliary and reference states:
(i) For every QPT committer, one QPT simulator extracts a bit b∗ by the receipt. Omitting this
private output, the joint corrupt state, retained honest verification state, and reference are
computationally indistinguishable from the real state. Any subsequent accepted opening has value b∗
except with negligible probability. (ii) For every QPT receiver, one QPT simulator runs the
commitment phase without the honest bit. Given that bit only at opening, it simulates the opening
and the receiver's continuing state, jointly with the reference and the prescribed honest
input–output interface. The guarantees include rejection and withholding, permit sequential
completed phases and delayed opening, and use only the declared honest device interface of
Definition 5."

**Formalization Note** (decisions D10, D11 of the base mission, and a reading of Definition 10).
Definition 10 is stated as realization (the base `Emulates`) of the ideal bit-commitment
functionality `idealBC` below, with Alice the committer and Bob the receiver.

* Commands of the committer: `pack [0, m]` commits to the one-bit string `m`; `pack [1]` opens.
  On a commit, `idealBC` stores the bit and releases to the adversary only the receipt
  `pack [0, 1]` (tag and record length); on the open command it releases `pack [1, [b]]`. Both
  parties receive these values when the adversary delivers (its empty message). A corrupt committer
  (played by the simulator) submits its commit command itself: the submitted bit is the extracted
  `b∗`, fixed before the receipt can be delivered, and the only opening `idealBC` can ever deliver
  has value `b∗` (clause (i), including "any subsequent accepted opening has value `b∗`"). Against a
  corrupt receiver the simulator sees the receipt only, and the bit only when the committer opens
  (clause (ii)).
* One opening attempt: after the open command no command is accepted, and after its delivery the
  session is closed. Any other command (a second commit, an open before a commit, a command from
  the receiver, a command while a delivery is pending) aborts the session. The adversary may abort
  at any time by `[true]` (every honest party gets `⊥`) or withhold delivery (rejection and
  withholding).
* Sequential completed phases and delayed opening: the committer's side is an arbitrary *honest
  committer caller* (`IsCommitterCaller`): a classical controller that issues the commit and,
  whenever it decides (possibly never), the open command, and treats `⊥` as terminal ("Rejection is
  terminal abort", Protocol 9). It flips coins but performs no interparty message or device
  operation of its own (interleaving with other protocols is composition, Theorem 20). The
  receiver's side is the prescribed receiver `bcReceiver`: wait for the receipt, wait for the
  opening, output the opened bit.
-/

/-- The receipt of the one-bit record: tag `0` and the record length `1`. -/
def bcReceipt : Bits := pack [encNat 0, encNat 1]

/-- The opening of bit `b`: tag `1` and the bit. -/
def bcOpening (b : Bool) : Bits := pack [encNat 1, [b]]

/-- The state of `idealBC`: the security parameter, the honest-party set, the committed bit,
the phase (`0` nothing committed, `1` committed, `2` opening issued, `3` closed), the pending
deliveries and the abort flag. -/
structure BCSt where
  lam : ℕ
  H : Option Bool
  bit : Option Bool
  phase : ℕ
  pending : List FOut
  aborted : Bool

/-- Session abort: every party receives `⊥`. -/
def BCSt.abort (st : BCSt) : BCSt × List FOut :=
  ({ st with aborted := true, pending := [] }, [.party true none, .party false none])

/-- **Definition 10**, the ideal bit commitment with committer Alice: commit with receipt, one
opening attempt, delivery and abort scheduled by the adversary. -/
def idealBC : Func where
  St := BCSt
  init := fun lam H => ⟨lam, H, none, 0, [], false⟩
  step := fun st e =>
    if st.aborted ∨ st.phase = 3 then (st, []) else
    match e with
    | .adv x =>
      if x = [true] then st.abort
      else if x = [] then
        ({ st with pending := [], phase := if st.phase = 2 then 3 else st.phase }, st.pending)
      else (st, [])
    | .party p x =>
      if p = false ∨ st.pending ≠ [] then st.abort else
      match unpack x with
      | [t, m] =>
        if bitsNat t = 0 ∧ m.length = 1 ∧ st.phase = 0 then
          let pend : List FOut := [.party true (some bcReceipt), .party false (some bcReceipt)]
          ({ st with bit := some (m.headD false), phase := 1, pending := pend }, [.adv bcReceipt])
        else st.abort
      | [t] =>
        if bitsNat t = 1 ∧ st.phase = 1 then
          match st.bit with
          | some b =>
            let pend : List FOut :=
              [.party true (some (bcOpening b)), .party false (some (bcOpening b))]
            ({ st with phase := 2, pending := pend }, [.adv (bcOpening b)])
          | none => st.abort
        else st.abort
      | _ => st.abort
  validA := fun _ => Set.univ
  validB := fun _ => Set.univ

/-- An honest committer caller: only coins, ideal calls and waits, and `⊥` from a call or a wait
ends the controller with output `⊥` (rejection is terminal abort). -/
def IsCommitterCaller {α : Type} : Code (Option α) → Prop
  | .ret _ => True
  | .coin k => ∀ b, IsCommitterCaller (k b)
  | .send _ _ => False
  | .recv _ => False
  | .dev _ _ _ => False
  | .call _ k => k none = .ret none ∧ ∀ r, IsCommitterCaller (k r)
  | .fwait k => k none = .ret none ∧ ∀ r, IsCommitterCaller (k r)

/-- The prescribed honest receiver: wait for the receipt, wait for the opening, output the opened
bit (`⊥` on abort or on a malformed delivery). -/
def bcReceiver : Code (Option Bits) :=
  .fwait fun r => match r with
    | none => .ret none
    | some _ => .fwait fun r' => match r' with
      | none => .ret none
      | some z => match unpack z with
        | [_, m] => .ret (some m)
        | _ => .ret none

/-- The canonical committer of correctness: commit to its input, then open; output `∅`. -/
def bcCommitter (x : Bits) : Code (Option Bits) :=
  .call (pack [encNat 0, x]) fun r => match r with
    | none => .ret none
    | some _ => .call (pack [encNat 1]) fun r' => match r' with
      | none => .ret none
      | some _ => .ret (some [])

/-- The ideal side: committer caller `cA` for Alice and the prescribed receiver for Bob, both
calling `idealBC`; no device batches. -/
def bcCaller (cA : ℕ → Bits → Code (Option Bits)) : Protocol :=
  { idealProtocol with
    codeA := cA
    codeB := fun _ _ => bcReceiver }

end Supplement

end DIObliviousTransfer


