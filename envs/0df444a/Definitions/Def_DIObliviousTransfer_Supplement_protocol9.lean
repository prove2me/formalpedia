-- Prove2me | Definitions.Def_DIObliviousTransfer_Supplement_protocol9
-- name    : DIObliviousTransfer_Supplement_protocol9
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:15:44.099195+00:00
-- url     : https://prove2.me/theorems/d877fa3f-fba8-4ddc-a21f-1bf09130ea8b
-- title:
--   Protocol 9 — one-window DI bit commitment with a certified opening
-- statement:
--   Protocol 9 of the paper is a one-window device-independent bit commitment with a certified opening. Alice commits to $b\in\{0,1\}$ and Bob receives. The protocol runs the masked commit-and-prove protocol (Protocol 5) in Alice's direction only, with capacity $q=1$ and a string commitment $S$ as source. Any rejection is a terminal abort.
--
--   1. **Preprocessing (Alice).** Alice samples a uniform mask $\mu\in\{0,1\}$ and commits to it with $S$, with Bob as receiver. She keeps the transcript $\tau$ and her native witness $w$; Bob keeps his verification record. This is the only step that uses devices: the batches of $S$.
--   2. **Commitment (Alice).** Alice sends the one-bit record $c=b\oplus\mu$ with its identifier.
--   3. **Receipt (Bob).** Bob checks the masked-record syntax, saves $c$ and returns the receipt.
--   4. **Opening (Alice).** When her caller issues the open command, Alice publishes $b$ and proves, with the zero-knowledge proof system of the predicate phase, the statement
--   $$\exists u,w:\ \mathrm{OpenVer}_{\mathrm{str}}(\tau,u,w)=1\ \wedge\ c\oplus u=b .$$
--   5. **Verification (Bob).** Bob checks the routing and syntax and verifies the proof. On acceptance he outputs $b$.
--
--   Alice's side runs an honest committer caller, which issues the commit and open commands. Bob's side runs the prescribed receiver. Both receive their deliveries in the format of the ideal bit commitment $\mathcal F_{\mathrm{BC}}$.
--
--   **Formalization Note** Steps 2–5 are the published Steps 2–5 of Protocol 5 (`p5OnCall` for Alice, `p5OnWait` for Bob) with capacity $1$. The predicate language has the single full-projection predicate $P(M,y)=[M=y]$, and the authorized schedule admits exactly one commitment of a one-bit record by Alice followed by one check. The source $S$ is a parameter; Theorem 16 instantiates it with Protocol 7 at $q=1$. The protocol declares exactly the batches of $S$.
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Protocol 9, pp.53–54 (PDF pp.55–56); Protocol 5, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_DIObliviousTransfer_protocol5
import Definitions.Def_DIObliviousTransfer_Supplement_idealBC

namespace DIObliviousTransfer

namespace Supplement

/-!
Batra, Chen, Jain, Zhang, *Robust and Leakage-Resilient Device-Independent Oblivious Transfer in
MiniQCrypt*, arXiv:2610.01421 (held version, sha256 8334c039…), §6.1, Protocol 9, pp.53–54
(PDF pp.55–56): one-window DI bit commitment with a certified opening.

"Alice commits to b ∈ {0, 1}; Bob receives. Use Protocol 5 in Alice's direction only, with
capacity q = 1 and source Protocol 7. Rejection is terminal abort. 1. Alice (preprocessing).
Complete the mask-bank preprocessing with Bob. Its mask is µ ∈ {0, 1} and its transcript is τ.
2. Alice (commitment). Create the one-bit record b by sending c = b ⊕ µ with its prescribed
identifier. 3. Bob (receipt). Verify the masked-record syntax, save c, and send the receipt.
4. Alice (opening). Publish the full projection value b and prove
∃u, w : OpenVer_str(τ, u, w) = 1 ∧ c ⊕ u = b by the predicate phase of masked CP. 5. Bob
(verification). Verify that projection and send accept or reject. On acceptance output b. Close the
session and discard all call-local private state; Alice does the same on the result. … Only
preprocessing uses devices."

**Formalization Note** (decisions D10, D11, D14 of the base mission). Protocol 9 is built from the
published Steps 2–5 of Protocol 5 (`p5OnCall` for the owner Alice, `p5OnWait` for the verifier Bob)
with capacity `q = 1`, in Alice's direction only: Step 1 is one run of the source `S` with Alice as
committer of a uniform mask `µ ∈ {0,1}` on the source's own batches (Bob's bank is never created).
The predicate language `predBC` has the single full-projection predicate `P(M, y) = [M = y]`, and
the authorized schedule `schedBC` admits exactly one commit of a one-bit record by Alice followed by
one check; so Step 4 proves exactly `∃u, w : OpenVer_str(τ, u, w) = 1 ∧ c ⊕ u = b` (relation (16)
of the base for this predicate). The committer caller's commands (`pack [0, m]`, `pack [1]`) are
translated into the CP commands `pack [0, 0, 1, m]` (record `0` of length `1`) and
`pack [1, pack [0], ∅, [b]]`; the CP receipt and certificate are returned to the callers in the
format of `idealBC` (`bcReceipt`, `bcOpening b`). Any failed check is a global abort (`⊥`).
The source is a parameter; Theorem 16 instantiates it with the published Protocol 7 at `q = 1`.
-/

open Code

/-- The predicate language of Protocol 9: the single full-projection predicate
`P(M, y) = [M = y]`. -/
def predBC : ℕ → PredLang := fun _ =>
  { Pred := Unit
    enc := fun _ => []
    dec := fun _ => some ()
    eval := fun _ M y => decide (M = y) }

/-- The command is a commit of a one-bit record. -/
def isCommit1 (cmd : Bits) : Bool :=
  match unpack cmd with
  | [t, _, _, M] => decide (bitsNat t = 0 ∧ M.length = 1)
  | _ => false

/-- The command is a check with a one-bit public value. -/
def isCheck1 (cmd : Bits) : Bool :=
  match unpack cmd with
  | [t, _, _, y] => decide (bitsNat t = 1 ∧ y.length = 1)
  | _ => false

/-- The authorized schedule of Protocol 9: Alice's one-bit commit, then one check by Alice. -/
def schedBC (hist : List (Bool × Bits)) (c : Bool × Bits) : Bool :=
  c.1 && match hist with
    | [] => isCommit1 c.2
    | [_] => isCheck1 c.2
    | _ => false

/-- The capacity `q = 1`. -/
def qOne : ℕ → ℕ := fun _ => 1

/-- Alice's Protocol 9 state: the Protocol 5 state of her bank and the committed bit. -/
structure P9St where
  core : P5St
  bit : Option Bool

/-- Step 1 for Alice: sample `µ ∈ {0,1}` and commit to it with the source, as committer. -/
noncomputable def p9PreA (S : StrCom) (lam : ℕ) : Prog P9St := do
  let mu ← Prog.bits 1
  let z ← (OptionT.mk (S.commit lam mu) : Prog Bits)
  match unpack z with
  | [τ, w] => pure ⟨⟨mu, τ, w, [], [], [], []⟩, none⟩
  | _ => failure

/-- Step 1 for Bob: receive the source commitment; keep its verification record `τ`. -/
noncomputable def p9PreB (S : StrCom) (lam : ℕ) : Prog P5St := do
  let τo ← (OptionT.mk (S.receive lam) : Prog Bits)
  pure ⟨[], [], [], τo, [], [], []⟩

/-- Steps 2 and 4 for Alice on a committer-caller command. -/
noncomputable def p9OnCallA (S : StrCom) (ZK : (Bits → Bits → Bool) → (ℕ → ℕ) → Protocol)
    (lam : ℕ) (st : P9St) (cmd : Bits) : Prog (P9St × Option Bits) :=
  match unpack cmd with
  | [t, m] =>
    if bitsNat t = 0 ∧ m.length = 1 then do
      let r ← p5OnCall S ZK predBC schedBC qOne lam true st.core
        (pack [encNat 0, encNat 0, encNat 1, m])
      pure (⟨r.1, some (m.headD false)⟩, some bcReceipt)
    else failure
  | [t] =>
    if bitsNat t = 1 then
      match st.bit with
      | some b => do
        let r ← p5OnCall S ZK predBC schedBC qOne lam true st.core
          (pack [encNat 1, pack [encNat 0], [], [b]])
        pure (⟨r.1, some b⟩, some (bcOpening b))
      | none => failure
    else failure
  | _ => failure

/-- Steps 3 and 5 for Bob when the receiver waits for a delivery. -/
noncomputable def p9OnWaitB (S : StrCom) (ZK : (Bits → Bits → Bool) → (ℕ → ℕ) → Protocol)
    (lam : ℕ) (st : P5St) : Prog (P5St × Option Bits) := do
  let r ← p5OnWait S ZK predBC schedBC qOne lam false st
  match r.2 with
  | some z =>
    match unpack z with
    | [_, _, _, _] => pure (r.1, some bcReceipt)
    | [msg, _] =>
      match unpack msg with
      | [_, _, _, y] => do
        Prog.check (decide (y.length = 1))
        pure (r.1, some (pack [encNat 1, y]))
      | _ => failure
    | _ => failure
  | none => failure

/-- **Protocol 9** with source `S`, proof system `ZK` and committer caller `cA` (Alice); Bob runs
the prescribed receiver. Only Step 1 uses devices: the source's batches. -/
noncomputable def protocol9 (S : StrCom) (ZK : (Bits → Bits → Bool) → (ℕ → ℕ) → Protocol)
    (cA : ℕ → Bits → Code (Option Bits)) : Protocol where
  codeA := fun lam x => (do
    let st ← p9PreA S lam
    let r ← (OptionT.mk (Code.plug
      (fun s c => (p9OnCallA S ZK lam s c).run)
      (fun _ => (failure : Prog (P9St × Option Bits)).run) st (cA lam x)) : Prog (Option Bits))
    match r with | some o => pure o | none => failure).run
  codeB := fun lam _ => (do
    let st ← p9PreB S lam
    let r ← (OptionT.mk (Code.plug
      (fun _ _ => (failure : Prog (P5St × Option Bits)).run)
      (fun s => (p9OnWaitB S ZK lam s).run) st bcReceiver) : Prog (Option Bits))
    match r with | some o => pure o | none => failure).run
  nb := S.nb
  ng := S.ng
  group := S.group
  coords := S.coords
  rowsA := S.committerRows
  steps := fun lam => S.steps lam + 2 ^ lam

end Supplement

end DIObliviousTransfer


