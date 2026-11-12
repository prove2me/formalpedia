-- Prove2me | Definitions.Def_DIObliviousTransfer_protocol5
-- name    : DIObliviousTransfer_protocol5
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T09:10:25.847225+00:00
-- url     : https://prove2.me/theorems/5b7ae693-1093-43a9-ab51-5c044e3368ed
-- title:
--   Protocol 5: masked commit-and-prove over a source commitment
-- statement:
--   This module transcribes Protocol 5 for both owner directions, substituted into a caller.
--
--   - *Preprocessing:* each owner commits to a uniform mask $\mu\in\mathbb F_2^q$ with the source string commitment on its own batch (Alice's bank first).
--   - *Records:* a new record $M_a$ is sent as $c_a=M_a\oplus\mu_{I_a}$ on the next unused interval.
--   - *Receipts:* the verifier checks the record and returns a metadata-only receipt.
--   - *Predicates:* the owner publishes the request and proves the NP statement (16), $\exists u,w:\mathrm{OpenVer}_{\mathrm{str}}(\tau,u,w)=1\wedge P((c_{a_1}\oplus u_{I_{a_1}})\|\cdots,y)=1$, with the ZK proof system; the verifier checks routing and schedule and verifies the proof.
--
--   The caller's ideal commit-and-prove calls and waits are replaced by these steps.
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Protocol 5 and (16), p.38

import Mathlib
import Definitions.Def_DIObliviousTransfer_SelData
import Definitions.Def_DIObliviousTransfer_idealCP
import Definitions.Def_DIObliviousTransfer_IsExtractableStringCommitment
import Definitions.Def_DIObliviousTransfer_ZKSpec

namespace DIObliviousTransfer

/-!
Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held version, sha256 8334c039…), Protocol 5, p.38:
masked commit-and-prove with one preprocessing commitment per owner, and its NP statement (16).

"1. Alice (preprocessing). Sample µ ←U F₂^q and complete a string commitment to µ, with Bob as
receiver. Save its transcript τ, native witness w, and an allocation counter initially zero. Abort
if preprocessing fails. 2. Alice (new record). On input M_a ∈ F₂^{n_a}, allocate the next unused
interval I_a ⊆ [q] of length n_a. Abort on insufficient capacity. Send the tagged tuple
(a, I_a, c_a), c_a = M_a ⊕ µ_{I_a}. 3. Bob (receipt). Check the identifier, role, prescribed
length, and next unused interval. Store (a, I_a, c_a), advance the counter, and send the
mtdata-only receipt. 4. Alice (predicate). Publish an authorized request (a, P, y) for previously
receipted same-owner records a = (a₁, …, a_r). Abort unless their handles, roles, lengths, saved
intervals, and schedule are valid. If P(M_{a₁}‖⋯‖M_{a_r}, y) = 0, abort. Otherwise prove
∃u, w : OpenVer_str(τ, u, w) = 1 ∧ P((c_{a₁} ⊕ u_{I_{a₁}})‖⋯‖(c_{a_r} ⊕ u_{I_{a_r}}), y) = 1 (16)
using the same bank witness (µ, w) for every component. … 5. Bob (certificate). Check routing and
syntax against the saved tuple …, and verify the proof. … Steps 2–5 may repeat on the public
polynomial schedule."

**Formalization Note** (decisions D10, D11, D14). Both owner directions are run: Alice's bank is
preprocessed first on the source's batches `[0, nb)`, Bob's second on `[nb, 2nb)` (the caller's own
batches are shifted after them). The caller's ideal calls and waits are replaced by Steps 2–5
(`Code.plug`): an owner's `commit`/`check` command runs Steps 2/4, the other party's wait runs
Steps 3/5 on the next message. Receipts and certificates returned to the caller have the format of
the ideal functionality. The schedule is checked by both parties on the command mtdata (record
contents replaced by zeros). Proofs use the proof system `ZK` for the relation (16) (statement
`pack [1^λ, q, τ, records, P, y]`, witness `pack [u, w]`), whose witness bound is `q + wbound`.
-/

open Code

/-- A record of a bank: identifier, interval start, length, ciphertext. -/
abbrev BankRec := ℕ × ℕ × ℕ × Bits

/-- Encoding of a list of bank records for the statement (16). -/
def encRecs (rs : List BankRec) : Bits :=
  pack (rs.map fun r => pack [encNat r.1, encNat r.2.1, encNat r.2.2.1, r.2.2.2])

/-- XOR of two strings (to the length of the first). -/
def xorBits (a b : Bits) : Bits := (List.range a.length).map fun i => a.getD i false ^^ b.getD i false

/-- The NP relation (16) of the source `S`, predicate language `L` and capacity `q`. -/
def rel16 (S : StrCom) (L : ℕ → PredLang) (q : ℕ → ℕ) (x wit : Bits) : Bool := by
  classical
  exact match unpack x, unpack wit with
  | [l, qb, τ, recs, pe, y], [u, w] =>
    let lam := l.length
    let rs := (unpack recs).map fun r => match unpack r with
      | [i, st, ln, c] => (bitsNat i, bitsNat st, bitsNat ln, c)
      | _ => (0, 0, 0, [])
    decide (bitsNat qb = q lam ∧ u.length = q lam) && S.OpenVer lam τ u w &&
      match (L lam).dec pe with
      | some P => (L lam).eval P ((rs.map fun r => xorBits r.2.2.2 ((u.drop r.2.1).take r.2.2.1)).flatten) y
      | none => false
  | _, _ => false

/-- The witness bound of (16). -/
def pw16 (S : StrCom) (q : ℕ → ℕ) : ℕ → ℕ :=
  fun n => ((Finset.range (n + 1)).sup fun l => q l + S.wbound l) + 4 * n + 8

/-- The state of one party's Protocol 5 machinery: own bank `(µ, τ, w)`, the other bank's `τ`,
the records of both owners, and the accepted command history (for the schedule). -/
structure P5St where
  mu : Bits
  tauOwn : Bits
  wOwn : Bits
  tauOther : Bits
  own : List BankRec
  other : List BankRec
  hist : List (Bool × Bits)

/-- Metadata of a command (contents replaced by zeros) for the schedule. -/
def cmdMt (cmd : Bits) : Bits :=
  match unpack cmd with
  | [t, i, l, M] => if bitsNat t = 0 then pack [t, i, l, List.replicate M.length false] else cmd
  | _ => cmd

/-- Steps 2 and 4 for party `p` (owner) on a caller command. -/
noncomputable def p5OnCall (S : StrCom) (ZK : (Bits → Bits → Bool) → (ℕ → ℕ) → Protocol)
    (L : ℕ → PredLang) (Sched : List (Bool × Bits) → Bool × Bits → Bool) (q : ℕ → ℕ)
    (lam : ℕ) (p : Bool) (st : P5St) (cmd : Bits) : Prog (P5St × Option Bits) := do
  Prog.check (Sched st.hist (p, cmdMt cmd))
  match unpack cmd with
  | [t, i, l, M] =>
    if bitsNat t = 0 then do
      -- Step 2
      let start := (st.own.map fun r => r.2.2.1).sum
      Prog.check (decide (M.length = bitsNat l ∧ (st.own.all fun r => r.1 ≠ bitsNat i) ∧
        start + M.length ≤ q lam))
      let c := xorBits M ((st.mu.drop start).take M.length)
      Prog.send (pack [encNat 0, i, encNat start, c])
      let receipt ← Prog.recv
      Prog.check (receipt = pack [encNat 0, i, [p], l])
      pure ({ st with own := st.own ++ [(bitsNat i, start, M.length, c)], hist := st.hist ++ [(p, cmdMt cmd)] }, some receipt)
    else if bitsNat t = 1 then do
      -- Step 4
      let ids := (unpack i).map bitsNat
      let recs := ids.filterMap fun a => st.own.find? fun r => r.1 = a
      Prog.check (decide (ids ≠ [] ∧ ids.Nodup ∧ recs.length = ids.length))
      let P ← match (L lam).dec l with | some P => pure P | none => failure
      let contents := (recs.map fun r => xorBits r.2.2.2 ((st.mu.drop r.2.1).take r.2.2.1)).flatten
      Prog.check ((L lam).eval P contents M)
      let request := pack [encNat 1, i, l, M]
      Prog.send request
      let x := pack [List.replicate lam true, encNat (q lam), st.tauOwn, encRecs recs, l, M]
      let pf := ZK (rel16 S L q) (pw16 S q)
      let _ ← (OptionT.mk ((if p then pf.codeA else pf.codeB) lam (pack [x, pack [st.mu, st.wOwn]])) : Prog Bits)
      pure ({ st with hist := st.hist ++ [(p, cmd)] }, some (pack [request, [true]]))
    else failure
  | _ => failure

/-- Steps 3 and 5 for party `p` (verifier) when its caller waits for a delivery. -/
noncomputable def p5OnWait (S : StrCom) (ZK : (Bits → Bits → Bool) → (ℕ → ℕ) → Protocol)
    (L : ℕ → PredLang) (Sched : List (Bool × Bits) → Bool × Bits → Bool) (q : ℕ → ℕ)
    (lam : ℕ) (p : Bool) (st : P5St) : Prog (P5St × Option Bits) := do
  let msg ← Prog.recv
  match unpack msg with
  | [t, i, a, c] =>
    if bitsNat t = 0 then do
      -- Step 3
      let start := (st.other.map fun r => r.2.2.1).sum
      let mt := pack [encNat 0, i, encNat c.length, List.replicate c.length false]
      Prog.check (decide (bitsNat a = start ∧ start + c.length ≤ q lam ∧
        (st.other.all fun r => r.1 ≠ bitsNat i)) && Sched st.hist (!p, mt))
      let receipt := pack [encNat 0, i, [!p], encNat c.length]
      Prog.send receipt
      pure ({ st with other := st.other ++ [(bitsNat i, start, c.length, c)], hist := st.hist ++ [(!p, mt)] }, some receipt)
    else if bitsNat t = 1 then do
      -- Step 5
      let ids := (unpack i).map bitsNat
      let recs := ids.filterMap fun b => st.other.find? fun r => r.1 = b
      Prog.check (decide (ids ≠ [] ∧ ids.Nodup ∧ recs.length = ids.length ∧ (L lam).dec a ≠ none) &&
        Sched st.hist (!p, msg))
      let x := pack [List.replicate lam true, encNat (q lam), st.tauOther, encRecs recs, a, c]
      let pf := ZK (rel16 S L q) (pw16 S q)
      let res ← (OptionT.mk ((if p then pf.codeA else pf.codeB) lam x) : Prog Bits)
      Prog.check (res = [true])
      pure ({ st with hist := st.hist ++ [(!p, msg)] }, some (pack [msg, [true]]))
    else failure
  | _ => failure

/-- Step 1 for both owners: Alice's bank on the source batches `[0, nb)`, then Bob's on
`[nb, 2nb)`; returns party `p`'s initial state. -/
noncomputable def p5Pre (S : StrCom) (q : ℕ → ℕ) (lam : ℕ) (p : Bool) : Prog P5St := do
  let nb := S.nb lam
  let mine ← Prog.bits (q lam)
  let commitMine : Prog (Bits × Bits) := do
    let z ← (OptionT.mk (Code.mapDev (fun j => (if p then 0 else nb) + j) (S.commit lam mine)) : Prog Bits)
    match unpack z with | [τ, w] => pure (τ, w) | _ => failure
  let receiveOther : Prog Bits :=
    (OptionT.mk (Code.mapDev (fun j => (if p then nb else 0) + j) (S.receive lam)) : Prog Bits)
  if p then do
    let (τ, w) ← commitMine
    let τo ← receiveOther
    pure ⟨mine, τ, w, τo, [], [], []⟩
  else do
    let τo ← receiveOther
    let (τ, w) ← commitMine
    pure ⟨mine, τ, w, τo, [], [], []⟩

/-- **Protocol 5** substituted into a caller: preprocessing of both banks, then the caller's
commit-and-prove operations by Steps 2–5. The caller's batches are shifted after the `2 nb` source
batches. -/
noncomputable def protocol5 (S : StrCom) (ZK : (Bits → Bits → Bool) → (ℕ → ℕ) → Protocol)
    (L : ℕ → PredLang) (Sched : List (Bool × Bits) → Bool × Bits → Bool) (q : ℕ → ℕ)
    (caller : Protocol) (grp : ℕ → ℕ → ℕ) (ng : ℕ → ℕ) : Protocol where
  codeA := fun lam x => (do
    let st ← p5Pre S q lam true
    let r ← (OptionT.mk (Code.plug
      (fun s c => (p5OnCall S ZK L Sched q lam true s c).run)
      (fun s => (p5OnWait S ZK L Sched q lam true s).run) st
      (Code.mapDev (fun j => 2 * S.nb lam + j) (caller.codeA lam x))) : Prog (Option Bits))
    match r with | some o => pure o | none => failure).run
  codeB := fun lam x => (do
    let st ← p5Pre S q lam false
    let r ← (OptionT.mk (Code.plug
      (fun s c => (p5OnCall S ZK L Sched q lam false s c).run)
      (fun s => (p5OnWait S ZK L Sched q lam false s).run) st
      (Code.mapDev (fun j => 2 * S.nb lam + j) (caller.codeB lam x))) : Prog (Option Bits))
    match r with | some o => pure o | none => failure).run
  nb := fun lam => 2 * S.nb lam + caller.nb lam
  ng := ng
  group := grp
  coords := fun lam b => if b < S.nb lam then S.coords lam b
    else if b < 2 * S.nb lam then S.coords lam (b - S.nb lam)
    else caller.coords lam (b - 2 * S.nb lam)
  rowsA := fun lam b => if b < S.nb lam then S.committerRows lam b
    else if b < 2 * S.nb lam then !S.committerRows lam (b - S.nb lam)
    else caller.rowsA lam (b - 2 * S.nb lam)
  steps := fun lam => S.steps lam * 2 + caller.steps lam * (S.steps lam + 1) * 4 + 2 ^ lam

/-- The caller with its batches shifted after the `2 nb` source batches (the ideal side of
Theorem 10). -/
def shiftCaller (S : StrCom) (caller : Protocol) (grp : ℕ → ℕ → ℕ) (ng : ℕ → ℕ) : Protocol :=
  { caller with
    codeA := fun lam x => Code.mapDev (fun j => 2 * S.nb lam + j) (caller.codeA lam x)
    codeB := fun lam x => Code.mapDev (fun j => 2 * S.nb lam + j) (caller.codeB lam x)
    nb := fun lam => 2 * S.nb lam + caller.nb lam
    ng := ng
    group := grp }

end DIObliviousTransfer


