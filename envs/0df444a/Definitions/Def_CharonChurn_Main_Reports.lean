-- Prove2me | Definitions.Def_CharonChurn_Main_Reports
-- name    : CharonChurn_Main_Reports
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:54:31.981205+00:00
-- url     : https://prove2.me/theorems/f95ac404-85fc-4940-aeed-b4e9d7b46f14
-- title:
--   Signed neighbourhood reports, the authentication interface and the validated evidence cache
-- statement:
--   A report payload has the fields of Eq. (1): message type, protocol version, session, original round, signer and an asserted list of neighbour identifiers; a record is a payload with signature bytes. Any field values may occur. A payload is *well-formed* if it has type NBR, the protocol version, and exactly $D$ distinct neighbour identifiers none of which is the signer. Payloads and records are ordered by a fixed injective canonical key compared lexicographically.
--
--   The authentication interface supplies signing and verification for each identity (fixed identity-to-key binding). At round $r$ of session $\mathrm{sid}$ a record is *acceptable* if its signature verifies under its claimed signer, its session is $\mathrm{sid}$, its original round $q$ satisfies $q\le r<q+F_{\mathrm{ret}}$ (retained through the beginning of round $q+F_{\mathrm{ret}}-1$, discarded at $q+F_{\mathrm{ret}}$), and the length of the entire self-delimiting binary record, including signature bits, is at most the prescribed public bound for its signed session and original round. Normalization keeps only acceptable records, one record per distinct payload (least key, so duplicate copies and alternative signature encodings count once), and per signer and round the two least distinct well-formed payloads and the least signature-verified malformed payload.
--
--   The binary payload and record encodings include every field. The prescribed maximum is a context-indexed parameter; ReportsFit in the execution assumptions requires correct generated envelopes to fit. This represents the whole-envelope limit of pp. 13 and 18, without a fixed bound on future identities.
-- source:
--   Sengupta and Perrin (2026), Byzantine Partition Detection Under Churn, supplied 48-page artifact (venue metadata: STOC 2027 submission; citation basis published per source.meta.json; SHA-256 3f9994406f38c73927d0b5cc78d0dd05740de0f7d09e544b7b203eefe39cdb74), §§2.4–2.5, pp. 9–10; §3.1, pp. 12–13; §3.2, p. 13, Eq. (1)

import Mathlib

namespace CharonChurn.Main

/-! # Signed neighbourhood reports, authentication interface and the evidence cache
(Sengupta–Perrin 2026, §§2.4–2.5, pp. 9–10; §§3.1–3.2, pp. 12–13, Eq. (1)) -/

/-- The fields of a report payload: message type, protocol version, session identifier, original
round, signer identity and the asserted neighbour list. Any field values may occur (Byzantine
signers may sign anything); well-formedness is a separate check. -/
structure Payload where
  tag : ℕ
  ver : ℕ
  sid : ℕ
  round : ℕ
  signer : ℕ
  nbrs : List ℕ
  deriving DecidableEq

/-- A signed record: a payload with signature bytes. -/
structure Record where
  payload : Payload
  sig : List Bool
  deriving DecidableEq

/-- Self-delimiting binary code of a natural number: each binary digit `b` (least significant
first) is written as `true, b`, and `false` terminates. Length `2·⌊log₂ k + 1⌋ + 1`. -/
def encNat (k : ℕ) : List Bool :=
  (Nat.bits k).flatMap (fun b => [true, b]) ++ [false]

/-- Length-prefixed code of a list. -/
def encList {β : Type*} (f : β → List Bool) (l : List β) : List Bool :=
  encNat l.length ++ l.flatMap f

/-- Code of a payload (all fields, including the full neighbour list). -/
def encPayload (p : Payload) : List Bool :=
  encNat p.tag ++ encNat p.ver ++ encNat p.sid ++ encNat p.round ++ encNat p.signer ++
    encList encNat p.nbrs

/-- Code of a signed record (payload, then the signature bytes). -/
def encRecord (x : Record) : List Bool :=
  encPayload x.payload ++ encList (fun b => [b]) x.sig

/-- The message-type tag `NBR`. -/
def NBR : ℕ := 0

/-- The protocol-version tag `ver`. -/
def VER : ℕ := 0

/-- Mandatory format of a report: type `NBR`, version `ver`, and exactly `D` distinct neighbour
identifiers, none equal to the signer. (Session and round are checked as context.) -/
def WellFormed (D : ℕ) (p : Payload) : Prop :=
  p.tag = NBR ∧ p.ver = VER ∧ p.nbrs.length = D ∧ p.nbrs.Nodup ∧ p.signer ∉ p.nbrs

/-- Canonical (injective) key of a payload, compared lexicographically; it fixes the canonical
order used to choose retained payloads. -/
def Payload.key (p : Payload) : List ℕ :=
  [p.tag, p.ver, p.sid, p.round, p.signer, p.nbrs.length] ++ p.nbrs

/-- Canonical key of a record (payload key, then signature bytes). -/
def Record.key (x : Record) : List ℕ :=
  x.payload.key ++ [x.sig.length] ++ x.sig.map (fun b => if b then 1 else 0)

/-- Authentication interface of the execution model: `sign u p` is the signature of identity `u`
(with its fixed, uncompromised key) on payload `p`, and `verify u p σ` checks `σ` against the
authenticated public key of `u`. Signatures bind every field of the payload. -/
structure Crypto where
  sign : ℕ → Payload → List Bool
  verify : ℕ → Payload → List Bool → Bool
  /-- Prescribed maximum encoded envelope length for a session and original round.
  The bound is fixed for that context, includes all fields and signature bits, and accommodates
  correct reports (`Execution.ReportsFit`). It need not bound identities in future rounds. -/
  maxReportBits : ℕ → ℕ → ℕ

/-- Validation of a record at round `r` of session `sidNow`: the signature verifies under the
claimed signer's key, the signed session is the active one, the original round is not in the
future, the record is not expired (a round-`q` record is retained through the beginning of
round `q + Fret − 1` and discarded at `q + Fret`), and the entire encoded envelope fits the prescribed length limit for its signed context. -/
def Acceptable (Cr : Crypto) (sidNow r Fret : ℕ) (x : Record) : Prop :=
  Cr.verify x.payload.signer x.payload x.sig = true ∧ x.payload.sid = sidNow ∧
    x.payload.round ≤ r ∧ r < x.payload.round + Fret ∧ (encRecord x).length ≤ Cr.maxReportBits x.payload.sid x.payload.round

/-- Same signer and same original round. -/
def SameSlot (x y : Record) : Prop :=
  x.payload.signer = y.payload.signer ∧ x.payload.round = y.payload.round

/-- Validate and normalize a pool of records (old cache, deliveries, own report) at round `r`:
keep only acceptable records; per payload keep one record (least key), so duplicate copies and
alternative signature encodings of one payload count once; per signer and round keep the two
least distinct well-formed payloads and the least signature-verified malformed payload. -/
noncomputable def normalize (Cr : Crypto) (D sidNow r Fret : ℕ) (pool : Finset Record) :
    Finset Record := by
  classical
  let valid := pool.filter (Acceptable Cr sidNow r Fret)
  exact valid.filter (fun x =>
    (∀ y ∈ valid, y.payload = x.payload → x.key ≤ y.key) ∧
    (WellFormed D x.payload →
      ((valid.filter (fun y => SameSlot y x ∧ WellFormed D y.payload ∧
          y.payload.key < x.payload.key)).image (fun y => y.payload)).card < 2) ∧
    (¬ WellFormed D x.payload →
      ∀ y ∈ valid, SameSlot y x → ¬ WellFormed D y.payload → x.payload.key ≤ y.payload.key))

end CharonChurn.Main


