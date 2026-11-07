-- Prove2me | Definitions.Def_BeyondDS_Envelope
-- name    : BeyondDS_Envelope
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:07:56.990206+00:00
-- url     : https://prove2.me/theorems/4a9e2121-5f47-4065-8486-c73a4276a9cf
-- title:
--   Evidence records, payloads, acknowledgements, envelopes and signed data
-- statement:
--   1. A **proposal header** $q=(r,i,b,k)$: iteration, candidate, bit, support rank $k\in\mathbb Z$.
--   2. **Evidence records**, each with one signature: the designated sender's signature on its bit (rank 0); a candidate's signature on its header; an endorsement by $j$ on $(\mathrm{Endorse},q)$; a vote by $j$ on $(\mathrm{Vote},r,b)$ with a reference to its prepared proposal (a header), not covered by the signature; a commit by $j$ on $(\mathrm{Commit},r,b)$; a terminal acknowledgement by $j$ on $(\mathrm{TAck},b)$. A rank $-1$ fallback has no record.
--   3. A **payload** $P_i=\langle(\mathrm{Payload},sid,i,x_i)\rangle_i$ and an **acknowledgement** $\langle(\mathrm{Ack},sid,P)\rangle_j$, which contains the full payload, "so equality of acknowledged payloads is byte equality and requires no hash assumption".
--   4. An **envelope** names its instance and sending round and batches payloads, acknowledgements and termination evidence.
--   5. The **signed data** and their injective codes: every signed item names its invocation, stage and signer, and distinct tags separate its types.
--
--   **Formalization Note** The flat list of records is the paper's directed acyclic graph whose "references name those vertices by their semantic fields" (p.15): a certificate is the set of votes it refers to, and a proposal's support is named by $(b,k)$ of its header. Natural numbers inside signed data are binary.
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), §5.2, pp.14–15 (PDF pp.15–16); §7.1, p.22 (PDF p.23); §7.4, p.26 (PDF p.27); §8.1, p.29 (PDF p.30)

import Mathlib
import Definitions.Def_BeyondDS_tup

set_option autoImplicit false

open QAlgorithms.Complexity

namespace BeyondDS

/-- A proposal header `q = (r, i, b, k)` (§5.2, p.14): iteration, candidate, bit and support rank. -/
structure Header where
  r : ℕ
  cand : ℕ
  b : Bool
  k : ℤ
  deriving DecidableEq

/-- An elementary evidence record of the compiler (§5.2, pp.14–15; §8.1, p.29), each holding one signature and
explicit semantic fields. A rank-`−1` fallback has no record.

* `senderSig b s`: the rank-0 certificate, the designated sender's signature on its bit.
* `headerSig q s`: the candidate's signature on its header.
* `endorse q j s`: the signature of `j` on `(Endorse, q)`.
* `vote r b j s q`: the signature of `j` on `(Vote, r, b)`, with `q` the reference to the attached prepared
  proposal, which the signature does not cover.
* `commit r b j s`: the signature of `j` on `(Commit, r, b)`.
* `tack b j s`: the terminal acknowledgement of `j`, on `(TAck, b)`.

**Formalization Note.** This flat form is the paper's "directed acyclic graph" with "references [that] name those
vertices by their semantic fields" (p.15). Certificates are not records: an iteration-`r` certificate for `b` is
the votes it refers to, and a proposal's support is named by the fields `(q.b, q.k)` of its header. -/
inductive EvRec where
  | senderSig (b : Bool) (s : Str)
  | headerSig (q : Header) (s : Str)
  | endorse (q : Header) (j : ℕ) (s : Str)
  | vote (r : ℕ) (b : Bool) (j : ℕ) (s : Str) (q : Header)
  | commit (r : ℕ) (b : Bool) (j : ℕ) (s : Str)
  | tack (b : Bool) (j : ℕ) (s : Str)
  deriving DecidableEq

/-- A signed payload of source `src` in dissemination instance `sid` (§7.1, p.22): `Pi = ⟨(Payload, sid, i, xi)⟩i`.
The body is a bit string in the stand-alone dissemination and a batch of evidence records in the compiler. -/
structure Payload (B : Type) where
  sid : ℕ
  src : ℕ
  body : B
  sig : Str
  deriving DecidableEq

/-- An acknowledgement by `issuer` for a payload (§7.1, p.22): `⟨(Ack, sid, P)⟩j`. "It contains the full payload, so
equality of acknowledged payloads is byte equality and requires no hash assumption." -/
structure Ack (B : Type) where
  issuer : ℕ
  payload : Payload B
  sig : Str
  deriving DecidableEq

/-- A network message (§7.4, p.26: "Every network message identifies this instance and its sending round"). It may
batch arbitrarily many records. `term` carries termination evidence and terminal acknowledgements (§8.1, p.29). -/
structure Envelope (B : Type) where
  sid : ℕ
  round : ℕ
  pay : List (Payload B)
  ack : List (Ack B)
  term : List EvRec

/-- A code of a natural number, in binary. -/
def encN (k : ℕ) : Str := k.bits

/-- A code of an integer. -/
def encZ (k : ℤ) : Str := tup [[decide (k < 0)], encN k.natAbs]

/-- A code of a header. -/
def encHeader (q : Header) : Str :=
  tup [encN q.r, encN q.cand, [q.b], encZ q.k]

/-- The data signed by each record: every signed item names its invocation, its stage and its signer (§5.1,
p.14), and distinct tags separate its types (§7.1, p.22). -/
inductive Datum (B : Type) where
  | payload (sid src : ℕ) (body : B)
  | ack (sid j : ℕ) (P : Payload B)
  | senderBit (src : ℕ) (b : Bool)
  | header (q : Header)
  | endorse (j : ℕ) (q : Header)
  | vote (j r : ℕ) (b : Bool)
  | commit (j r : ℕ) (b : Bool)
  | tack (j : ℕ) (b : Bool)

/-- The injective code of signed data, given an injective code of bodies. -/
def encDatum {B : Type} (enc : B → Str) : Datum B → Str
  | Datum.payload sid src body => tup [[false, false, false], encN sid, encN src, enc body]
  | Datum.ack sid j P =>
    tup [[false, false, true], encN sid, encN j, encN P.sid, encN P.src, enc P.body, P.sig]
  | Datum.senderBit src b => tup [[false, true, false], encN src, [b]]
  | Datum.header q => tup [[false, true, true], encHeader q]
  | Datum.endorse j q => tup [[true, false, false], encN j, encHeader q]
  | Datum.vote j r b => tup [[true, false, true], encN j, encN r, [b]]
  | Datum.commit j r b => tup [[true, true, false], encN j, encN r, [b]]
  | Datum.tack j b => tup [[true, true, true], encN j, [b]]

/-- The header, the signature and the reference of a record: the three fields bounded by `L` on p.15. A reference is a
header. -/
def EvRec.fields : EvRec → List Str
  | EvRec.senderSig b s => [[b], s, []]
  | EvRec.headerSig q s => [encHeader q, s, []]
  | EvRec.endorse q j s => [tup [encHeader q, encN j], s, []]
  | EvRec.vote r b j s q => [tup [encN r, [b], encN j], s, encHeader q]
  | EvRec.commit r b j s => [tup [encN r, [b], encN j], s, []]
  | EvRec.tack b j s => [tup [[b], encN j], s, []]

/-- The tag of a record's type. -/
def EvRec.tag : EvRec → Str
  | EvRec.senderSig .. => [false, false, false]
  | EvRec.headerSig .. => [false, false, true]
  | EvRec.endorse .. => [false, true, false]
  | EvRec.vote .. => [false, true, true]
  | EvRec.commit .. => [true, false, false]
  | EvRec.tack .. => [true, false, true]

/-- The code of a record. -/
def encEvRec (e : EvRec) : Str := tup (e.tag :: e.fields)

/-- The code of a batch of records: the body of a compiler payload. -/
def encRecs (es : List EvRec) : Str := tup (es.map encEvRec)

end BeyondDS


