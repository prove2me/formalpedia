-- Prove2me | Definitions.Def_BeyondDS_certValid
-- name    : BeyondDS_certValid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:09:02.299847+00:00
-- url     : https://prove2.me/theorems/a7397e75-d59d-4009-aa2c-4b8e0d5bcc05
-- title:
--   Recursive verification of certificates, closures and normalization
-- statement:
--   Relative to public data (population, budget $t$, sender, iteration cap $J$, election outputs released so far), on a store of records whose signatures were checked individually:
--
--   1. **Domains.** A header must have $1\le r\le J$, a candidate $<n$, and $-1\le k<r$; records outside the public domains are rejected before traversal.
--   2. **Certificate.** An iteration-$r$ certificate for $b$ verifies when $t+1$ distinct players have votes for $(r,b)$ each attaching a prepared proposal of the elected candidate $L_r$ (rejected if $L_r$ is not yet released) for bit $b$ with support rank below $r$; support of rank $-1$ verifies only for bit $0$, of rank $0$ is a sender signature, and of rank $k>0$ is a certificate of rank $k$, checked recursively (ranks strictly decrease).
--   3. **Prepared proposal.** A domain-valid header with its candidate signature, verifying support, and endorsements by $t+1$ distinct players.
--   4. **Termination certificate.** A certificate of rank $r$ for $b$ together with commits for $(r,b)$ by $t+1$ distinct players.
--   5. **Closures.** The fixed choice of the records reachable from a certificate, a support, a prepared proposal or a termination certificate ("A message includes all vertices reachable from its evidence roots").
--   6. **Normalization.** Keep the domain-valid records and one representative per issuer and signed header, a vote's representative having verifying attached evidence whenever one exists.
--
--   **Formalization Note** Fixed orderings are increasing rank, then bit $0$ before $1$, and increasing issuer; "fixed ordering" in the paper means some fixed choice, and these are the ones made.
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), §5.2, pp.14–15 (PDF pp.15–16); §8.1, p.29 (PDF p.30)

import Mathlib
import Definitions.Def_BeyondDS_Envelope

set_option autoImplicit false

open QAlgorithms.Complexity

namespace BeyondDS

/-- Public data of a compiler instance: population, budget, sender, iteration cap, and the election outputs
`(r, L_r)` released so far. -/
structure EvCtx where
  n : ℕ
  t : ℕ
  sender : ℕ
  J : ℕ
  elect : List (ℕ × ℕ)

/-- The election output of iteration `r`, if released. -/
def EvCtx.L (x : EvCtx) (r : ℕ) : Option ℕ :=
  (x.elect.find? fun e => e.1 = r).map Prod.snd

/-- The public domain checks made "before recursive traversal" (§5.2, p.15): "a player index outside {1, . . . , n},
a bit outside {0, 1}, an iteration outside {1, . . . , J}, or a support rank outside {−1, . . . , r − 1} for an
iteration-r proposal". -/
def Header.inDomain (x : EvCtx) (q : Header) : Bool :=
  decide (1 ≤ q.r ∧ q.r ≤ x.J ∧ q.cand < x.n ∧ -1 ≤ q.k ∧ q.k < q.r)

/-- The domain check of a record. The fallback bit rule of p.14, "The fallback support verifies only for the fixed
bit 0 and rank −1", is in `supportValid`. -/
def EvRec.inDomain (x : EvCtx) : EvRec → Bool
  | EvRec.senderSig _ _ => true
  | EvRec.headerSig q _ => q.inDomain x
  | EvRec.endorse q j _ => q.inDomain x && decide (j < x.n)
  | EvRec.vote r _ j _ q => q.inDomain x && decide (1 ≤ r ∧ r ≤ x.J ∧ j < x.n)
  | EvRec.commit r _ j _ => decide (1 ≤ r ∧ r ≤ x.J ∧ j < x.n)
  | EvRec.tack _ j _ => decide (j < x.n)

/-- The signature query of a record: signer and the data signed. -/
def EvRec.query {B : Type} (enc : B → Str) (x : EvCtx) (e : EvRec) : ℕ × Str × Str :=
  match e with
  | EvRec.senderSig b s => (x.sender, encDatum enc (Datum.senderBit x.sender b), s)
  | EvRec.headerSig q s => (q.cand, encDatum enc (Datum.header q), s)
  | EvRec.endorse q j s => (j, encDatum enc (Datum.endorse j q), s)
  | EvRec.vote r b j s _ => (j, encDatum enc (Datum.vote j r b), s)
  | EvRec.commit r b j s => (j, encDatum enc (Datum.commit j r b), s)
  | EvRec.tack b j s => (j, encDatum enc (Datum.tack j b), s)

/-- The distinct issuers among a list of identities. -/
def distinctCount (l : List ℕ) : ℕ := l.dedup.length

/-- The identities with an endorsement of `q` in the store. -/
def endorsers (S : List EvRec) (q : Header) : List ℕ :=
  S.filterMap fun e =>
    match e with
    | EvRec.endorse q' j _ => if q' = q then some j else none
    | _ => none

/-- Whether the store holds a rank-0 certificate for `b`. -/
def hasSender (S : List EvRec) (b : Bool) : Bool :=
  S.any fun e =>
    match e with
    | EvRec.senderSig b' _ => b' == b
    | _ => false

/-- Whether the store holds the candidate's signature on `q`. -/
def hasHeader (S : List EvRec) (q : Header) : Bool :=
  S.any fun e =>
    match e with
    | EvRec.headerSig q' _ => decide (q' = q)
    | _ => false

/-- Verification of evidence in a store of records whose individual signatures were all checked, by recursion on rank
(§5.2, p.14: "Evidence is checked recursively, and strictly decreasing support ranks rule out circular certificates").
The first component says that an iteration-`r` certificate for `b` verifies: votes by `t + 1` distinct players, each
attaching a verifying prepared proposal of candidate `L_r` for `b` with support rank below `r`. Verification "rejects the
record if that output has not yet been released" (p.15). -/
def certValidAux (x : EvCtx) (S : List EvRec) : ℕ → ℕ → Bool → Bool
  | 0, _, _ => false
  | f + 1, r, b =>
    decide (x.t + 1 ≤ distinctCount (S.filterMap fun e =>
      match e with
      | EvRec.vote r' b' j _ q =>
        if r' = r ∧ b' = b ∧ q.r = r ∧ q.b = b ∧ q.k < r ∧ x.L r = some q.cand ∧ q.inDomain x = true ∧
            hasHeader S q = true ∧ x.t + 1 ≤ distinctCount (endorsers S q) ∧
            (match q.k with
              | Int.ofNat 0 => hasSender S q.b
              | Int.ofNat (k + 1) => certValidAux x S f (k + 1) q.b
              | Int.negSucc 0 => q.b == false
              | Int.negSucc (_ + 1) => false) = true
        then some j else none
      | _ => none))

/-- An iteration-`r` certificate for `b` verifies in the store. -/
def certValid (x : EvCtx) (S : List EvRec) (r : ℕ) (b : Bool) : Bool :=
  certValidAux x S r r b

/-- A state or a proposal's support of bit `b` and rank `k` verifies: "For k = −1, the support is the fallback state; for
k = 0, it is a sender signature; and for k > 0, it is the vote certificate" (p.14). -/
def supportValid (x : EvCtx) (S : List EvRec) (b : Bool) : ℤ → Bool
  | Int.ofNat 0 => hasSender S b
  | Int.ofNat (k + 1) => certValid x S (k + 1) b
  | Int.negSucc 0 => b == false
  | Int.negSucc (_ + 1) => false

/-- A header with a candidate signature and verifying support: "verifying proposal header with its required evidence"
(p.16). -/
def headerValid (x : EvCtx) (S : List EvRec) (q : Header) : Bool :=
  q.inDomain x && hasHeader S q && supportValid x S q.b q.k

/-- A prepared proposal: "q, the candidate's signature, a verifying supporting certificate, and endorsements by t + 1 distinct
players" (p.15). -/
def preparedValid (x : EvCtx) (S : List EvRec) (q : Header) : Bool :=
  headerValid x S q && decide (x.t + 1 ≤ distinctCount (endorsers S q))

/-- A vote of iteration `r` for `b` by `j` with attached proposal `q` is counted: "its signature and attached evidence verify,
including the elected candidate and strictly lower support rank" (p.16). -/
def voteOK (x : EvCtx) (S : List EvRec) (r : ℕ) (b : Bool) (q : Header) : Bool :=
  decide (q.r = r ∧ q.b = b ∧ q.k < r ∧ x.L r = some q.cand) && preparedValid x S q

/-- The identities with a counted iteration-`r` vote for `b`. -/
def voters (x : EvCtx) (S : List EvRec) (r : ℕ) (b : Bool) : List ℕ :=
  (S.filterMap fun e =>
    match e with
    | EvRec.vote r' b' j _ q => if r' = r ∧ b' = b ∧ voteOK x S r b q = true then some j else none
    | _ => none).dedup

/-- The identities with a commit of iteration `r` for `b`. -/
def committers (S : List EvRec) (r : ℕ) (b : Bool) : List ℕ :=
  (S.filterMap fun e =>
    match e with
    | EvRec.commit r' b' j _ => if r' = r ∧ b' = b then some j else none
    | _ => none).dedup

/-- A termination certificate of rank `r` for `b` verifies: "t + 1 such commit signatures for the same rank and bit, with their
verifying evidence" (p.15). -/
def termValid (x : EvCtx) (S : List EvRec) (r : ℕ) (b : Bool) : Bool :=
  certValid x S r b && decide (x.t + 1 ≤ (committers S r b).length)

/-- All iteration and bit pairs, in the fixed order: increasing rank, `false` first. -/
def rankBits (J : ℕ) : List (ℕ × Bool) :=
  (List.range J).flatMap fun r => [(r + 1, false), (r + 1, true)]

/-- The first verifying termination certificate, in the fixed order. -/
def firstTerm (x : EvCtx) (S : List EvRec) : Option (ℕ × Bool) :=
  (rankBits x.J).find? fun e => termValid x S e.1 e.2

/-- The bits with verifying termination evidence (§8.1, p.29: "Each player acknowledges every bit for which it holds verifying
termination evidence"). -/
def termBits (x : EvCtx) (S : List EvRec) : List Bool :=
  [false, true].filter fun b => (rankBits x.J).any fun e => e.2 == b && termValid x S e.1 b

/-- The first record of a list satisfying a test: the fixed choice of representative (p.15: "a player retains one verifying
signature"). -/
def firstRec (S : List EvRec) (f : EvRec → Bool) : List EvRec :=
  (S.find? f).toList

/-- The fixed choice of `t + 1` endorsement records for `q`, in increasing issuer order. -/
def endorseClosure (x : EvCtx) (S : List EvRec) (q : Header) : List EvRec :=
  (((List.range x.n).filter fun j => j ∈ endorsers S q).take (x.t + 1)).flatMap fun j =>
    firstRec S fun e =>
      match e with
      | EvRec.endorse q' j' _ => decide (q' = q ∧ j' = j)
      | _ => false

/-- The evidence closure of an iteration-`r` certificate for `b` and of its proposals' supports: "A message includes all vertices
reachable from its evidence roots" (p.15). -/
def certClosureAux (x : EvCtx) (S : List EvRec) : ℕ → ℕ → Bool → List EvRec
  | 0, _, _ => []
  | f + 1, r, b =>
    (((List.range x.n).filter fun j => j ∈ voters x S r b).take (x.t + 1)).flatMap fun j =>
      let v := firstRec S fun e =>
        match e with
        | EvRec.vote r' b' j' _ q => decide (r' = r ∧ b' = b ∧ j' = j) && voteOK x S r b q
        | _ => false
      v ++ v.flatMap fun e =>
        match e with
        | EvRec.vote _ _ _ _ q =>
          (firstRec S fun e' =>
            match e' with
            | EvRec.headerSig q' _ => decide (q' = q)
            | _ => false) ++ endorseClosure x S q ++
          (match q.k with
            | Int.ofNat 0 =>
              firstRec S fun e' =>
                match e' with
                | EvRec.senderSig b' _ => b' == q.b
                | _ => false
            | Int.ofNat (k + 1) => certClosureAux x S f (k + 1) q.b
            | Int.negSucc _ => [])
        | _ => []

/-- The closure of a certificate, without repeats. -/
def certClosure (x : EvCtx) (S : List EvRec) (r : ℕ) (b : Bool) : List EvRec :=
  (certClosureAux x S r r b).dedup

/-- The closure of a state or support of bit `b` and rank `k`. -/
def supportClosure (x : EvCtx) (S : List EvRec) (b : Bool) : ℤ → List EvRec
  | Int.ofNat 0 =>
    firstRec S fun e' =>
      match e' with
      | EvRec.senderSig b' _ => b' == b
      | _ => false
  | Int.ofNat (k + 1) => certClosure x S (k + 1) b
  | Int.negSucc _ => []

/-- The closure of a header with its support. -/
def headerClosure (x : EvCtx) (S : List EvRec) (q : Header) : List EvRec :=
  (firstRec S (fun e' =>
    match e' with
    | EvRec.headerSig q' _ => decide (q' = q)
    | _ => false) ++ supportClosure x S q.b q.k).dedup

/-- The closure of a prepared proposal. -/
def preparedClosure (x : EvCtx) (S : List EvRec) (q : Header) : List EvRec :=
  (headerClosure x S q ++ endorseClosure x S q).dedup

/-- The closure of a termination certificate of rank `r` for `b`. -/
def termClosure (x : EvCtx) (S : List EvRec) (r : ℕ) (b : Bool) : List EvRec :=
  ((((List.range x.n).filter fun j => j ∈ committers S r b).take (x.t + 1)).flatMap (fun j =>
    firstRec S fun e =>
      match e with
      | EvRec.commit r' b' j' _ => decide (r' = r ∧ b' = b ∧ j' = j)
      | _ => false) ++ certClosure x S r b).dedup

/-- The terminal acknowledgement records of the store. -/
def tacks (S : List EvRec) : List EvRec :=
  S.filter fun e =>
    match e with
    | EvRec.tack .. => true
    | _ => false

/-- Termination evidence to forward: "verifying termination certificates, and terminal acknowledgements" (§8.1, p.29), one
certificate for each verifying rank and bit. -/
def termEvidence (x : EvCtx) (S : List EvRec) : List EvRec :=
  ((rankBits x.J).flatMap (fun e =>
    if termValid x S e.1 e.2 then termClosure x S e.1 e.2 else []) ++ tacks S).dedup

/-- The semantic key of a record: "For each issuer and signed header, a player retains one verifying signature" (p.15); a
vote's attached proposal is not part of the header it signs. -/
def EvRec.key : EvRec → EvRec
  | EvRec.senderSig b _ => EvRec.senderSig b []
  | EvRec.headerSig q _ => EvRec.headerSig q []
  | EvRec.endorse q j _ => EvRec.endorse q j []
  | EvRec.vote r b j _ _ => EvRec.vote r b j [] ⟨0, 0, false, 0⟩
  | EvRec.commit r b j _ => EvRec.commit r b j []
  | EvRec.tack b j _ => EvRec.tack b j []

/-- Normalization of a store (§5.2, p.15; Lemma 5.1, p.16): only records inside the public domains, and only one representative
per semantic key, a vote's representative being one with verifying attached evidence whenever one exists. -/
def normalize (x : EvCtx) (S : List EvRec) : List EvRec :=
  let D := S.filter (EvRec.inDomain x)
  let good : EvRec → Bool := fun e =>
    match e with
    | EvRec.vote r b _ _ q => voteOK x D r b q
    | _ => true
  (D.map EvRec.key).dedup.flatMap fun k =>
    ((D.find? fun e => decide (e.key = k) && good e).orElse fun _ =>
      D.find? fun e => decide (e.key = k)).toList

end BeyondDS


