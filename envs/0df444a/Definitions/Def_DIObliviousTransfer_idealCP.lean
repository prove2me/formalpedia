-- Prove2me | Definitions.Def_DIObliviousTransfer_idealCP
-- name    : DIObliviousTransfer_idealCP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T09:05:21.24749+00:00
-- url     : https://prove2.me/theorems/b14e2feb-54b9-4b9d-858b-fee89f541b43
-- title:
--   Ideal commit-and-prove (Definition 8)
-- statement:
--   The functionality keeps immutable records, each with an identifier, an owner (the issuing party), a public length and contents.
--
--   1. A `commit` command checks the length and the schedule and issues a metadata-only receipt.
--   2. A `check` command names an ordered nonempty tuple of distinct same-owner records, a predicate $P$ and a public value $y$. It publishes the request and certifies success if $P(M_{a_1}\|\cdots\|M_{a_r},y)=1$; otherwise it aborts the session.
--   3. Projections are checks with $P_S(M;z)=[\pi_S(M)=z]$.
--   4. Wrong-role, duplicate, unknown, repeated, malformed and out-of-schedule commands abort the session.
--   5. The adversary schedules all deliveries and may abort at any time; on abort every honest party receives $\perp$.
--
--   **Formalization Note** This is decision D10. Predicates come from a $\lambda$-indexed predicate language with an encoding and an evaluation map; Boolean circuits are one instance. The authorized predicate schedule is a parameter.
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Definition 8, pp.19–20

import Mathlib
import Definitions.Def_DIObliviousTransfer_Protocol

namespace DIObliviousTransfer

/-!
Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held version, sha256 8334c039…), Definition 8,
pp.19–20: the commit-and-prove functionality.

"(i) Commitment. On the owner's first (commit, M) command, check that M is a bit string of the
prescribed public length; otherwise abort the session without creating a record. On success,
store M and issue a receipt consisting of the identifier, the roles, and the length. (ii) Predicate
certification. Only the common owner may issue (check, a, P, y), where a = (a₁, …, a_r) is an
ordered nonempty tuple of distinct previously committed record identifiers from this session, all
with that owner and the same designated verifier. … Check the tuple, public lengths, and authorized
predicate schedule. … Publish the request identifier, a, P, and y. If P(M_{a₁}‖⋯‖M_{a_r}, y) = 1,
issue a success certificate subject to the delivery rule below; otherwise abort the session.
(iii) Selective opening. Open(M_S) is the request (check, P_S, (S, z)) with
P_S(M; S, z) = [π_S(M) = z] … (iv) Rejections. Wrong-role, cross-session, duplicate-commitment,
unknown or unreceipted handles, repeated handles, wrong-owner or wrong-verifier tuples, malformed,
and out-of-schedule commands cause session abort. … No record is ever updated. (v) Delivery with
abort. The adversary schedules the delivery of receipts, certificates, and ⊥, and receives its own
releases first. It may send ⊥ at any time. On abort, every honest party receives ⊥, and the
session terminates …"

**Formalization Note** (decision D10, a generalization and a reading). One session between Alice
and Bob; the owner is the party issuing a command and the verifier is the other party. Predicates
are drawn from a predicate language `L λ` (a type of descriptions with an encoding and an evaluation
map); Boolean circuits are one such language, and the theorems quantify over every language with
polynomial-time evaluation. The authorized predicate schedule is a parameter `Sched` (a predicate
on the accepted command history and the new command); out-of-schedule commands abort. Commands
are `pack [0, id, length, M]` (commit) and `pack [1, pack ids, P, y]` (check); projections are
checks with a projection predicate of `L`. Releases go to the adversary; the honest deliveries
wait for the adversary's empty message (`[true]` aborts). A command issued while deliveries are
pending is out of schedule. Records are never updated.
-/

/-- A predicate language for commit-and-prove: descriptions, their encoding and evaluation
`P(M, y)`. -/
structure PredLang where
  Pred : Type
  enc : Pred → Bits
  dec : Bits → Option Pred
  eval : Pred → Bits → Bits → Bool

/-- Evaluation of a family of predicate languages (one per `λ`) is uniformly polynomial-time,
on `pack [1^λ, P, M, y]`. -/
def PredLang.PolyTime (L : ℕ → PredLang) : Prop :=
  PolyTimeBits fun x => match unpack x with
    | [l, p, m, y] => match (L l.length).dec p with
      | some P => [(L l.length).eval P m y]
      | none => []
    | _ => []

/-- The state of ideal CP. -/
structure CPSt where
  lam : ℕ
  H : Option Bool
  recs : List (ℕ × Bool × ℕ × Bits)
  hist : List (Bool × Bits)
  pending : List FOut
  aborted : Bool

/-- Session abort: every party receives `⊥`. -/
def CPSt.abort (st : CPSt) (pre : List FOut) : CPSt × List FOut :=
  ({ st with aborted := true, pending := [] }, pre ++ [.party true none, .party false none])

/-- **Definition 8**, the commit-and-prove functionality with predicate language `L` and
authorized schedule `Sched`. -/
def idealCP (L : ℕ → PredLang) (Sched : List (Bool × Bits) → Bool × Bits → Bool) : Func where
  St := CPSt
  init := fun lam H => ⟨lam, H, [], [], [], false⟩
  step := fun st e =>
    if st.aborted then (st, []) else
    match e with
    | .adv x =>
      if x = [true] then st.abort []
      else if x = [] then ({ st with pending := [] }, st.pending)
      else (st, [])
    | .party p x =>
      if st.pending ≠ [] ∨ Sched st.hist (p, x) = false then st.abort [] else
      match unpack x with
      | [t, i, l, m] =>
        if bitsNat t = 1 then
        let ids := i
        let pe := l
        let y := m
        let idl := (unpack ids).map bitsNat
        let found := idl.map fun a => st.recs.find? fun r => r.1 = a
        if idl ≠ [] ∧ idl.Nodup ∧ (found.all fun r => match r with
            | some r => r.2.1 = p | none => false) then
          let request := pack [encNat 1, ids, pe, y]
          let contents := (found.map fun r => match r with | some r => r.2.2.2 | none => []).flatten
          match (L st.lam).dec pe with
          | some P =>
            if (L st.lam).eval P contents y then
              let cert := pack [request, [true]]
              let pend : List FOut := [.party p (some cert), .party (!p) (some cert)]
              ({ st with hist := st.hist ++ [(p, x)], pending := pend }, [.adv request])
            else st.abort [.adv request]
          | none => st.abort [.adv request]
        else st.abort []
        else if bitsNat t = 0 ∧ m.length = bitsNat l ∧ (st.recs.all fun r => r.1 ≠ bitsNat i) then
          let receipt := pack [encNat 0, i, [p], l]
          let pend : List FOut := [.party p (some receipt), .party (!p) (some receipt)]
          ({ st with recs := st.recs ++ [(bitsNat i, p, bitsNat l, m)], hist := st.hist ++ [(p, x)], pending := pend }, [.adv receipt])
        else st.abort []
      | _ => st.abort []
  validA := fun _ => Set.univ
  validB := fun _ => Set.univ

end DIObliviousTransfer


