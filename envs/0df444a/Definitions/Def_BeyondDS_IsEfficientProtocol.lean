-- Prove2me | Definitions.Def_BeyondDS_IsEfficientProtocol
-- name    : BeyondDS_IsEfficientProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:11:20.089708+00:00
-- url     : https://prove2.me/theorems/05ed834c-cd02-4b8a-a800-a9541e6257fb
-- title:
--   Efficient protocols on bit strings
-- statement:
--   A protocol $\Pi$ on bit-string states and messages is **efficient with polynomial $p$** when:
--
--   1. one polynomial-time machine computes $\mathrm{next}$ for all parameters, on the unambiguous code of (parameters in unary, state, model answer), and likewise for the initial state and for the public election schedule;
--   2. the round cap and the per-round operation cap are at most $p(\kappa+t+\lambda)$;
--   3. in every run with a perfectly correct scheme of signature-length bound $\ell$, under any election law and any adversary, every honest local state and every honest message has length at most $p(\kappa+t+\lambda+\ell+b)$, where $b$ is the number of bits the adversary has injected before that point.
--
--   This is §4.2's "The algorithms, population, number of signed data items, and capped execution length are polynomially bounded in the computational security parameter κ", and §7.4's "the record count, total buffer length, and signing and verification work are polynomial in κ".
--
--   **Formalization Note** The size clause bounds what polynomial time per step does not: the growth of a state through repeated forwarding. Under arbitrary batching (p.22) retained records can only be bounded in terms of what was received, which is why the adversary's bits appear on the right.
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), §4.2, p.12 (PDF p.13); §7.4, p.27 (PDF p.28)

import Mathlib
import Definitions.Def_BeyondDS_Fail
import Definitions.Def_BeyondDS_tup

set_option autoImplicit false

open QAlgorithms.Complexity
open Polynomial

namespace BeyondDS

/-- The code of `Params`, in unary, so that a polynomial in the input length is a polynomial in
`κ + t + λ`. -/
def encParams (P : Params) : Str :=
  tup [encNat P.κ, encNat P.t, encNat P.lam, encNat P.sender.val]

/-- The code of an answer of the model, for bit-string messages. -/
def encResp : Resp Str → Str
  | Resp.start => tup [[false, false, false]]
  | Resp.signatures ss => tup [[false, false, true], tup ss]
  | Resp.verdicts vs => tup [[false, true, false], vs]
  | Resp.sampled k => tup [[false, true, true], encNat k]
  | Resp.done => tup [[true, false, false]]
  | Resp.boundary inbox e =>
    tup [[true, false, true], tup (inbox.map fun m => tup [encNat m.1, m.2]),
      match e with
      | none => []
      | some l => encNat l]

/-- The code of an operation, for bit-string messages. -/
def encOp : Op Str → Str
  | Op.signAll ms => tup [[false, false, false], tup ms]
  | Op.verifyAll qs =>
    tup [[false, false, true], tup (qs.map fun q => tup [encNat q.1, q.2.1, q.2.2])]
  | Op.sample N => tup [[false, true, false], encNat N]
  | Op.send j m => tup [[false, true, true], encNat j, m]
  | Op.yield => tup [[true, false, false]]
  | Op.decide b => tup [[true, false, true], [b]]
  | Op.halt => tup [[true, true, false]]

/-- The total bits the adversary has injected in a transcript prefix. -/
def injectedBits {n : ℕ} {St : Type} (h : List (Event n Str St)) : ℕ :=
  (h.map fun e =>
    match e with
    | Event.injected _ _ m => m.length
    | _ => 0).sum

/-- The bits of an honest local state or honest message in a transcript entry; `0` for other entries. -/
def honestBits {n : ℕ} (e : Event n Str Str) : ℕ :=
  match e with
  | Event.state _ s => s.length
  | Event.obs (Obs.sent _ _ m) => m.length
  | _ => 0

/-- The efficiency clause of Theorem 1, from §4.2, p.12 ("The algorithms, population, number of signed
data items, and capped execution length are polynomially bounded in the computational security
parameter κ") and §7.4, p.27 ("the record count, total buffer length, and signing and verification work
are polynomial in κ"). One machine computes `next` for all parameters, and `init` and the election
schedule likewise; the caps are polynomial in `κ + t + λ`.

The last clause bounds what polynomial time per step does not bound, namely the growth of a state
through repeated forwarding: in every run, each honest local state and each honest message has length
polynomial in `κ + t + λ`, the signature length and the bits the adversary has injected so far.

**Formalization Note.** Bit strings are the messages and states of this layer, and `tup` makes all
machine inputs unambiguous. The adversary's bits appear on the right because, under arbitrary batching
(p.22), retained records can only be bounded in terms of what was received. -/
def IsEfficientProtocol (Pi : Protocol Str Str) (p : ℕ[X]) : Prop :=
  (∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ (P : Params) (s : Str) (r : Resp Str),
      f (tup [encParams P, s, encResp r]) =
        tup [encOp (Pi.next P s r).1, (Pi.next P s r).2]) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ (P : Params) (i : Fin P.n) (x : Option Bool),
      f (tup [encParams P, encNat i.val, encOptBool x]) = Pi.init P i x) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ (P : Params) (r : ℕ), f (tup [encParams P, encNat r]) = encBool (Pi.electAt P r)) ∧
  (∀ P : Params, Pi.roundCap P ≤ p.eval (P.κ + P.t + P.lam)) ∧
  (∀ P : Params, Pi.opCap P ≤ p.eval (P.κ + P.t + P.lam)) ∧
  (∀ (S : Sig) (P : Params) (x : Bool) (E : List (Event P.n Str Str) → PMF (Fin P.n))
      (A : Adversary P.n Str Str) (ω : Config P.n Str Str A.σ),
    S.Correct → ω ∈ (exec Pi S P x E A).support →
    ∀ (pre : List (Event P.n Str Str)) (e : Event P.n Str Str) (post : List (Event P.n Str Str)),
      ω.log = pre ++ e :: post →
      honestBits e ≤ p.eval (P.κ + P.t + P.lam + S.sigLen + injectedBits pre))

end BeyondDS


