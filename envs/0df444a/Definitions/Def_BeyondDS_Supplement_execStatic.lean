-- Prove2me | Definitions.Def_BeyondDS_Supplement_execStatic
-- name    : BeyondDS_Supplement_execStatic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T05:07:57.796997+00:00
-- url     : https://prove2.me/theorems/4b2e68e8-86a9-4ea1-a5b2-a53514ac07b1
-- title:
--   Executions with fresh public collector samples and a corrupt set fixed before the first sample
-- statement:
--   This is the model of the static-corruption result (Theorem 2): the execution model of the base mission, with a public source of collector samples.
--
--   A protocol comes with a public **sample schedule** $\mathrm{sched}(P,r)\in\mathbb N$, the number of collector samples revealed at the delivery boundary of round $r$ under parameters $P$. At that boundary, after the common election output if one is scheduled, $\mathrm{sched}(P,r)$ identities $a_1,\dots,a_k$ are drawn uniformly from the $n$ identities, independently of each other and of everything that happened before. The adversary observes them, and every active uncorrupted player receives them with that boundary's deliveries.
--
--   The adversary is the adversary of the base mission, with one restriction: **once a boundary has revealed collector samples, the corrupt set is frozen**. Until the first reveal it may corrupt up to $t$ players adaptively; afterwards every further corruption is ignored. Corrupted players are Byzantine. Everything else is as in the base model: honest key generation, atomic activations, a rushing adversary that sees every transmission and schedules the honest players, rounds through the public cap and a final local computation.
--
--   The samples are an ideal public resource: they are not honest transmissions, so they do not count as messages, and they take no extra round.
--
--   The definition also states when a protocol with a sample schedule is **efficient**: one polynomial-time machine computes its transition function for all parameters, and its initial states, election schedule and sample schedule likewise; the round cap, the operation cap and the number of samples per boundary are polynomial in $\kappa+t+\lambda$; and in every run each honest state and message has length polynomial in $\kappa+t+\lambda$, the signature length and the bits the adversary has injected so far.
--
--   **Formalization Note** The samples arrive at the front of the inbox as messages from the pseudo-identity $n$, which no player has. With no samples scheduled the boundary is that of the base model.
-- source:
--   Rambaud, Beyond Dolev–Strong: Adaptive Byzantine Broadcast with Õ(n^{3/2}) Messages at a Tight Honest Majority, STOC 2027 submission (manuscript sha256 c84cf9c9…), §6.1, pp.19–20 (PDF pp.20–21); §4.3, p.13 (PDF p.14); Theorem 2, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_BeyondDS_EUFCMA

set_option autoImplicit false

open QAlgorithms.Complexity
open Polynomial

namespace BeyondDS.Supplement

open BeyondDS

variable {St σ : Type}

/-- The delivery boundary of the static-corruption model of Rambaud, *Beyond Dolev–Strong*, STOC 2027
submission (manuscript sha256 c84cf9c9…), §6.1, p.19 (PDF 20): the boundary of the base model
(`BeyondDS.boundary`) together with a fresh batch of `k` public collector samples. "For a call, public
common randomness independently samples k uniform identities a1, . . . , ak after F has been fixed. …
The samples are independent of F and of prior call transcripts."

At the boundary, first the common election (if scheduled) is drawn from `E` as in the base model; then
`k` identities `a₁, …, a_k` are drawn uniformly and independently of each other and of everything else;
the adversary observes each of them (`Obs.elected r aⱼ`, after the election output); and every active
uncorrupted player receives them at the front of its inbox, as the entries `(n, encNat aⱼ)`, sent by the
pseudo-identity `n` that no player has (real senders are `< n`).

**Formalization Note.** The samples are an ideal public resource: they are not honest transmissions,
so `msgCount` does not count them ("their implementation traffic is not counted", §4.3), and they take
no extra round. With `k = 0` this is exactly the base boundary. -/
noncomputable def boundaryB (P : Params) (elect : Bool) (k : ℕ)
    (E : List (Event P.n Str St) → PMF (Fin P.n)) (c : Config P.n Str St σ) :
    PMF (Config P.n Str St σ) :=
  (if elect then (E c.log).map some else PMF.pure none).bind fun L =>
    (PMF.uniformOfFintype (Fin k → Fin P.n)).bind fun a =>
      let c₁ := match L with
        | some l => c.push (Obs.elected c.round l)
        | none => c
      let c₁' := (List.ofFn a).foldl (fun d l => d.push (Obs.elected c.round l)) c₁
      let c₂ := c₁'.push (Obs.boundary c.round)
      let beacon : List (ℕ × Str) := (List.ofFn a).map fun l => (P.n, encNat l.val)
      PMF.pure { c₂ with
        resp := fun i =>
          if i ∉ c.corrupted ∧ c.active i = true then
            Resp.boundary (beacon ++ c.inbox i) (L.map Fin.val)
          else c.resp i
        inbox := fun _ => []
        round := c.round + 1
        doneAt := c.doneAt.orElse fun _ =>
          if ∀ i, i ∉ c.corrupted → c.active i = false then some (c.round + 1) else none }

/-- Whether some boundary strictly before round `r` revealed collector samples, under the public
sample schedule `sched` (`sched P r` samples at the boundary of round `r`). -/
def samplesRevealedBefore (sched : Params → ℕ → ℕ) (P : Params) (r : ℕ) : Bool :=
  (List.range r).any fun r' => sched P r' != 0

/-- One round of the static-corruption model (§6.1, p.19; Theorem 2, p.3: "if the corrupt set is fixed
before fresh public collector samples"). As `BeyondDS.oneRound`, except that

* the boundary is `boundaryB`, revealing `sched P r` fresh collector samples;
* once a boundary has revealed collector samples, the corrupt set is frozen: the corruption budget passed
  to the moves is the number of players already corrupted, so a move naming a new corruption has its
  corruptions ignored (`Config.corruptAll`).

Before the first sample reveal the adversary may corrupt up to `t` players, adaptively, as in the base
model; afterwards it never corrupts again. Corrupted players are Byzantine. -/
noncomputable def oneRoundB (Pi : Protocol Str St) (sched : Params → ℕ → ℕ) (S : Sig) (P : Params)
    (E : List (Event P.n Str St) → PMF (Fin P.n)) (A : Adversary P.n Str St)
    (c : Config P.n Str St A.σ) : PMF (Config P.n Str St A.σ) :=
  let tb : ℕ := if samplesRevealedBefore sched P c.round then c.corrupted.card else P.t
  (moves S (Pi.next P) tb A.step (P.n * Pi.opCap P + P.n + P.t + 1)
    { c with
      budget := fun _ => Pi.opCap P
      yielded := fun _ => false }).bind (boundaryB P (Pi.electAt P c.round) (sched P c.round) E)

/-- `k` further rounds of the static-corruption model. -/
noncomputable def runRoundsB (Pi : Protocol Str St) (sched : Params → ℕ → ℕ) (S : Sig) (P : Params)
    (E : List (Event P.n Str St) → PMF (Fin P.n)) (A : Adversary P.n Str St) :
    ℕ → Config P.n Str St A.σ → PMF (Config P.n Str St A.σ)
  | 0, c => PMF.pure c
  | k + 1, c => (oneRoundB Pi sched S P E A c).bind (runRoundsB Pi sched S P E A k)

/-- The whole execution of protocol `Pi` with public collector-sample schedule `sched`, under scheme `S`,
parameters `P`, sender input `x`, election law `E` and adversary `A`, in the static-corruption model:
the base setup (`BeyondDS.setup`: honest keys, nobody corrupted), then rounds of `oneRoundB` through the
public cap, then the base final local computation (`BeyondDS.finalize`).

**Formalization Note.** Every adversary of the base type is admitted; the model itself makes it static,
by ignoring every corruption after the first collector-sample reveal. -/
noncomputable def execStatic (Pi : Protocol Str St) (sched : Params → ℕ → ℕ) (S : Sig) (P : Params)
    (x : Bool) (E : List (Event P.n Str St) → PMF (Fin P.n)) (A : Adversary P.n Str St) :
    PMF (Config P.n Str St A.σ) :=
  (setup Pi S P x A).bind fun c =>
    (runRoundsB Pi sched S P E A (Pi.roundCap P - c.round) c).bind (finalize Pi S P)

/-- The efficiency clause of `BeyondDS.IsEfficientProtocol`, for a protocol run with a public
collector-sample schedule in the static-corruption model (§4.2, p.12; §6.1, p.19): one polynomial-time
machine computes `next` for all parameters, and `init`, the election schedule and the sample schedule
likewise; the round cap, the operation cap and the number of samples per boundary are polynomial in
`κ + t + λ`; and in every run of `execStatic`, each honest local state and each honest message has length
polynomial in `κ + t + λ`, the signature length and the bits the adversary has injected so far. -/
def IsEfficientStaticProtocol (Pi : Protocol Str Str) (sched : Params → ℕ → ℕ) (p : ℕ[X]) : Prop :=
  (∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ (P : Params) (s : Str) (r : Resp Str),
      f (tup [encParams P, s, encResp r]) =
        tup [encOp (Pi.next P s r).1, (Pi.next P s r).2]) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ (P : Params) (i : Fin P.n) (x : Option Bool),
      f (tup [encParams P, encNat i.val, encOptBool x]) = Pi.init P i x) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ (P : Params) (r : ℕ), f (tup [encParams P, encNat r]) = encBool (Pi.electAt P r)) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ (P : Params) (r : ℕ), f (tup [encParams P, encNat r]) = encNat (sched P r)) ∧
  (∀ P : Params, Pi.roundCap P ≤ p.eval (P.κ + P.t + P.lam)) ∧
  (∀ P : Params, Pi.opCap P ≤ p.eval (P.κ + P.t + P.lam)) ∧
  (∀ (P : Params) (r : ℕ), sched P r ≤ p.eval (P.κ + P.t + P.lam)) ∧
  (∀ (S : Sig) (P : Params) (x : Bool) (E : List (Event P.n Str Str) → PMF (Fin P.n))
      (A : Adversary P.n Str Str) (ω : Config P.n Str Str A.σ),
    S.Correct → ω ∈ (execStatic Pi sched S P x E A).support →
    ∀ (pre : List (Event P.n Str Str)) (e : Event P.n Str Str) (post : List (Event P.n Str Str)),
      ω.log = pre ++ e :: post →
      honestBits e ≤ p.eval (P.κ + P.t + P.lam + S.sigLen + injectedBits pre))

end BeyondDS.Supplement


