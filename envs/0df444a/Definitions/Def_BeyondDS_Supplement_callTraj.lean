-- Prove2me | Definitions.Def_BeyondDS_Supplement_callTraj
-- name    : BeyondDS_Supplement_callTraj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T05:10:06.918+00:00
-- url     : https://prove2.me/theorems/50dafb8f-037c-458d-b4d1-f7833ed05abc
-- title:
--   Call-boundary trajectories, the boundary $\sigma$, delivery and certificate holders for the parametric compiler
-- statement:
--   These are the events and the conditional laws in which the hypotheses of Theorem 6 are stated.
--
--   **Trajectories.** For calls of $d$ rounds, the trajectory of an execution with $Q$ calls is the list $[c_0,c_1,\dots,c_Q,\omega]$, where $c_j$ is the configuration at the beginning of call $j$ (so $c_{j+1}$ is the configuration at the last delivery boundary of call $j$) and $\omega$ is the outcome after the final local computation. A configuration holds its whole history, so the law of the rest of the trajectory from $c_j$ is the conditional law given the prefix that ends at $c_j$.
--
--   **Returned payloads and held evidence.** At the last boundary of invocation $c$, the payloads returned to player $i$ are the implementation's output on the player's saved state and the messages just delivered, restricted to payloads of this invocation whose source signature verifies. The evidence the player holds at that boundary is its verified store together with the records of these payloads that lie in the public domains and carry valid, authentic signatures; a signature is authentic at the boundary if it is attributed to a corrupted identity or is on data that identity has signed. On histories without an authentication failure this is what the player computes in its next activation, read from the configuration before that activation.
--
--   **Holders and $\sigma$.** A player holds a termination certificate at the beginning of call $c$ if its evidence there contains a verifying termination certificate. The boundary $\sigma$ is the first call at whose beginning some currently uncorrupted player holds one, and $Q=6J+3$ if there is none.
--
--   **Delivery.** The required delivery of invocation $c$ holds at its last boundary if the frozen source payload of every player uncorrupted at that boundary is returned to every player uncorrupted at that boundary.
--
--   **Failure events and certificate decisions.** A declared failure event of call $c$ occurs in a trajectory if it holds of $c_{c+1}$. A player decides by certificate in an outcome if its decision is the bit of a verifying termination certificate in its store.
--
--   **Formalization Note** $\sigma$ depends only on $c_0,\dots,c_\sigma$, as the source requires: "This boundary depends only on the history so far, and does not select a holder by whether it remains honest in the future". The authenticity clause is needed because the holder verifies the returned records, and a forgery is logged, only in its next activation; a forged certificate delivered to a player that is corrupted before that activation would otherwise move $\sigma$ although no forgery is ever logged.
-- source:
--   Rambaud, Beyond Dolev–Strong: Adaptive Byzantine Broadcast with Õ(n^{3/2}) Messages at a Tight Honest Majority, STOC 2027 submission (manuscript sha256 c84cf9c9…), §5.1, p.14 (PDF p.15); p.18 (PDF p.19), the paragraph before Theorem 6; §4.3, p.13 (PDF p.14)

import Mathlib
import Definitions.Def_BeyondDS_Supplement_compilerG

set_option autoImplicit false

open QAlgorithms.Complexity
open scoped ENNReal Classical

namespace BeyondDS.Supplement

open BeyondDS

/-- The configurations at the call boundaries of an execution, for calls of `d` rounds (Rambaud, *Beyond
Dolev–Strong*, STOC 2027 submission (manuscript sha256 c84cf9c9…), §4.3, p.13: "Statistical error bounds for
fresh sampling apply after every fixed reachable prefix"). From a configuration `c` at the beginning of a call,
with `k` calls left, `callTraj … d k c` is the law of the list `[c₀, c₁, …, c_k, ω]`: `c₀ = c`, each `c_{j+1}` is
the configuration `d` rounds after `c_j`, and `ω` is the outcome after the final local computation
(`BeyondDS.finalize`). A configuration holds its whole history, so the law of the rest of the list given its first
entries is the conditional law given that prefix. -/
noncomputable def callTraj {Msg St : Type} (Pi : Protocol Msg St) (S : Sig) (P : Params)
    (E : List (Event P.n Msg St) → PMF (Fin P.n)) (A : Adversary P.n Msg St) (d : ℕ) :
    ℕ → Config P.n Msg St A.σ → PMF (List (Config P.n Msg St A.σ))
  | 0, c => (finalize Pi S P c).map fun ω => [c, ω]
  | k + 1, c =>
    (runRounds Pi S P E A d c).bind fun c' => (callTraj Pi S P E A d k c').map fun τ => c :: τ

section Events

variable {σ : Type}

/-- The public evidence context of a configuration of the compiler `compilerG` with calls of `d` rounds: the
election outputs in the transcript. The election revealed at the boundary of round `R` belongs to iteration
`((R + 1)/d + 1)/6`, by `electAtG`. -/
def publicCtxG (d : ℕ) (P : Params) (J : ℕ) (cf : Config P.n CMsg CSt σ) : EvCtx :=
  ⟨P.n, P.t, P.sender.val, J,
    cf.log.filterMap fun e =>
      match e with
      | Event.obs (Obs.elected R l) => some (((R + 1) / d + 1) / 6, l.val)
      | _ => none⟩

/-- The payloads that invocation `c` returns to player `i`, read from the configuration `cf` at the invocation's
last delivery boundary, before `i` has processed that boundary: the implementation's output on the player's saved
state and the messages just delivered, restricted to payloads of this invocation whose source signature verifies.
This is what `callG` computes in the player's next activation. -/
def returnedTo (D : Dissem) (S : Sig) (P : Params) (J c : ℕ) (cf : Config P.n CMsg CSt σ) (i : Fin P.n) :
    List (Payload (List EvRec)) :=
  let cfg : CallCfg (List EvRec) :=
    ⟨P.n, P.t, 0, 0, c, i.val, P.sender.val, J, electIter J c, true, encRecs⟩
  match cf.resp i with
  | Resp.boundary inbox _ =>
    (D.out cfg (viewOf cf i) inbox).filter fun p =>
      decide (p.sid = c) && cf.checks S p.src (encDatum encRecs (Datum.payload p.sid p.src p.body)) p.sig
  | _ => []

/-- The evidence player `i` holds at the boundary that ends invocation `c`: its verified store and the records,
with valid and authentic signatures and inside the public domains, of the payloads returned to it. A record is
authentic at this boundary when its signature is attributed to a corrupted identity or is on data that identity has
signed (§4.2, p.12: "any verifying data attributed to a currently uncorrupted player were signed by that player").

**Formalization Note.** The player has not yet verified these records: it does so in its next activation, where a
record that verifies but is not authentic is logged as a forgery (`BeyondDS.Forge`). Without the authenticity
clause, a forged certificate delivered to a player that is corrupted before that activation would count as held
although no forgery is ever logged. On histories without an authentication failure the clause changes nothing. -/
noncomputable def evidenceAtG (D : Dissem) (S : Sig) (P : Params) (J c : ℕ) (cf : Config P.n CMsg CSt σ)
    (i : Fin P.n) : List EvRec :=
  let x := publicCtxG D.d P J cf
  (viewOf cf i).store ++ ((returnedTo D S P J c cf i).flatMap Payload.body).filter fun e =>
    e.inDomain x && (let q := e.query encRecs x; cf.checks S q.1 q.2.1 q.2.2 &&
      decide (∀ j : Fin P.n, j.val = q.1 → j ∉ cf.corrupted → (j, q.2.1) ∈ cf.signLog))

/-- Player `i` holds a verifying termination certificate at the beginning of call `c`, in the configuration `cf`
at that boundary (for `c = 0`, the initial configuration, where nobody does). The certificate is built from the
player's verified store and from returned records that verify and are authentic (`evidenceAtG`). -/
def HoldsAtG (D : Dissem) (S : Sig) (P : Params) (J c : ℕ) (cf : Config P.n CMsg CSt σ) (i : Fin P.n) : Prop :=
  ∃ r b, termValid (publicCtxG D.d P J cf) (evidenceAtG D S P J (c - 1) cf i) r b = true

/-- Some currently uncorrupted player holds a termination certificate at the beginning of call `c` of the
trajectory `τ`. -/
def HolderAt (D : Dissem) (S : Sig) (P : Params) (J : ℕ) (τ : List (Config P.n CMsg CSt σ)) (c : ℕ) : Prop :=
  ∃ cf, τ[c]? = some cf ∧ ∃ i, i ∉ cf.corrupted ∧ HoldsAtG D S P J c cf i

/-- The boundary `σ` of p.18, as a call index: "the first beginning of a scheduled call at which some currently
uncorrupted player holds a termination certificate, or the public final deadline if there is no such beginning"
(the value `6J + 3`). "This boundary depends only on the history so far". -/
noncomputable def sigmaG (D : Dissem) (S : Sig) (P : Params) (J : ℕ) (τ : List (Config P.n CMsg CSt σ)) : ℕ :=
  if h : ∃ c, c < 6 * J + 3 ∧ HolderAt D S P J τ c then Nat.find h else 6 * J + 3

/-- The required delivery of invocation `c` (§5.1, p.14), read at the configuration `cf` of its last boundary:
the frozen source payload of every source that "remains honest for the entire invocation" is returned to every
recipient that remains honest for the entire invocation. -/
def DeliveredG (D : Dissem) (S : Sig) (P : Params) (J c : ℕ) (cf : Config P.n CMsg CSt σ) : Prop :=
  ∀ s r : Fin P.n, s ∉ cf.corrupted → r ∉ cf.corrupted → ∀ p,
    (recOf cf s c).bind CallRec.source = some p → p ∈ returnedTo D S P J c cf r

/-- A declared failure event occurs in call `c` of the trajectory: the event `F c` holds of the configuration at
the call's last boundary. -/
def FailAt {P : Params} (F : ℕ → Config P.n CMsg CSt σ → Prop) (τ : List (Config P.n CMsg CSt σ))
    (c : ℕ) : Prop :=
  ∃ cf, τ[c + 1]? = some cf ∧ F c cf

/-- The decision of `i` in the outcome `ω` comes from a verifying termination certificate in its store. -/
def DecidedByCert (d : ℕ) (P : Params) (J : ℕ) (ω : Config P.n CMsg CSt σ) (i : Fin P.n) : Prop :=
  ∃ r b, ω.decision i = some b ∧ termValid (publicCtxG d P J ω) (viewOf ω i).store r b = true

end Events

end BeyondDS.Supplement


