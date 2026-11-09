-- Prove2me | Definitions.Def_EfronBroadcast_Main_Network
-- name    : EfronBroadcast_Main_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:02:41.37507+00:00
-- url     : https://prove2.me/theorems/d1d2342c-8233-4b0b-b270-b2010f29970b
-- title:
--   Synchronous executions, ideal signatures and primitive sizes
-- statement:
--   A deterministic synchronous protocol is given by local rules: an initial state per party, the messages a party sends in round $r$ as a function of its own local state, and its next state as a function of the messages delivered at the end of round $r$, each tagged with its authentic source. An adversary in one execution is the realized corruption-time map together with the messages each party sends once corrupted. Quantifying over all such values covers every adaptive, rushing strategy against a deterministic protocol, including omission and equivocation; the silent adversary always exists, so no execution set is empty.
--
--   Ideal signatures: if a corrupt party sends a signature in round $r$, then its signer is corrupt by round $r$, or that signature was sent in some round $r'\le r$ by a then-uncorrupted party in a message whose sender or destination is corrupt by round $r$ (corruption cedes the internal state). The sent-bit count sums the serialized length of every copy sent by correct parties, including copies to faulty parties.
--
--   Primitive sizes are parameters with $\mathrm{sig},\mathrm{com}\le\kappa\lambda$ and $\mathrm{opening}(L)\le\kappa\lambda(1+\lceil\log_2 L\rceil)$. The constant $\kappa$ is the $O(\cdot)$ constant of §2; no numerical length is invented.
-- source:
--   Yuval Efron, Jovan Komatovic, Ling Ren, Byzantine Broadcast in Õ(n²) Communication, STOC 2027 submission #526 (October 2026), p. 1, PDF p. 2, §2, Model & primitives; pinned local source.pdf, SHA256 626a479d5227c34ed2d6343fdc7113666962d88d8b482e8a2be02db9f8028a0f

import Mathlib
import Definitions.Def_EfronBroadcast_Main_FaultModel
set_option autoImplicit false

namespace EfronBroadcast.Main

/-- A deterministic synchronous protocol given by local rules: the initial state of each party,
the messages it sends in round `r` from its local state alone, and its next local state from the
messages delivered at the end of round `r` (each tagged with its authentic source). -/
structure Machine (n : ℕ) (Msg State : Type) where
  init : Party n → State
  send : ℕ → Party n → State → List (Party n × Msg)
  recv : ℕ → Party n → State → List (Party n × Msg) → State

/-- One execution's Byzantine behaviour: the realized corruption times and, for every round and
party, the messages it sends once corrupted. Quantifying over all such values covers every
adaptive rushing strategy against a deterministic protocol, including omission and equivocation. -/
structure NetAdversary (n : ℕ) (Msg : Type) where
  corruptions : Corruptions n
  sends : ℕ → Party n → List (Party n × Msg)

section Execution

variable {n : ℕ} {Msg State : Type} (m : Machine n Msg State) (adv : NetAdversary n Msg)

/-- What `src` sends in round `r` when the local states are `g`. -/
noncomputable def outgoing (g : Party n → State) (r : ℕ) (src : Party n) :
    List (Party n × Msg) := by
  classical
  exact if IsCorruptAt adv.corruptions r src then adv.sends r src else m.send r src (g src)

/-- The messages delivered to `p` at the end of round `r`, with their sources. -/
noncomputable def delivered (g : Party n → State) (r : ℕ) (p : Party n) :
    List (Party n × Msg) :=
  (List.finRange n).flatMap (fun src =>
    ((outgoing m adv g r src).filter (fun e => e.1 = p)).map (fun e => (src, e.2)))

/-- Local states at the start of round `r`; rounds are numbered from `0`. -/
noncomputable def globalState : ℕ → Party n → State
  | 0 => m.init
  | r + 1 => fun p => m.recv r p (globalState r p) (delivered m adv (globalState r) r p)

/-- The messages actually sent by `src` in round `r` of the execution. -/
noncomputable def sentAt (r : ℕ) (src : Party n) : List (Party n × Msg) :=
  outgoing m adv (globalState m adv r) r src

/-- Ideal signatures. `sigs` lists the signatures `(signer, body)` a message carries. Whenever a
corrupt party sends a signature in round `r`, its signer is corrupt by round `r`, or the signature
was sent earlier (or in this round: rushing) by a then-uncorrupted party, in a message whose
sender or destination is corrupt by round `r` (corruption cedes the internal state). -/
def Unforgeable {Body : Type} (sigs : Msg → List (Party n × Body)) : Prop :=
  ∀ r p, IsCorruptAt adv.corruptions r p → ∀ e ∈ adv.sends r p, ∀ sg ∈ sigs e.2,
    IsCorruptAt adv.corruptions r sg.1 ∨
    ∃ r' ≤ r, ∃ (src dst : Party n) (m' : Msg),
      ¬ IsCorruptAt adv.corruptions r' src ∧ (dst, m') ∈ sentAt m adv r' src ∧ sg ∈ sigs m' ∧
        (IsCorruptAt adv.corruptions r dst ∨ IsCorruptAt adv.corruptions r src)

/-- Bits in a list of addressed messages, counting every copy. -/
def listBits (bits : Msg → ℕ) (l : List (Party n × Msg)) : ℕ :=
  (l.map (fun e => bits e.2)).sum

/-- Total bits sent by correct parties during rounds `0, …, R - 1`, counting every copy,
including copies sent to faulty parties; faulty parties' own bits are not counted. -/
noncomputable def correctBits (bits : Msg → ℕ) (R : ℕ) : ℕ := by
  classical
  exact ∑ p ∈ Finset.univ.filter (fun p => IsCorrect adv.corruptions p),
    ∑ r ∈ Finset.range R, listBits bits (sentAt m adv r p)

end Execution

/-- Bit lengths of the ideal primitives at one security parameter. Terms are symbolic, so that
unforgeability and binding are structural, and each primitive is charged these lengths. -/
structure PrimitiveSizes where
  sig : ℕ
  com : ℕ
  opening : ℕ → ℕ

/-- §2: signatures and commitments have `O(λ)` bits and openings of a length-`L` vector have
`O(λ log L)` bits, with `κ` the implied constant (`1 + clog` accounts for `L ≤ 1`). -/
def PrimitiveSizes.Bounded (Z : PrimitiveSizes) (κ lam : ℕ) : Prop :=
  Z.sig ≤ κ * lam ∧ Z.com ≤ κ * lam ∧ ∀ L, Z.opening L ≤ κ * lam * (1 + Nat.clog 2 L)

end EfronBroadcast.Main


