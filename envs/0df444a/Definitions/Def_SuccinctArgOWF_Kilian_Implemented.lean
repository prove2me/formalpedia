-- Prove2me | Definitions.Def_SuccinctArgOWF_Kilian_Implemented
-- name    : SuccinctArgOWF_Kilian_Implemented
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:19.818889+00:00
-- url     : https://prove2.me/theorems/1e1d419d-89f4-4fcd-98da-11abec6fc3d1
-- title:
--   Public-coin schedules and commitment families given by uniform sender and receiver machines
-- statement:
--   Honest parties are single machines (uniform algorithms) that take the parameter as input; their running time is their number of steps.
--
--   **Public-coin schedules.** On a public input, a receiver (or verifier) machine $V$ is queried for round $j=0,1,2,\dots$; it either continues and announces a length $m_j$, or stops. The number of rounds is the first round in which it stops; the round-$j$ message is a uniformly random string in $\{0,1\}^{m_j}$. The schedule is well formed if $V$ stops in some round and every query up to that round halts. Its time is the total running time of these queries.
--
--   **Canonical commitments from a sender machine.** For a sender machine $\mathrm{Snd}$, a message length $n$, $\ell$ rounds and receiver message lengths $m_1,\dots,m_\ell$, the scheme has $R_j=\{0,1\}^{m_j}$, $\mathrm{state}_0=x$, next-message functions computed by $\mathrm{Snd}$ on (state, $r_j$, $n$, $j$), empty proofs and the canonical verifier $\mathrm{Ver}(\rho,\tau,x,\pi)=1\iff\mathrm{tr}(x,\rho)=\tau$.
--
--   **Interval commitments from a sender and a receiver machine.** For machines $\mathrm{Snd},\mathrm{Rcv}$ and $N$: the receiver's schedule on input $N$ fixes the rounds and $R_j=\{0,1\}^{m_j}$; the sender's messages and openings are computed by $\mathrm{Snd}$; $\mathrm{Ver}(\rho,\tau,I,v,\pi)=1$ iff $\mathrm{Rcv}$, run on $(N,\rho,\tau,I,v,\pi)$, halts with output $1$.
--
--   These families carry the efficiency claims of Theorem 4.1 and Corollary 6.3.
-- source:
--   Jesko Dujmovic, Daniel Wichs, STOC 2027 submission #650 (October 2026), §3.3, p. 8 (PDF p. 10); Theorem 4.1, p. 10 (PDF p. 12); Corollary 6.3, p. 20 (PDF p. 22)

import Mathlib
import Definitions.Def_SuccinctArgOWF_Kilian_Commit

set_option autoImplicit false

namespace SuccinctArgOWF.Kilian

/-! # Commitment families implemented by uniform machines, and public-coin schedules

Honest parties are single machines (uniform algorithms) taking the parameter as input; their running
time is their number of steps. A public-coin receiver/verifier announces, round by round, only the
length of its next message; the message itself is a uniformly random string of that length. -/

open MetaSearch.Heyting

/-! ## Public-coin schedules -/

/-- The schedule query for round `j` (from `0`) on public input `pub`. -/
def schedIns (pub : List Str) (j : ℕ) : List Str := pub ++ [[false], natBits j]

/-- In round `j` the receiver `V` halts, continues (output `[1]` on tape `0`) and sends a uniformly
random string whose length is written in binary on tape `1`. -/
def SchedCont (V : Machine) (pub : List Str) (j : ℕ) : Prop :=
  Halts V (schedIns pub j) ∧ out V (schedIns pub j) 0 = [true]

/-- In round `j` the receiver halts and stops sending (any output other than `[1]`). -/
def SchedStop (V : Machine) (pub : List Str) (j : ℕ) : Prop :=
  Halts V (schedIns pub j) ∧ out V (schedIns pub j) 0 ≠ [true]

/-- The length of the receiver's round-`j` message. -/
noncomputable def schedLen (V : Machine) (pub : List Str) (j : ℕ) : ℕ :=
  bitsVal (out V (schedIns pub j) 1)

open Classical in
/-- The number of rounds: the first round in which the receiver stops. -/
noncomputable def schedRounds (V : Machine) (pub : List Str) : ℕ :=
  if h : ∃ j, SchedStop V pub j then Nat.find h else 0

/-- The schedule is well formed: the receiver stops in some round and continues before it. -/
def SchedOK (V : Machine) (pub : List Str) : Prop :=
  (∃ j, SchedStop V pub j) ∧ ∀ j < schedRounds V pub, SchedCont V pub j

/-- The receiver's total time spent on the schedule (all queries up to and including the stop). -/
noncomputable def schedTime (V : Machine) (pub : List Str) : ℕ :=
  ((List.range (schedRounds V pub + 1)).map fun j => time V (schedIns pub j)).sum

/-- All receiver message vectors of the schedule. -/
abbrev SchedCoins (V : Machine) (pub : List Str) :=
  (j : Fin (schedRounds V pub)) → ↥(allStr (schedLen V pub j))

/-- The set `{0,1}^m` is nonempty. -/
theorem allStr_nonempty (m : ℕ) : (allStr m).Nonempty :=
  Finset.univ_nonempty.image _

/-! ## Plain canonical commitments from a sender machine (Theorem 4.1) -/

/-- The honest sender's round-`j` invocation on parameter `n`: inputs `[state, r_j, bin n, [0], bin j]`,
outputs the new state (tape `0`) and the message `y_j` (tape `1`). -/
def sndIns (n j : ℕ) (st r : Str) : List Str := [st, r, natBits n, [false], natBits j]

/-- The next-message function computed by `Snd`. -/
noncomputable def sndStep (Snd : Machine) (n : ℕ) (j : ℕ) (st r : Str) : Str × Str :=
  (out Snd (sndIns n j st r) 1, out Snd (sndIns n j st r) 0)

/-- The `ℓ`-round public-coin commitment for `n`-bit messages with the canonical opening whose
sender is the machine `Snd` and whose receiver sends uniformly random strings of lengths
`m₁, …, m_ℓ`: `state₀ = x`, `S_j = sndStep Snd n j`, empty proofs, and `Ver(ρ, τ, x, π) = 1` iff
`tr(x, ρ) = τ`. -/
noncomputable def canonFamily (Snd : Machine) (n ℓ : ℕ) (m : Fin ℓ → ℕ) : Commit where
  n := n
  ℓ := ℓ
  R := fun j => allStr (m j)
  R_ne := fun j => allStr_nonempty (m j)
  σ := Str
  init := fun x => x
  S := fun j st r => sndStep Snd n j.1 st r
  Open := fun _ => []
  Ver := fun ρ τ x _ =>
    decide (transcript (fun x => x) (fun (j : Fin ℓ) st r => sndStep Snd n j.1 st r) x ρ = τ)

/-! ## Interval commitments from a sender and a receiver machine (Corollary 6.3) -/

/-- The receiver's verification input for coins `ρ`, sender messages `τ`, interval `{a, …, b}`,
values `v` and proof `π`, on parameter `N`. -/
def rcvIns (N : ℕ) (ρ τ : List Str) (a b : ℕ) (v π : Str) : List Str :=
  [natBits N, [true], encList ρ, encList τ, encList [natBits a, natBits b, v, π]]

/-- The sender's opening input for the interval `{a, …, b}`. -/
def openIns (N : ℕ) (st : Str) (a b : ℕ) : List Str :=
  [st, [], natBits N, [true], encList [natBits a, natBits b]]

open Classical in
/-- The commitment with interval opening for messages in `{0,1}^N` given by the uniform sender
`Snd` and receiver `Rcv` on parameter `N`: the receiver's schedule (on public input `bin N`) fixes the
rounds and message lengths (`R_j = {0,1}^{m_j}`), `S_j = sndStep Snd N j`, `Open` runs `Snd` in
opening mode, and `Ver` runs `Rcv` on the whole interaction and accepts iff it halts with output
`[1]`. -/
noncomputable def machineVC (Snd Rcv : Machine) (N : ℕ) : ICommit where
  N := N
  ℓ := schedRounds Rcv [natBits N]
  R := fun j => allStr (schedLen Rcv [natBits N] j)
  R_ne := fun _ => allStr_nonempty _
  σ := Str
  init := fun m => m
  S := fun j st r => sndStep Snd N j.1 st r
  Open := fun st a b => out Snd (openIns N st a b) 1
  Ver := fun ρ τ a b v π =>
    decide (Halts Rcv (rcvIns N (List.ofFn ρ) (List.ofFn τ) a b v π) ∧
      out Rcv (rcvIns N (List.ofFn ρ) (List.ofFn τ) a b v π) 0 = [true])

end SuccinctArgOWF.Kilian


