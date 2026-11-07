-- Prove2me | Definitions.Def_BeyondDS_TokenState
-- name    : BeyondDS_TokenState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:51.226149+00:00
-- url     : https://prove2.me/theorems/f9d866a7-ebe9-489a-b9a6-c4f334f11295
-- title:
--   The token game of two spreading rounds
-- statement:
--   The token game is the possession content of the epochs of §§7.2–7.3. Players hold finite sets of tokens (records). In each round every uncorrupted player freezes what it holds at the beginning of the round and owes $K$ random trials carrying it. An adaptive adversary sees the whole state after every trial (every destination and every holding), may corrupt one more player between trials (permanently, at most $t$ in total), may add tokens to any player's incoming set through a corrupted identity, and chooses which uncorrupted player with trials left performs the next trial (the least one if its choice cannot). A trial draws a fresh uniform destination and commits the frozen set to it; a trial to the sender itself is free, every other trial counts one message. At the delivery boundary each uncorrupted player adds what it received to its holding. Two rounds form an epoch. A start has any corrupted set of size at most $t$ and arbitrary holdings.
--
--   **Formalization Note** Buffers are tokens: Lemmas 7.4 and 7.5 concern possession only. Injection by the adversary only enlarges holdings and never changes an honest trial count.
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), §§7.2–7.3, pp.23–25 (PDF pp.24–26); Lemma 7.4, p.24; Lemma 7.5, p.24

import Mathlib

set_option autoImplicit false

namespace BeyondDS

/-- The state of the token game of §§7.2–7.3, pp.24–25: who holds which records.

* `corrupted`, and the identities uncorrupted through each round follow from `corruptAt`.
* `hold i`: what `i` retains and can use in this round.
* `recv i`: what will be delivered to `i` at this round's boundary.
* `trials i`: random trials `i` has yet to perform in this round.
* `carry i`: the buffer frozen for `i` at the beginning of this round.
* `msgs`: messages sent while the sender is honest. -/
structure TokenState (n : ℕ) (Token : Type) where
  round : ℕ
  corrupted : Finset (Fin n)
  corruptAt : Fin n → Option ℕ
  hold : Fin n → Finset Token
  recv : Fin n → Finset Token
  trials : Fin n → ℕ
  carry : Fin n → Finset Token
  msgs : ℕ

/-- One move of the adversary in the token game: one more corruption, tokens delivered through corrupted
identities, and the next sender (`none`: the least that can still send). -/
structure TokenMove (n : ℕ) (Token : Type) where
  corrupt : Option (Fin n)
  inject : List (Fin n × Finset Token)
  next : Option (Fin n)

/-- An adaptive adversary of the token game. It sees the whole state after every trial, including every
destination and every holding, and corrupts or injects between trials. Its strategy is arbitrary. -/
structure TokenAdversary (n : ℕ) (Token : Type) where
  σ : Type
  step : σ → TokenState n Token → PMF (σ × TokenMove n Token)

variable {n : ℕ} {Token : Type} [DecidableEq Token]

/-- The budget rule and permanence of corruption, and injection through corrupted identities only. -/
def TokenState.applyMove (t : ℕ) (c : TokenState n Token) (m : TokenMove n Token) : TokenState n Token :=
  let c₁ : TokenState n Token :=
    match m.corrupt with
    | some i =>
      if i ∉ c.corrupted ∧ c.corrupted.card < t then
        { c with
          corrupted := insert i c.corrupted
          corruptAt := Function.update c.corruptAt i (some c.round) }
      else c
    | none => c
  if c₁.corrupted.Nonempty then
    { c₁ with recv := fun j => c₁.recv j ∪ (m.inject.filter fun e => e.1 = j).foldr (fun e s => e.2 ∪ s) ∅ }
  else c₁

/-- The player who performs the next trial: the one named if it can, else the least that can. -/
def TokenState.nextSender (c : TokenState n Token) (m : TokenMove n Token) : Option (Fin n) :=
  let can : Fin n → Bool := fun i => decide (i ∉ c.corrupted) && decide (0 < c.trials i)
  match m.next with
  | some i => if can i then some i else (List.finRange n).find? can
  | none => (List.finRange n).find? can

/-- A trial of `i`: a fresh uniform destination; a committed transmission of `i`'s frozen buffer. A trial to
`i` itself is a free local delivery (§7.1, p.22). -/
def TokenState.trial (c : TokenState n Token) (i d : Fin n) : TokenState n Token :=
  { c with
    recv := Function.update c.recv d (c.recv d ∪ c.carry i)
    trials := Function.update c.trials i (c.trials i - 1)
    msgs := if i = d then c.msgs else c.msgs + 1 }

/-- The moves of one round of the token game. A move with a new corruption performs no trial, so the
adversary can corrupt several players between two trials. -/
noncomputable def tokenMoves [NeZero n] (t : ℕ) (A : TokenAdversary n Token) :
    ℕ → A.σ × TokenState n Token → PMF (A.σ × TokenState n Token)
  | 0, x => PMF.pure x
  | f + 1, (a, c) =>
    (A.step a c).bind fun am =>
      let c₁ := c.applyMove t am.2
      if c₁.corrupted ≠ c.corrupted then tokenMoves t A f (am.1, c₁)
      else
        match c₁.nextSender am.2 with
        | some i =>
          (PMF.uniformOfFintype (Fin n)).bind fun d => tokenMoves t A f (am.1, c₁.trial i d)
        | none => tokenMoves t A f (am.1, c₁)

/-- One round: every uncorrupted player freezes what it holds at the beginning of the round and owes `K`
trials carrying it; then the moves; then the delivery boundary, at which uncorrupted players retain what was
sent to them. The fuel allows for all trials and for `t + 1` further moves. -/
noncomputable def tokenRound [NeZero n] (t K : ℕ) (A : TokenAdversary n Token)
    (x : A.σ × TokenState n Token) : PMF (A.σ × TokenState n Token) :=
  (tokenMoves t A (n * K + t + 1)
      (x.1, { x.2 with
        carry := x.2.hold
        trials := fun i => if i ∈ x.2.corrupted then 0 else K
        recv := fun _ => ∅ })).map fun y =>
    (y.1, { y.2 with
      hold := fun i => if i ∈ y.2.corrupted then y.2.hold i else y.2.hold i ∪ y.2.recv i
      round := y.2.round + 1
      trials := fun _ => 0 })

/-- Two rounds of the game: the two-round epoch of Lemma 7.4 (p.24) and the two spreading rounds of Lemma 7.5
(p.24). -/
noncomputable def tokenEpoch [NeZero n] (t K : ℕ) (A : TokenAdversary n Token)
    (x : A.σ × TokenState n Token) : PMF (A.σ × TokenState n Token) :=
  (tokenRound t K A x).bind (tokenRound t K A)

/-- A start of the game: a corrupted set of size at most `t`, arbitrary holdings, and round `0`. -/
def tokenStart (C₀ : Finset (Fin n)) (h : Fin n → Finset Token) : TokenState n Token where
  round := 0
  corrupted := C₀
  corruptAt := fun i => if i ∈ C₀ then some 0 else none
  hold := h
  recv := fun _ => ∅
  trials := fun _ => 0
  carry := h
  msgs := 0

/-- `i` is uncorrupted through the epoch's two rounds. -/
def TokenState.UncorruptedThroughEpoch (c : TokenState n Token) (i : Fin n) : Prop :=
  c.corruptAt i = none

end BeyondDS


