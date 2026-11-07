-- Prove2me | Definitions.Def_CharPSComp_run
-- name    : CharPSComp_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:18.653889+00:00
-- url     : https://prove2.me/theorems/702f181d-a940-47a8-8e25-7b67f493aa09
-- title:
--   Algebraic RAM over a commutative ring: instructions, states, one step, runs, cost, working space
-- statement:
--   This definition fixes the machine on which every cost statement of the mission is made, following the computational model of §2.2 and the multiplication primitive of §2.3.
--
--   A **program** is a finite list of instructions acting on a program counter, a **word memory** $W:\mathbb N\to\mathbb Z$ and a **ring memory** $R:\mathbb N\to R$ over a commutative ring $R$.
--
--   1. *Word instructions:* constants, $+,-,\times$, Euclidean division and remainder ($x/0=0$), shifts by a nonnegative amount, and indirect load/store $W[d]:=W[W[a]]$, $W[W[a]]:=W[b]$.
--   2. *Ring instructions:* $R[d]:=R[a]\pm R[b]$, $R[d]:=R[a]\cdot R[b]$, indirect load/store through a word address, and $R[d]:=W[a]\cdot 1_R$.
--   3. *Control:* unconditional jump, jump if $W[a]=0$, jump if $W[a]<W[b]$, and `halt`.
--   4. *Polynomial multiplication* `pmul`: for $\ell=W[\mathrm{len}]\ge1$ it writes the $2\ell-1$ coefficients of $\big(\sum_{i<\ell}R[W[x]+i]z^i\big)\big(\sum_{i<\ell}R[W[y]+i]z^i\big)$ from $R[W[\mathrm{dst}]]$ on, reading all inputs first.
--
--   Every executed instruction costs $1$, except `pmul` on length $\ell$, which costs $M(\ell)$ for a cost function $M$ supplied to the step function. A negative address or shift, an invalid program counter or a `pmul` with $\ell<1$ is a *stuck step*: it is charged $1$ and changes nothing else, so only `halt` halts; halted states stay put at no cost. A state also records the sets of word and ring addresses written so far and the largest absolute value of any word held so far. The **working space** of a state is the number of distinct word addresses plus the number of distinct ring addresses written, and `ReadOnly nw nr` says that no word cell below $nw$ and no ring cell below $nr$ was written.
--
--   No instruction compares ring elements, maps a ring element to a word, or inverts in $R$, so control flow never depends on ring values: one program runs uniformly over every ring.
--
--   **Formalization Note** `run M P s k` is the state after $k$ steps; `initState ws rs` puts the lists `ws` and `rs` at addresses $0,1,\dots$ of the two memories, with all other cells $0$.
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), §2.2 Computational model, p.4 (PDF p.5); §2.3 Polynomial multiplication, p.5 (PDF p.6)

import Mathlib

namespace CharPSComp

/-- One instruction of the algebraic RAM of Zhu, *Faster Power Series Composition in Fixed Positive
Characteristic*, STOC 2027 submission (manuscript sha256 e63e0527…), §2.2 "Computational model",
p.4 (PDF p.5), and §2.3 "Polynomial multiplication", p.5 (PDF p.6).

The machine has a word memory `W : ℕ → ℤ` and a ring memory `R : ℕ → R`. Arguments named `d a b`
are direct addresses (natural-number literals of the instruction); `W[a]` used as an address is an
indirect access.

* word instructions: `wconst d k` (`W[d] := k`), `wadd`, `wsub`, `wmul`, `wdiv`, `wmod`
  (`W[d] := W[a] ∘ W[b]`, Lean's `Int.ediv`/`Int.emod`, so `x / 0 = 0`), `wshl`, `wshr`
  (shift `W[a]` by `W[b] ≥ 0` bits), `wload d a` (`W[d] := W[W[a]]`), `wstore a b`
  (`W[W[a]] := W[b]`);
* ring instructions: `radd`, `rsub`, `rmul` (`R[d] := R[a] ∘ R[b]`), `rload d a`
  (`R[d] := R[W[a]]`), `rstore a b` (`R[W[a]] := R[b]`), `rint d a` (`R[d] := W[a] · 1_R`);
* control: `jmp t`, `jz a t` (jump if `W[a] = 0`), `jlt a b t` (jump if `W[a] < W[b]`), `halt`;
* `pmul dst x y len`: with `ℓ = W[len] ≥ 1`, writes the `2ℓ − 1` coefficients of
  `(Σ_{i<ℓ} R[W[x]+i] zⁱ)(Σ_{i<ℓ} R[W[y]+i] zⁱ)` to `R[W[dst]+j]`, `j < 2ℓ − 1`.

**Formalization Note** No instruction carries a ring element or a function, and there is no ring
comparison, no map from ring elements to words, and no inversion or division in the ring, so control
flow never depends on ring values. -/
inductive Instr : Type
  | wconst (d : ℕ) (k : ℤ)
  | wadd (d a b : ℕ)
  | wsub (d a b : ℕ)
  | wmul (d a b : ℕ)
  | wdiv (d a b : ℕ)
  | wmod (d a b : ℕ)
  | wshl (d a b : ℕ)
  | wshr (d a b : ℕ)
  | wload (d a : ℕ)
  | wstore (a b : ℕ)
  | radd (d a b : ℕ)
  | rsub (d a b : ℕ)
  | rmul (d a b : ℕ)
  | rload (d a : ℕ)
  | rstore (a b : ℕ)
  | rint (d a : ℕ)
  | jmp (t : ℕ)
  | jz (a t : ℕ)
  | jlt (a b t : ℕ)
  | pmul (dst x y len : ℕ)
  | halt
  deriving DecidableEq

/-- A program is a finite list of instructions; the program counter indexes it from `0`. -/
abbrev Program : Type := List Instr

/-- A machine state over the ring `R`: program counter, word memory, ring memory, the halted flag,
the cost charged so far, the sets of word and ring addresses written so far, and the largest
absolute value of a word held so far (initial words included). -/
structure State (R : Type*) where
  pc : ℕ
  wmem : ℕ → ℤ
  rmem : ℕ → R
  halted : Bool
  cost : ℕ
  wWritten : Finset ℕ
  rWritten : Finset ℕ
  maxWord : ℕ

variable {R : Type*} [CommRing R]

/-- A stuck step (invalid program counter, negative address or shift, `pmul` with length `< 1`):
it is charged one unit and changes nothing else, so a stuck machine never halts. -/
def State.stuck (s : State R) : State R := { s with cost := s.cost + 1 }

/-- Advance the program counter and charge one unit. -/
def State.next (s : State R) : State R := { s with pc := s.pc + 1, cost := s.cost + 1 }

/-- Jump to `t` and charge one unit. -/
def State.jumpTo (s : State R) (t : ℕ) : State R := { s with pc := t, cost := s.cost + 1 }

/-- Write the word `x` to word address `d`, recording the address and the size of `x`. -/
def State.wset (s : State R) (d : ℕ) (x : ℤ) : State R :=
  { s with wmem := Function.update s.wmem d x, wWritten := insert d s.wWritten,
           maxWord := max s.maxWord x.natAbs }

/-- Write the ring element `x` to ring address `d`, recording the address. -/
def State.rset (s : State R) (d : ℕ) (x : R) : State R :=
  { s with rmem := Function.update s.rmem d x, rWritten := insert d s.rWritten }

/-- Coefficient `j` of `(Σ_{a<ℓ} r(x+a) zᵃ)(Σ_{b<ℓ} r(y+b) zᵇ)`. -/
def pmulOut (r : ℕ → R) (x y ℓ j : ℕ) : R :=
  ∑ a ∈ Finset.range ℓ, ∑ b ∈ Finset.range ℓ, if a + b = j then r (x + a) * r (y + b) else 0

/-- Execute one instruction. Every instruction costs `1`, except `pmul` on length `ℓ`, which costs
`M ℓ`. -/
def exec (M : ℕ → ℕ) (s : State R) : Instr → State R
  | .wconst d k => (s.wset d k).next
  | .wadd d a b => (s.wset d (s.wmem a + s.wmem b)).next
  | .wsub d a b => (s.wset d (s.wmem a - s.wmem b)).next
  | .wmul d a b => (s.wset d (s.wmem a * s.wmem b)).next
  | .wdiv d a b => (s.wset d (Int.ediv (s.wmem a) (s.wmem b))).next
  | .wmod d a b => (s.wset d (Int.emod (s.wmem a) (s.wmem b))).next
  | .wshl d a b =>
      if 0 ≤ s.wmem b then (s.wset d (s.wmem a * 2 ^ (s.wmem b).toNat)).next else s.stuck
  | .wshr d a b =>
      if 0 ≤ s.wmem b then (s.wset d (Int.ediv (s.wmem a) (2 ^ (s.wmem b).toNat))).next
      else s.stuck
  | .wload d a =>
      if 0 ≤ s.wmem a then (s.wset d (s.wmem (s.wmem a).toNat)).next else s.stuck
  | .wstore a b =>
      if 0 ≤ s.wmem a then (s.wset (s.wmem a).toNat (s.wmem b)).next else s.stuck
  | .radd d a b => (s.rset d (s.rmem a + s.rmem b)).next
  | .rsub d a b => (s.rset d (s.rmem a - s.rmem b)).next
  | .rmul d a b => (s.rset d (s.rmem a * s.rmem b)).next
  | .rload d a =>
      if 0 ≤ s.wmem a then (s.rset d (s.rmem (s.wmem a).toNat)).next else s.stuck
  | .rstore a b =>
      if 0 ≤ s.wmem a then (s.rset (s.wmem a).toNat (s.rmem b)).next else s.stuck
  | .rint d a => (s.rset d ((s.wmem a : ℤ) : R)).next
  | .jmp t => s.jumpTo t
  | .jz a t => if s.wmem a = 0 then s.jumpTo t else s.next
  | .jlt a b t => if s.wmem a < s.wmem b then s.jumpTo t else s.next
  | .pmul dst x y len =>
      if 1 ≤ s.wmem len ∧ 0 ≤ s.wmem dst ∧ 0 ≤ s.wmem x ∧ 0 ≤ s.wmem y then
        { s with
          rmem := fun i =>
            if (s.wmem dst).toNat ≤ i ∧ i < (s.wmem dst).toNat + (2 * (s.wmem len).toNat - 1) then
              pmulOut s.rmem (s.wmem x).toNat (s.wmem y).toNat (s.wmem len).toNat
                (i - (s.wmem dst).toNat)
            else s.rmem i
          rWritten := s.rWritten ∪
            (Finset.range (2 * (s.wmem len).toNat - 1)).image ((s.wmem dst).toNat + ·)
          pc := s.pc + 1
          cost := s.cost + M (s.wmem len).toNat }
      else s.stuck
  | .halt => { s with halted := true, cost := s.cost + 1 }

/-- One step of program `P` with multiplication cost `M`: a halted state stays put at no cost; an
invalid program counter is a stuck step; otherwise the current instruction is executed. -/
def step (M : ℕ → ℕ) (P : Program) (s : State R) : State R :=
  if s.halted then s
  else
    match P[s.pc]? with
    | none => s.stuck
    | some i => exec M s i

/-- The state after `k` steps of program `P` from `s`. -/
def run (M : ℕ → ℕ) (P : Program) (s : State R) : ℕ → State R
  | 0 => s
  | k + 1 => run M P (step M P s) k

/-- The initial state with word memory `w`, ring memory `r` and initial word-size record `mw`. -/
def mkState (w : ℕ → ℤ) (r : ℕ → R) (mw : ℕ) : State R where
  pc := 0
  wmem := w
  rmem := r
  halted := false
  cost := 0
  wWritten := ∅
  rWritten := ∅
  maxWord := mw

/-- The initial state whose word memory holds the list `wIn` from address `0` and whose ring memory
holds the list `rIn` from address `0`; all other cells are `0`. -/
def initState (wIn : List ℤ) (rIn : List R) : State R :=
  mkState (fun i => wIn.getD i 0) (fun i => rIn.getD i 0) ((wIn.map Int.natAbs).foldr max 0)

/-- Working space of a state: the number of distinct word addresses plus the number of distinct
ring addresses written so far. -/
def State.space (s : State R) : ℕ := s.wWritten.card + s.rWritten.card

/-- The run never wrote a word address below `nw` nor a ring address below `nr` (a read-only input
occupying word cells `0, …, nw − 1` and ring cells `0, …, nr − 1`). -/
def State.ReadOnly (s : State R) (nw nr : ℕ) : Prop :=
  (∀ a ∈ s.wWritten, nw ≤ a) ∧ (∀ a ∈ s.rWritten, nr ≤ a)

end CharPSComp


