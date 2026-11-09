-- Prove2me | Definitions.Def_AnonymousDirectedCounting_Exact_LocalCost
-- name    : AnonymousDirectedCounting_Exact_LocalCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:36.447267+00:00
-- url     : https://prove2.me/theorems/b32311c5-9ff1-4b49-a019-b9889983437a
-- title:
--   One-tape binary machines and the polynomial local-computation clause
-- statement:
--   A binary machine is a deterministic one-tape Turing machine with a finite state set, tape alphabet $\{\text{blank},0,1\}$, and a transition table whose missing entries halt. A local input encodes $\ell$, the old state, the outdegree, and the compressed inbox, which lists each distinct received state once with its positive multiplicity in binary, in any order. A local output encodes the new state and the optional output.
--
--   A protocol has a polynomial binary implementation when there are one machine $M$ and one injective binary encoding of states such that $M$ computes the update and output in every executed round of every admissible network, on every listing of the inbox, and such that for every polynomial $p$ with natural coefficients there are constants $C>0$ and $k$ for which, on every admissible network with at most $2^{p(n)}$ arcs per round, every such computation takes at most $C(1+n)^k$ steps.
--
--   The machine is chosen before $p$, and $C,k$ before $n$, $\ell$, the network, the agent and the round. Neither $n$ nor $p$ is an input.
--
--   **Formalization Note** The source names no machine model and no exponent, and none is invented. Time on a one-tape machine is polynomially related to time on the usual models. Each round is bounded separately, as the source's "all local computations" reads; total work follows as at most $2n-1$ rounds occur.
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), Section 2, printed p. 3 (PDF p. 5); Theorem 1 and its proof, printed pp. 8–9 (PDF pp. 10–11)

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_NetworkModel

set_option autoImplicit false

namespace AnonymousDirectedCounting.Exact

open scoped Classical

noncomputable section

/-- A head move of a one-tape machine. -/
inductive HeadMove
  | left
  | stay
  | right

/-- A deterministic one-tape Turing machine over the alphabet `{blank, 0, 1}`: a finite state set
and a transition table; a `none` transition halts. This is the cost model of the local-computation
clause; every standard machine model is polynomially equivalent to it. -/
structure BinaryMachine where
  Q : Type
  [finiteQ : Finite Q]
  start : Q
  δ : Q → Option Bool → Option (Q × Option Bool × HeadMove)

/-- A configuration of a machine. -/
structure MachineConfig (M : BinaryMachine) where
  state : M.Q
  tape : ℤ → Option Bool
  head : ℤ

/-- One machine step; `none` when the machine halts. -/
def machineStep (M : BinaryMachine) (c : MachineConfig M) : Option (MachineConfig M) :=
  (M.δ c.state (c.tape c.head)).map fun r =>
    { state := r.1
      tape := Function.update c.tape c.head r.2.1
      head :=
        match r.2.2 with
        | HeadMove.left => c.head - 1
        | HeadMove.stay => c.head
        | HeadMove.right => c.head + 1 }

/-- `T` steps, if the machine has not halted before them. -/
def machineSteps (M : BinaryMachine) : ℕ → MachineConfig M → Option (MachineConfig M)
  | 0, c => some c
  | T + 1, c => (machineStep M c).bind (machineSteps M T)

/-- A word written from cell 0, all other cells blank. -/
def tapeOf (w : List Bool) : ℤ → Option Bool := fun i =>
  if 0 ≤ i then w[i.toNat]? else none

/-- On input `w` the machine halts after exactly `T` steps with exactly `out` on its tape. -/
def MachineRuns (M : BinaryMachine) (w : List Bool) (T : ℕ) (out : List Bool) : Prop :=
  ∃ c : MachineConfig M,
    machineSteps M T { state := M.start, tape := tapeOf w, head := 0 } = some c ∧
      machineStep M c = none ∧ c.tape = tapeOf out

/-- Self-delimiting bit string: each bit `b` becomes `1 b`; `0` terminates. -/
def encodeBits (w : List Bool) : List Bool :=
  w.flatMap (fun b => [true, b]) ++ [false]

/-- A natural number in binary. -/
def encodeNat (a : ℕ) : List Bool :=
  encodeBits (Nat.bits a)

/-- The source's input convention (printed p. 3, PDF p. 5): `l` lists each distinct received
state once, in any order, with its positive multiplicity. -/
def IsCompressedInbox (msgs : Multiset (List Bool)) (l : List (List Bool × ℕ)) : Prop :=
  (l.map Prod.fst).Nodup ∧ (∀ p ∈ l, 0 < p.2) ∧
    (l.map (fun p => Multiset.replicate p.2 p.1)).sum = msgs

/-- A local input: leader count, own old state, outdegree, and compressed inbox, all in binary. -/
def localInput (ell : ℕ) (s : List Bool) (d : ℕ) (l : List (List Bool × ℕ)) : List Bool :=
  encodeNat ell ++ encodeBits s ++ encodeNat d ++ encodeNat l.length ++
    l.flatMap (fun p => encodeBits p.1 ++ encodeNat p.2)

/-- A local output: new state, then `0` for no output or `1` and the number. -/
def localOutput (s : List Bool) (o : Option ℕ) : List Bool :=
  encodeBits s ++
    match o with
    | none => [false]
    | some a => true :: encodeNat a

/-- `M` computes, within `T` steps on every listing of the compressed inbox, the update and output
of `A` at round `t + 1` of agent `x`, states being written through `enc`. -/
def MachineRealizesRound {S : Type} (M : BinaryMachine) (enc : S → List Bool) (A : Protocol S)
    {n : ℕ} (G : NetworkModel n) (t : ℕ) (x : Fin n) (T : ℕ) : Prop :=
  let old := execution A G t
  let msgs := received G (t + 1) old x
  let d := outdegree G (t + 1) x
  let s' := A.update G.leaders.card (old x).1 msgs d
  ∀ l : List (List Bool × ℕ), IsCompressedInbox (msgs.map enc) l →
    ∃ T' : ℕ, T' ≤ T ∧ MachineRuns M (localInput G.leaders.card (enc (old x).1) d l) T'
      (localOutput (enc s') (A.output s' G.leaders.card))

/-- The local-computation clause: one machine and one injective binary state encoding realize `A`
in every executed round of every admissible network; and for every polynomial `p`, with constants
chosen before the network, every network with at most `2 ^ p(n)` arcs per round has every local
computation within `C (1 + n) ^ k` steps. Neither `p` nor `n` is an input of the machine. -/
def HasPolynomialBinaryImplementation {S : Type} (A : Protocol S) : Prop :=
  ∃ (M : BinaryMachine) (enc : S → List Bool), Function.Injective enc ∧
    (∀ (n : ℕ) (G : NetworkModel n), Admissible G → ∀ (t : ℕ) (x : Fin n),
      (execution A G t x).2 = none → ∃ T : ℕ, MachineRealizesRound M enc A G t x T) ∧
    ∀ p : Polynomial ℕ, ∃ C k : ℕ, 0 < C ∧
      ∀ (n : ℕ) (G : NetworkModel n), Admissible G →
        ArcsPerRoundAtMost G (2 ^ p.eval n) → ∀ (t : ℕ) (x : Fin n),
          (execution A G t x).2 = none →
            MachineRealizesRound M enc A G t x (C * (1 + n) ^ k)

end

end AnonymousDirectedCounting.Exact


