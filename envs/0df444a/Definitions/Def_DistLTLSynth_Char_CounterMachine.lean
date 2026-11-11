-- Prove2me | Definitions.Def_DistLTLSynth_Char_CounterMachine
-- name    : DistLTLSynth_Char_CounterMachine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:14:55.940745+00:00
-- url     : https://prove2.me/theorems/8202be88-c7de-405e-be08-94e7dbb32289
-- title:
--   Deterministic n-counter machines (Q, Δ, q_init, F), halting from the zero configuration, and finite codes of 2-counter machines
-- statement:
--   An **$n$-counter machine** $M=(Q,\Delta,q_{\mathrm{init}},F)$ has finitely many states $Q$, an initial state, halting states $F\subseteq Q$ and counters $c_1,\dots,c_n$; $\Delta$ assigns to each $q\in Q\setminus F$ either "increment$(c_i)$; goto $q'$" or "if $c_i=0$ then goto $q'$ else decrement$(c_i)$; goto $q''$". Configurations $(q,x_1,\dots,x_n)\in Q\times\mathbb N^n$ evolve accordingly, and $M$ **halts** if its run from $(q_{\mathrm{init}},0,\dots,0)$ reaches a state in $F$.
--
--   A **code** $(s,q_0,F,\Delta)$ describes the machine with states $\{0,\dots,s\}$, initial state $q_0 \bmod (s+1)$, halting states the listed numbers, and instruction $\Delta[q]=(\text{isDec},i,a,b)$ (counter index $i \bmod k$, targets mod $s+1$, missing entries read as an increment of counter $0$ to state $0$).
--
--   **Formalization Note.** $\Delta$ is given on all of $Q$; its values on $F$ are never used before the run reaches $F$, which is all that halting asks.
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), p. 8 (PDF 9), §3.2

import Mathlib

namespace DistLTLSynth.Char

/-- An instruction of an `n`-counter machine (§3.2, p. 8): `inc i q'` is
"increment(cᵢ); goto q'"; `dec i q' q''` is "if cᵢ = 0 then goto q' else decrement(cᵢ);
goto q''". -/
inductive Instr (Q : Type) (n : ℕ) : Type where
  | inc (i : Fin n) (q' : Q) : Instr Q n
  | dec (i : Fin n) (q' q'' : Q) : Instr Q n

/-- A deterministic `n`-counter machine `M = (Q, Δ, q_init, F)` with counters `c₁, …, cₙ`
(§3.2, p. 8). `Δ` is given on all of `Q`; only its values on `Q \ F` are used by a run
before it reaches `F`. -/
structure CounterMachine (Q : Type) (n : ℕ) : Type where
  init : Q
  halting : Set Q
  instr : Q → Instr Q n

/-- A configuration `(q, x₁, …, xₙ) ∈ Q × ℕⁿ`. -/
structure Config (Q : Type) (n : ℕ) : Type where
  state : Q
  counters : Fin n → ℕ

/-- One step of the machine. -/
def CounterMachine.step {Q : Type} {n : ℕ} (M : CounterMachine Q n) (c : Config Q n) :
    Config Q n :=
  match M.instr c.state with
  | .inc i q' => ⟨q', Function.update c.counters i (c.counters i + 1)⟩
  | .dec i q' q'' =>
      if c.counters i = 0 then ⟨q', c.counters⟩
      else ⟨q'', Function.update c.counters i (c.counters i - 1)⟩

/-- The run from `(q_init, 0, …, 0)`. -/
def CounterMachine.run {Q : Type} {n : ℕ} (M : CounterMachine Q n) : ℕ → Config Q n
  | 0 => ⟨M.init, fun _ => 0⟩
  | t + 1 => M.step (M.run t)

/-- `M` halts: its run from `(q_init, 0, …, 0)` reaches a state of `F`. -/
def CounterMachine.Halts {Q : Type} {n : ℕ} (M : CounterMachine Q n) : Prop :=
  ∃ t, (M.run t).state ∈ M.halting

/-- A finite description of a counter machine, used as the input of algorithms:
`(s, q₀, F, Δ)` has states `Fin (s + 1)`, initial state `q₀ mod (s + 1)`, halting states the
`q` with `q ∈ F`, and instruction `Δ[q] = (isDec, i, a, b)` (missing entries read as
`(false, 0, 0, 0)`; state numbers are read modulo `s + 1`). -/
abbrev CMCode : Type := ℕ × ℕ × List ℕ × List (Bool × ℕ × ℕ × ℕ)

/-- The `k`-counter machine (`k ≥ 1`) described by a code; counter indices are read
modulo `k`. -/
def CMCode.toMachine (c : CMCode) (k : ℕ) (hk : 0 < k) : CounterMachine (Fin (c.1 + 1)) k where
  init := ⟨c.2.1 % (c.1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  halting := {q | q.val ∈ c.2.2.1}
  instr q :=
    match c.2.2.2.getD q.val (false, 0, 0, 0) with
    | (false, i, a, _) =>
        .inc ⟨i % k, Nat.mod_lt _ hk⟩ ⟨a % (c.1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
    | (true, i, a, b) =>
        .dec ⟨i % k, Nat.mod_lt _ hk⟩ ⟨a % (c.1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
          ⟨b % (c.1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

end DistLTLSynth.Char


