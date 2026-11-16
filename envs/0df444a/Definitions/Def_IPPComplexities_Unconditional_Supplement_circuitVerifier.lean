-- Prove2me | Definitions.Def_IPPComplexities_Unconditional_Supplement_circuitVerifier
-- name    : IPPComplexities_Unconditional_Supplement_circuitVerifier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:23:26.290196+00:00
-- url     : https://prove2.me/theorems/31559483-cde7-400e-84b9-72d09ec5d8db
-- title:
--   Verification strategies implemented by probabilistic circuits
-- statement:
--   A **probabilistic circuit for a verification strategy** on $n$-bit inputs is a Boolean circuit $C$ (constants, $\neg$, $\wedge$, $\vee$, size counting input wires and gates, as in the published circuit model) together with two numbers, the randomness $R$ and the width $W$. Its input wires are a random pad $\rho\in\{0,1\}^R$ followed by $2W$ bits encoding the **view** so far: $W$ value slots and $W$ validity-mask bits. The view is the ordered list of every bit the verifier has seen or produced: oracle answers, bits it sent and bits it received. The circuit is **well formed** if the Boolean circuit is well formed and has exactly $R+2W$ input wires. Its size is that of the Boolean circuit, so the random and view inputs are charged.
--
--   The output wires encode the next action by a fixed code: tag $00$ followed by $b$ halts with verdict $b$; tag $01$ followed by $b$ sends $b$ to the prover; tag $10$ receives a bit from the prover; tag $11$ followed by a binary number $i$ queries position $i$ of the input, and an out-of-range $i$ or a malformed output rejects.
--
--   The **verifier implemented by $C$** draws $\rho$ uniformly from $\{0,1\}^R$ once and keeps it for the whole run (private coins persist). It then repeatedly evaluates $C$ on $\rho$ and the current view and performs the decoded action. Messages strictly alternate: the verifier speaks when an even number of bits has been exchanged and the prover when an odd number has; an action violating this schedule is a rejecting halt. After $W+1$ evaluations the verifier rejects, so the circuit is only consulted on views of length at most $W$.
--
--   This is the notion "a verification strategy that can be implemented by a family of probabilistic circuits" of Theorem 3.2: the induced verifier is an ordinary verifier of the published interaction model, so its validity and its query and communication costs are those of that model.
--
--   **Formalization Note** The induced plan is the unrolling of the circuit with the pad fixed. That every unrolled plan respects the alternating schedule is proved in the file (`unroll_compatible`), not assumed. The schedule is public and fixed, so it carries no hidden nonuniform information.
-- source:
--   Noga Amit, Oded Goldreich, STOC 2027 submission #297 (October 2026), p. 9, Theorem 3.2 (PDF p. 11); computational complexity "its size as a circuit otherwise", p. 6, §2 (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/297.pdf

import Definitions.Def_IPPComplexities_Unconditional_interaction
import Definitions.Def_PPADSIS_SubexpSIS_Circuit

namespace IPPComplexities.Unconditional.Supplement

open PPADSIS.SubexpSIS

/-- One move of a verifier: halt with a verdict, query an input position,
send a bit to the prover, or receive a bit from the prover. -/
inductive Action (n : ℕ) where
  | halt : Bool → Action n
  | query : Fin n → Action n
  | send : Bool → Action n
  | receive : Action n

/-- Little-endian binary value of a bit list (the first bit is the least significant). -/
def binValue : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * binValue bs

/-- Fixed decoding of a circuit's output wires into an action. Tag `00 b`: halt with
verdict `b`; tag `01 b`: send `b`; tag `10`: receive; tag `11` followed by a binary
index: query that position. An out-of-range index or a malformed output rejects. -/
def decodeAction (n : ℕ) : List Bool → Action n
  | false :: false :: b :: _ => .halt b
  | false :: true :: b :: _ => .send b
  | true :: false :: _ => .receive
  | true :: true :: idx =>
      if h : binValue idx < n then .query ⟨binValue idx, h⟩ else .halt false
  | _ => .halt false

/-- The view so far, padded to `W` slots: the `W` value bits (missing slots are
`false`) followed by the `W` validity-mask bits (`true` exactly on the occupied slots). -/
def encodeView (W : ℕ) (view : List Bool) : List Bool :=
  List.ofFn (fun i : Fin W => view.getD i.val false) ++
    List.ofFn (fun i : Fin W => decide (i.val < view.length))

/-- A probabilistic circuit for a verification strategy: a Boolean circuit whose input
wires are `coins` random bits followed by the `2 * width` bits of `encodeView width`. -/
structure ProbCircuit where
  circuit : Circuit
  coins : ℕ
  width : ℕ

/-- Well formed: the underlying circuit is well formed and has exactly the input wires
for the random pad and the padded view. -/
def ProbCircuit.WF (C : ProbCircuit) : Prop :=
  C.circuit.WF ∧ C.circuit.nIn = C.coins + 2 * C.width

/-- Size of a probabilistic circuit: the size of its Boolean circuit, which counts
every input wire (random bits and view bits) as well as every gate. -/
def ProbCircuit.size (C : ProbCircuit) : ℕ := C.circuit.size

/-- Public message schedule of a circuit verifier: strict alternation, the verifier
speaking at even transcript lengths and the prover at odd ones. -/
def alternatingTurn : Turn := fun t => t.length % 2 == 0

/-- The deterministic plan obtained by running the circuit with a FIXED random pad
`ρ` throughout. `view` records every bit seen or produced so far (oracle answers, sent
bits and received bits, in order); `t` is the public transcript. Each step evaluates the
circuit on `ρ ++ encodeView W view`. An action that violates the alternating schedule
is a rejecting halt; running out of fuel rejects. -/
def unroll (n : ℕ) (C : ProbCircuit) (ρ : List Bool) :
    ℕ → List Bool → List Bool → Plan n
  | 0, _, _ => .halt false
  | fuel + 1, view, t =>
      match decodeAction n (C.circuit.eval (ρ ++ encodeView C.width view)) with
      | .halt b => .halt b
      | .query i => .query i (unroll n C ρ fuel (view ++ [false]) t)
          (unroll n C ρ fuel (view ++ [true]) t)
      | .send b => if alternatingTurn t then
          .send b (unroll n C ρ fuel (view ++ [b]) (t ++ [b])) else .halt false
      | .receive => if alternatingTurn t then .halt false else
          .receive (unroll n C ρ fuel (view ++ [false]) (t ++ [false]))
            (unroll n C ρ fuel (view ++ [true]) (t ++ [true]))

theorem unroll_compatible (n : ℕ) (C : ProbCircuit) (ρ : List Bool) :
    ∀ (fuel : ℕ) (view t : List Bool),
      compatible alternatingTurn (unroll n C ρ fuel view t) t = true := by
  intro fuel
  induction fuel with
  | zero => intro view t; simp [unroll, compatible]
  | succ k ih =>
    intro view t
    simp only [unroll]
    split
    · simp [compatible]
    · simp [compatible, ih]
    · split
      · simp_all [compatible]
      · simp [compatible]
    · split
      · simp [compatible]
      · simp_all [compatible]

/-- The verifier implemented by a probabilistic circuit: a uniformly random pad
`ρ ∈ {0,1}^coins` is drawn once and kept for the whole run (private coins persist),
and the plan is the unrolling of the circuit with that pad, with fuel `width + 1`
(so the circuit is evaluated only on views of length at most `width`). -/
noncomputable def circuitVerifier (n : ℕ) (C : ProbCircuit) : Verifier n where
  turn := alternatingTurn
  law := (PMF.uniformOfFintype (Fin C.coins → Bool)).map fun ρ =>
    ⟨unroll n C (List.ofFn ρ) (C.width + 1) [] [],
      unroll_compatible n C (List.ofFn ρ) (C.width + 1) [] []⟩

end IPPComplexities.Unconditional.Supplement


