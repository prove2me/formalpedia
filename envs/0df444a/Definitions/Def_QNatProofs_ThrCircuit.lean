-- Prove2me | Definitions.Def_QNatProofs_ThrCircuit
-- name    : QNatProofs_ThrCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:02:17.701851+00:00
-- url     : https://prove2.me/theorems/627b9b9e-b36c-4080-b841-62cc54cfa361
-- title:
--   Threshold circuits and threshold-circuit computability of a keyed family
-- statement:
--   A **threshold circuit** with $n$ inputs and $R$ outputs is a list of gates. Gate $i$ reads a list of literals, each an input or an earlier gate, possibly negated (a literal may repeat), and outputs $1$ iff at least $t_i$ of them are $1$. Each output is a literal over the inputs and gates. Its **size** is the number of gates plus the total fan-in, and its **depth** is the length of the longest path from an input to an output.
--
--   A keyed family $\mathcal G$ is **computable by polynomial-size depth-$d$ threshold circuits** if there is a polynomial $p$ such that for every $m$ and every key $k\in\mathcal K_m$ some threshold circuit of depth at most $d$ and size at most $p(m)$ computes $x\mapsto G_{m,k}(x)$.
--
--   These are the TC$^0$ circuits of the main theorem's hypothesis ("polynomial-size depth-$d_F$ threshold circuits", p.33).
--
--   **Formalization Note** Repetition gives literals positive integer weights, so these are threshold circuits with polynomially bounded weights, the standard TC$^0$. The circuit may depend on the key; a circuit that takes the key as an extra input gives such circuits by fixing the key bits to constants.
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Theorem 4.7, p.33; Corollary 4.6.2, p.33; p.3

import Mathlib
import Definitions.Def_QNatProofs_KeyedFam

set_option autoImplicit false

namespace QNatProofs

open Polynomial

/-- A **threshold circuit** with `n` inputs and `R` outputs (the "polynomial-size depth-`d`
threshold circuits" / TC⁰ circuits of Li, Parham, arXiv:2610.06826 (held copy sha256 b604fa11…),
p.3, p.33, Theorem 4.7). Gate `i` reads a list of literals, each an input or an earlier gate,
possibly negated (the `Bool` is `true` for a negated literal; a literal may be repeated), and
outputs `1` iff at least `t_i` of them are `1`. Each output is a literal over the inputs and the
gates.

**Formalization Note** Repeating a literal gives it a positive integer weight, so these are the
threshold circuits with polynomially bounded weights (the standard definition of TC⁰). -/
structure ThrCircuit (n R : ℕ) where
  /-- The number of gates. -/
  numGates : ℕ
  /-- The input literals of gate `i` (sources: an input or a gate `< i`). -/
  ins : (i : Fin numGates) → List ((Fin n ⊕ Fin i.val) × Bool)
  /-- The threshold of gate `i`. -/
  thr : Fin numGates → ℕ
  /-- The output literals. -/
  out : Fin R → (Fin n ⊕ Fin numGates) × Bool

/-- The value of gate `i` on input `x`. -/
def ThrCircuit.gateVal {n R : ℕ} (Φ : ThrCircuit n R) (x : Fin n → Bool) :
    (i : ℕ) → i < Φ.numGates → Bool
  | i, h =>
    Φ.thr ⟨i, h⟩ ≤ ((Φ.ins ⟨i, h⟩).filter fun l =>
      Bool.xor l.2 (match l.1 with
        | Sum.inl j => x j
        | Sum.inr j => Φ.gateVal x j.val (lt_trans j.isLt h))).length
  termination_by i => i
  decreasing_by exact j.isLt

/-- The output `Φ(x) ∈ {0,1}^R` of the circuit. -/
def ThrCircuit.eval {n R : ℕ} (Φ : ThrCircuit n R) (x : Fin n → Bool) : Fin R → Bool :=
  fun r => Bool.xor (Φ.out r).2 (match (Φ.out r).1 with
    | Sum.inl j => x j
    | Sum.inr i => Φ.gateVal x i.val i.isLt)

/-- The depth of gate `i`: one more than the largest depth of a gate it reads (inputs have depth
`0`). -/
def ThrCircuit.gateDepth {n R : ℕ} (Φ : ThrCircuit n R) : (i : ℕ) → i < Φ.numGates → ℕ
  | i, h => 1 + ((Φ.ins ⟨i, h⟩).map fun l => match l.1 with
      | Sum.inl _ => 0
      | Sum.inr j => Φ.gateDepth j.val (lt_trans j.isLt h)).foldr max 0
  termination_by i => i
  decreasing_by exact j.isLt

/-- The **depth** of the circuit: the largest depth of a gate an output reads (`0` if every output
is an input literal). -/
def ThrCircuit.depth {n R : ℕ} (Φ : ThrCircuit n R) : ℕ :=
  ((List.finRange R).map fun r => match (Φ.out r).1 with
    | Sum.inl _ => 0
    | Sum.inr i => Φ.gateDepth i.val i.isLt).foldr max 0

/-- The **size** of the circuit: the number of gates plus the total fan-in (number of wires). -/
def ThrCircuit.size {n R : ℕ} (Φ : ThrCircuit n R) : ℕ :=
  Φ.numGates + ∑ i : Fin Φ.numGates, (Φ.ins i).length

/-- **`𝒢` is computable by polynomial-size depth-`d` threshold circuits** (Li, Parham,
arXiv:2610.06826 (held copy sha256 b604fa11…), Theorem 4.7, p.33; Corollary 4.6.2, p.33): there is
a polynomial `p` such that for every `m` and every key `k ∈ 𝒦_m` some threshold circuit of depth at
most `d` and size at most `p(m)` computes `x ↦ G_{m,k}(x)`.

**Formalization Note** The circuit may depend on the key. A circuit that takes the key as an extra
input gives such circuits by fixing the key bits to constants. -/
def KeyedFam.ThresholdComputable (G : KeyedFam) (d : ℕ) : Prop :=
  ∃ p : ℕ[X], ∀ (m : ℕ) (k : G.K m), ∃ Φ : ThrCircuit m m,
    Φ.depth ≤ d ∧ Φ.size ≤ p.eval m ∧ ∀ x, Φ.eval x = G.G m k x

end QNatProofs


