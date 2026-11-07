-- Prove2me | Definitions.Def_QiOPoQ_Circ
-- name    : QiOPoQ_Circ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:00:24.978203+00:00
-- url     : https://prove2.me/theorems/afe4f578-30e2-4423-9b32-93b1d3f2555d
-- title:
--   Quantum circuits, their shape, and polynomial-size families
-- statement:
--   A circuit $C$ over a gate set has $n_{\mathrm{in}}$ input wires and $n_{\mathrm{anc}}$ ancilla wires, a sequence of gate occurrences (a gate placed on an ordered tuple of distinct wires) applied first to last, and a designated output register given by an ordered list of distinct wires; the remaining wires form the junk register. Its **shape** is
--
--   $$
--   \mathrm{shape}(C) = (s, n_{\mathrm{in}}, n_{\mathrm{anc}}, n_{\mathrm{out}}),
--   $$
--
--   where $s$ is the gate count. A family $\{C_\lambda\}$ is **polynomial-size** if the gate count and the width $n_{\mathrm{in}}+n_{\mathrm{anc}}$ are bounded by a polynomial in $\lambda$.
--
--   **Formalization Note** The input wires are numbered first, then the ancillas. Circuits are in deferred-measurement form, as on p.13.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), §3.1, p.13

import Mathlib
import Definitions.Def_QiOPoQ_GateSet

set_option autoImplicit false

namespace QiOPoQ

/-- **Quantum circuits (§3.1).** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage
and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), §3.1,
p.13: "we may regard such a circuit C as a unitary U_C acting on an input register “in” and an
ancilla register “anc” initialized to |0^{n_anc}⟩. A designated output register “out” is
retained and the remaining register “junk” is discarded."

A circuit over the gate set `G` has `nin` input wires `0, …, nin − 1` and `nanc` ancilla wires
`nin, …, nin + nanc − 1`; `gates` is the sequence of gate occurrences, each a gate `i` of `G`
placed on an ordered tuple of distinct wires (gate qubit `j` on wire `w j`), applied first to
last; `out` lists the designated output wires, in order (output bit `j` is wire `out[j]`); the
other wires form the junk register.

**Formalization Note.** The width is `nin + nanc`, which equals `nout + njunk` with
`nout = out.length`. Circuits are in deferred-measurement form (see `GateSet`). -/
structure Circ (G : GateSet) where
  /-- Number of input qubits `n_in`. -/
  nin : ℕ
  /-- Number of ancilla qubits `n_anc`, initialized to `|0⟩`. -/
  nanc : ℕ
  /-- The gate occurrences, first applied first. -/
  gates : List (Σ i : Fin G.k, Fin (G.arity i) ↪ Fin (nin + nanc))
  /-- The output register, in order. -/
  out : List (Fin (nin + nanc))
  out_nodup : out.Nodup

variable {G : GateSet}

/-- p.13: "shape(C) := (s, n_in, n_anc, n_out), where s is the gate count." -/
def shape (C : Circ G) : ℕ × ℕ × ℕ × ℕ := (C.gates.length, C.nin, C.nanc, C.out.length)

/-- p.13: "a family of circuits {C_λ}λ∈N indexed by a security parameter λ is polynomial-sized
if there is a polynomial poly such that the gate count and width of C_λ are bounded by
poly(λ)." -/
def PolySize (Cf : ℕ → Circ G) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, (Cf n).gates.length ≤ p.eval n ∧ (Cf n).nin + (Cf n).nanc ≤ p.eval n

end QiOPoQ


