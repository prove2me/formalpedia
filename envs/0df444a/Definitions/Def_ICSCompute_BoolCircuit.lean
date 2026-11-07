-- Prove2me | Definitions.Def_ICSCompute_BoolCircuit
-- name    : ICSCompute_BoolCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:45:33.765977+00:00
-- url     : https://prove2.me/theorems/7642e854-3237-4647-9a86-18aae586474b
-- title:
--   Classical Boolean circuits and the outmap they compute
-- statement:
--   A **Boolean circuit** with $n_{\mathrm{in}}$ inputs is a list of gates, each an AND or OR of two earlier wires or a NOT of one, together with a list of output wires. Wires $0,\dots,n_{\mathrm{in}}-1$ carry the input bits and gate $k$ computes wire $n_{\mathrm{in}}+k$. A circuit **computes** $s:\{0,1\}^n\to\{0,1\}^n$ if it has $n$ inputs and outputs $s(x)$ on every input $x$.
--
--   In the USO problem the outmap $s$ is given by such a circuit, and running times are measured in its description length.
--
--   **Formalization Note** The paper fixes no basis; fan-in-two AND, OR and NOT is a finite complete basis, polynomially equivalent to any other. A reference to a wire not yet computed reads $0$, so every syntax tree denotes a function and no well-formedness side condition is needed.
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), Definition 6.1, p.31 (PDF p.33)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace ICSCompute

open QAlgorithms

/-- A gate of a classical Boolean circuit: `AND`, `OR` of two wires or `NOT` of one wire, wires
referred to by their index. -/
inductive BGate where
  | and (i j : ℕ)
  | or (i j : ℕ)
  | not (i : ℕ)

/-- **Classical Boolean circuit** (Shmueli, *What Can Be Computed with Indefinite Causal
Structure?*, arXiv:2610.40573, version of 2026-11-03, sha256 d3e36399…b606, Definition 6.1,
p.31 (PDF p.33): "the input is a classical Boolean circuit computing an outmap s").

Wires `0, …, nIn − 1` carry the input bits; gate `k` of `gates` computes wire `nIn + k` from
wires it names; the circuit's output is the list of the wires named in `outs`.

**Formalization Note** The paper fixes no basis; fan-in-two `AND`, `OR` and `NOT` is a finite
complete basis, polynomially equivalent to any other. Wires are named by natural numbers; a
reference to a wire that does not exist yet reads `false` (see `BoolCircuit.wires`), so every
syntax tree denotes a function and no well-formedness side condition is needed. -/
structure BoolCircuit where
  /-- The number of input wires. -/
  nIn : ℕ
  /-- The gates, in evaluation order. -/
  gates : List BGate
  /-- The output wires, in order. -/
  outs : List ℕ

/-- The value of one gate given the values `w` of the wires computed so far. -/
def BGate.eval (w : List Bool) : BGate → Bool
  | .and i j => w.getD i false && w.getD j false
  | .or i j => w.getD i false || w.getD j false
  | .not i => !w.getD i false

/-- The values of all wires of `c` on the input `inp`: the input bits, then the gates in order. -/
def BoolCircuit.wires (c : BoolCircuit) (inp : List Bool) : List Bool :=
  c.gates.foldl (fun w g => w ++ [g.eval w]) inp

/-- The output of `c` on the input `inp`. -/
def BoolCircuit.eval (c : BoolCircuit) (inp : List Bool) : List Bool :=
  c.outs.map fun o => (c.wires inp).getD o false

/-- `c` **computes** `s : {0,1}ⁿ → {0,1}ⁿ` (Definition 6.1, p.31): `c` has `n` input wires and on
every `x ∈ {0,1}ⁿ` its output is `s(x)` (bit `i` of `x` on input wire `i`). -/
def BoolCircuit.Computes {n : ℕ} (c : BoolCircuit) (s : Qubits n → Qubits n) : Prop :=
  c.nIn = n ∧ ∀ x : Qubits n, c.eval (List.ofFn x) = List.ofFn (s x)

end ICSCompute


