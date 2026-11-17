-- Prove2me | Definitions.Def_QuadraticRE_Supplement_Circuit
-- name    : QuadraticRE_Supplement_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:50:51.65523+00:00
-- url     : https://prove2.me/theorems/e22bec86-b5fa-4a68-8e61-14bd7a361715
-- title:
--   Boolean circuits of fan-in at most two: size, depth, evaluation and bit encoding
-- statement:
--   A **Boolean circuit of fan-in at most two** computing $f:\{0,1\}^N\to\{0,1\}^b$ consists of $N$ input variables, a list of non-input gates in topological order and $b$ designated output wires. Wires $0,\dots,N-1$ carry the input bits and wire $N+k$ carries the output of gate $k$. Each gate is either a constant or an arbitrary Boolean function (given by its truth table) of two wires that precede it; a fan-in-one gate reads the same wire twice.
--
--   1. The **size** of the representation is $\sigma=\#\{\text{non-input gates}\}+N+b$, exactly as in the preliminaries of the paper.
--   2. The **depth** is the length of a longest path from an input to an output wire: inputs and constants have depth $0$, a two-input gate has depth one more than its deeper input.
--   3. The circuit's **bit encoding** lists $N$, the number of gates, $b$, every gate and the output wires, with every number written in unary, so its length is polynomially related to $\sigma$.
--
--   These are the circuit representations of Theorem 4.13 and of the uniform $\mathrm{NC}^1$ hypothesis of Theorem 5.5.
--
--   **Formalization Note** The page fixes no gate basis, so every Boolean function of at most two inputs is a gate; this only widens the classes of circuits quantified over. Acyclicity is the topological order: gate $k$ reads only wires $<N+k$.
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), §3.2, "Representations and size", p.14

import Mathlib
import Definitions.Def_QuadraticRE_PolyTimeFn

namespace QuadraticRE.Supplement

open QuadraticRE

/-- A non-input gate of a Boolean circuit of fan-in at most two (Orsini, Patra, *From Degree Three to
Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), §3.2, "Representations and size",
p.14): either a constant (fan-in zero) or an arbitrary Boolean function of two earlier wires, given
by its truth table `t : Fin 16` (bit `2·u + v` of `t` is the value on inputs `(u, v)`).

**Formalization Note.** The page fixes no gate basis, so every Boolean function of at most two inputs
is allowed; a fan-in-one gate is an `op` whose two wires coincide (or whose table ignores one input).
Wires are numbered: `0, …, N − 1` are the input variables, `N + k` is the output of gate `k`. -/
inductive CGate where
  | const (c : Bool) : CGate
  | op (t : Fin 16) (a b : ℕ) : CGate

/-- A gate only reads wires that exist before it: inputs and earlier gates. -/
def CGate.WF (w : ℕ) : CGate → Prop
  | .const _ => True
  | .op _ a b => a < w ∧ b < w

/-- A Boolean circuit of fan-in at most two, p.14, computing `f : {0,1}^N → {0,1}^b`: `N` input
variables, a list of gates in topological order, and `b` designated output wires (`outs`, in order;
an output wire may be an input variable or any gate).

**Formalization Note.** Acyclicity is the topological order: gate `k` reads only wires `< N + k`. -/
structure Circuit where
  N : ℕ
  gates : List CGate
  outs : List ℕ
  wf : ∀ (k : ℕ) (hk : k < gates.length), (gates[k]).WF (N + k)
  outs_lt : ∀ o ∈ outs, o < N + gates.length

/-- The output length `b`. -/
def Circuit.b (C : Circuit) : ℕ := C.outs.length

/-- The total size of a circuit representation, p.14: "the number of non-input gates plus `N + b`". -/
def Circuit.size (C : Circuit) : ℕ := C.gates.length + C.N + C.b

/-- The value of one gate, given the values of all earlier wires. -/
def CGate.val (vals : List F2) : CGate → F2
  | .const c => if c then 1 else 0
  | .op t a b => if Nat.testBit t.val (2 * (vals.getD a 0).val + (vals.getD b 0).val) then 1 else 0

/-- The values of all wires on input `x`: the input bits, then the gates in order. -/
def Circuit.values (C : Circuit) (x : Fin C.N → F2) : List F2 :=
  C.gates.foldl (fun vals g => vals ++ [g.val vals]) (List.ofFn x)

/-- The function `f : {0,1}^N → {0,1}^b` computed by the circuit: output `i` is the value of the wire
`outs[i]`. -/
def Circuit.eval (C : Circuit) (x : Fin C.N → F2) (i : Fin C.b) : F2 :=
  (C.values x).getD (C.outs.get i) 0

/-- The depth of one gate given the depths of the earlier wires: a constant has depth `0` (no input
reaches it), a two-input gate is one more than its deeper input. -/
def CGate.depth (ds : List ℕ) : CGate → ℕ
  | .const _ => 0
  | .op _ a b => 1 + max (ds.getD a 0) (ds.getD b 0)

/-- The depths of all wires: inputs have depth `0`. -/
def Circuit.wireDepths (C : Circuit) : List ℕ :=
  C.gates.foldl (fun ds g => ds ++ [g.depth ds]) (List.replicate C.N 0)

/-- The depth of a circuit: the length of a longest path from an input to an output wire (the maximum
wire depth over the output wires, `0` if there are none). -/
def Circuit.depth (C : Circuit) : ℕ :=
  (C.outs.map fun o => C.wireDepths.getD o 0).foldr max 0

/-- The tokens of a gate: a constant is `[0, c]`, a two-input gate `[1, t, a, b]`. -/
def CGate.tokens : CGate → List ℕ
  | .const c => [0, if c then 1 else 0]
  | .op t a b => [1, t.val, a, b]

/-- The tokens of a circuit: `N`, the number of gates, `b`, the gates, the output wires. -/
def circuitTokens (C : Circuit) : List ℕ :=
  [C.N, C.gates.length, C.b] ++ C.gates.flatMap CGate.tokens ++ C.outs

/-- The bit encoding of a circuit, every number in unary as in the base mission's `encTokens`, so its
length is polynomially related to the circuit size. -/
def encCircuit (C : Circuit) : List Bool := encTokens (circuitTokens C)

end QuadraticRE.Supplement


