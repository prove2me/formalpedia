-- Prove2me | Definitions.Def_ComplexityUnpred_Catalytic_Circuit
-- name    : ComplexityUnpred_Catalytic_Circuit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:01:53.928195+00:00
-- url     : https://prove2.me/theorems/177976a1-1eaf-48b8-9e02-1de7a8ec4edc
-- title:
--   Boolean circuits with AND, OR, NOT and THRESHOLD gates and their binary code (§2.2)
-- statement:
--   A **Boolean circuit** on $k$ inputs is a list of gates in topological order: wires $0,\dots,k-1$ carry the inputs, and gate number $g$ (counting from $0$) drives wire $k+g$ and reads only wires with smaller numbers. Each gate is an **AND**, **OR** (unbounded fan-in), **NOT** (fan-in exactly $1$) or **THRESHOLD** gate $\mathrm{Th}_t$ (unbounded fan-in, output $1$ iff at least $t$ of its inputs are $1$, with $t$ written in the gate). One wire is the output; the circuit computes the value of that wire. AND and OR gates of fan-in $0$ are the constants $1$ and $0$.
--
--   The **binary code** of a circuit is fixed as follows: a natural number $k$ is written by $\mathrm{enc}(k)$ = its binary digits (least significant first) each doubled, then $01$; a list is written as its length followed by its entries; a gate is written as its kind ($0,1,2$ for AND, OR, NOT; $3$ followed by $t$ for $\mathrm{Th}_t$) followed by the list of the wires it reads; a circuit is its list of gates followed by its output wire. The unary code of $k$ is $1^k0$. All these codes are prefix-free. For a well-formed circuit with $S$ gates including inputs, $W$ wire references and total threshold-label bit length $B$, the code has $O((S+W)\log(S+W+2)+B)$ bits. Thresholds above the fan-in may be replaced by fan-in plus one without changing the gate function, so standard circuit descriptions have polynomial-size codes.
--
--   This fixes the representation of the predictors of UNPRED and of the edge circuit of WeakExcess, which are given as circuits.
--
--   **Formalization Note** The paper says "Circuits use AND, OR, NOT, and THRESHOLD gates. AND, OR, and THRESHOLD gates have unbounded fan-in, and NOT gates have fan-in 1" and does not fix the thresholds or a code; reading THRESHOLD as $\mathrm{Th}_t$ with $t$ in the label is the standard one. Only single-output circuits are needed. `Circuit.WF k` is well-formedness on $k$ inputs; `Circuit.eval` evaluates on a `List Bool` of input bits (an argument outside the existing wires, excluded by `WF`, reads $0$).
-- source:
--   Agarwala, Dorfman, The Complexity of Unpredictability, arXiv:2611.05956v1, p. 18, §2.2 (Circuits)

import Mathlib

namespace ComplexityUnpred.Catalytic

/-! Agarwala, Dorfman, *The Complexity of Unpredictability*, arXiv:2611.05956v1, §2.2, p. 18
("Circuits"): "circuits use AND, OR, NOT, and THRESHOLD gates. AND, OR, and THRESHOLD gates have
unbounded fan-in, and NOT gates have fan-in 1."

A circuit on `k` inputs is a list of gates in topological order. Wires `0, …, k−1` are the
inputs; gate number `g` (0-based) drives wire `k + g` and reads only wires below it. A THRESHOLD
gate is `Th_t` (output `1` iff at least `t` of its inputs are `1`), with `t` in its label. The
circuits used here have one output wire.

Binary codes: `encNat` writes a natural number in binary (least significant bit first), every
bit doubled, followed by the end mark `01`; `encUnary` writes `k` as `1ᵏ0`; `encList` writes the
length of a list (with `encNat`) and then its entries. All three are prefix-free. -/

/-- The kinds of gates. `thr t` is the threshold gate `Th_t`. -/
inductive GateKind
  | and
  | or
  | not
  | thr (t : ℕ)

/-- A gate: its kind and the wires it reads (its fan-in is the length of `args`). -/
structure Gate where
  kind : GateKind
  args : List ℕ

/-- A single-output Boolean circuit: gates in topological order and the output wire. -/
structure Circuit where
  gates : List Gate
  out : ℕ

/-- The value of a gate on the values of its input wires. AND and OR of no inputs are the
constants `1` and `0`. -/
def GateKind.apply : GateKind → List Bool → Bool
  | .and, bs => bs.all id
  | .or, bs => bs.any id
  | .not, bs => !(bs.headD false)
  | .thr t, bs => decide (t ≤ bs.count true)

/-- Well-formedness of a circuit on `k` inputs: gate `g` reads only wires `< k + g` (so the
circuit is acyclic), NOT gates have fan-in exactly 1, and the output is an existing wire. -/
def Circuit.WF (c : Circuit) (k : ℕ) : Prop :=
  (∀ g : Fin c.gates.length, ∀ a ∈ (c.gates.get g).args, a < k + g.val) ∧
  (∀ g ∈ c.gates, g.kind = GateKind.not → g.args.length = 1) ∧
  c.out < k + c.gates.length

/-- The values of all wires of `c` on the input bits `x` (inputs first, then the gates). -/
def Circuit.wires (c : Circuit) (x : List Bool) : List Bool :=
  c.gates.foldl (fun w g => w ++ [g.kind.apply (g.args.map fun a => w.getD a false)]) x

/-- The output of `c` on the input bits `x`. -/
def Circuit.eval (c : Circuit) (x : List Bool) : Bool :=
  (c.wires x).getD c.out false

/-- Self-delimiting binary code of a natural number: bits of `k` (least significant first),
each doubled, then `01`. -/
def encNat (k : ℕ) : List Bool :=
  (Nat.bits k).flatMap (fun b => [b, b]) ++ [false, true]

/-- Unary code `1ᵏ0`. -/
def encUnary (k : ℕ) : List Bool :=
  List.replicate k true ++ [false]

/-- Code of a list: its length (`encNat`), then the codes of its entries. -/
def encList {α : Type} (f : α → List Bool) (l : List α) : List Bool :=
  encNat l.length ++ l.flatMap f

/-- Code of a gate kind: `0, 1, 2` for AND, OR, NOT; `3` followed by `t` for `Th_t`. -/
def GateKind.encode : GateKind → List Bool
  | .and => encNat 0
  | .or => encNat 1
  | .not => encNat 2
  | .thr t => encNat 3 ++ encNat t

/-- Code of a gate: its kind, then the list of the wires it reads. -/
def Gate.encode (g : Gate) : List Bool :=
  g.kind.encode ++ encList encNat g.args

/-- Code of a circuit: the list of its gates, then its output wire. -/
def Circuit.encode (c : Circuit) : List Bool :=
  encList Gate.encode c.gates ++ encNat c.out

end ComplexityUnpred.Catalytic


