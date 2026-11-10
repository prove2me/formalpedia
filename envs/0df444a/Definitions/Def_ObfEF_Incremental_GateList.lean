-- Prove2me | Definitions.Def_ObfEF_Incremental_GateList
-- name    : ObfEF_Incremental_GateList
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:55:21.156085+00:00
-- url     : https://prove2.me/theorems/94abfdd5-4abb-44ee-8017-a1b4b6617bee
-- title:
--   The gate-list view of a circuit: wires, gates, inp(S), out(S), evaluation of a subcircuit, the sets R_o (§2.1.1, §3.1)
-- statement:
--   In the **gate-list view** (§2.1.1, p. 25) a circuit is an ordered list of gates connected by wires. There are $il$ **input wires** $0,\dots,il-1$ and $n$ gates; gate $j$ writes wire $o_j=il+j$, reads the wires $l_j,r_j$, and computes a function $f_j:\{0,1\}^2\to\{0,1\}$. A vertex with fewer than two in-neighbours ignores its unused arguments, and the first input wire is fed to each missing argument. The **output wires** $W_{\mathrm{out}}$ are an ordered list of wires. The **topology** is the data $(il,n,l,r,W_{\mathrm{out}})$; two circuits with the same topology differ only in their gate functions. The view is **well formed** when the gates are topologically ordered ($l_j,r_j<il+j$), output wires exist, and no gate reads a wire of $W_{\mathrm{out}}$.
--
--   A **subcircuit** $S$ is a set of gates. Its **input boundary** $\mathrm{inp}(S)$ consists of the wires read by gates of $S$ that are not outputs of gates of $S$; its **output boundary** $\mathrm{out}(S)$ consists of the wires produced in $S$ that are read by a gate outside $S$ or belong to $W_{\mathrm{out}}$. For an assignment $\xi\in\{0,1\}^{\mathrm{inp}(S)}$ the gates of $S$ are evaluated in topological order; $o(\xi)$ is the resulting value at the output wire $o$ of a gate of $S$, and $w(\xi)=\xi_w$ for $w\in\mathrm{inp}(S)$. The map $\xi\mapsto(o(\xi))_{o\in\mathrm{out}(S)}$ is $C_S$. For $R\subseteq\mathrm{inp}(S)$ and an output wire $o$ of a gate of $S$,
--   $$R_o=\{\,w\in R:\ \text{a path through gates of }S\text{ leads from }w\text{ to }o\,\},$$
--   where a path step goes from a wire read by a gate of $S$ to the wire that gate writes.
--
--   These are the objects on which δ-equivalence (Definition 2.3) and incremental changes (Definition 3.1) are defined.
--
--   **Formalization Note.** Wires are natural numbers. `subVal f S ξ w` evaluates the gates of `S` in order on an assignment `ξ : ℕ → Bool` to all wires (only its values on $\mathrm{inp}(S)$ matter); wires not written by a gate of `S` keep their value under `ξ`. With `S` all gates and `ξ` the input it evaluates the whole circuit. `Ro S R j` is $R_o$ for $o=il+j$, as a type indexing the inputs of a describing circuit.
-- source:
--   Abram, Datta, Dutta, Roy, Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to Falsifiable Assumptions, STOC 2027 submission (manuscript sha256 f9518747…), p. 25, 'Gates and Subcircuits'; p. 45, §3.1 (o(ξ), R_o)

import Mathlib

/-!
# The gate-list view of a circuit: wires, gates, subcircuits and their boundaries (§2.1.1)

Abram, Datta, Dutta, Roy, *Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to
Falsifiable Assumptions*, STOC 2027 submission (manuscript sha256 f9518747…), p. 25, "Gates and
Subcircuits"; p. 45, the evaluation `o(ξ)` and the sets `R_o` of §3.1.

Representation. Wires are natural numbers. A `Wiring` (the topology in the gate-list view) has
`il` input wires `0, …, il - 1`, gates `0, …, n - 1`, gate `j` writing wire `il + j` and reading
wires `l j`, `r j`, and `ol` ordered output wires (`W_out`). The gate functions
`f : Fin n → Bool → Bool → Bool` are kept apart from the wiring, so two circuits with the same
topology are two label maps over one wiring. `WellFormed` is the paper's convention: gates are
topologically ordered (gate `j` reads only wires `< il + j`), output wires exist, and no gate reads
an output wire.
-/

namespace ObfEF.Incremental

/-- The topology of a circuit in the gate-list view. -/
structure Wiring where
  /-- Number of input wires `W_in = {0, …, il - 1}`. -/
  il : ℕ
  /-- Number of gates; gate `j` writes wire `il + j`. -/
  n : ℕ
  /-- Number of output wires. -/
  ol : ℕ
  /-- First input wire `l_j` of gate `j`. -/
  l : Fin n → ℕ
  /-- Second input wire `r_j` of gate `j`. -/
  r : Fin n → ℕ
  /-- The ordered output wires; `W_out` is their set. -/
  out : Fin ol → ℕ

namespace Wiring

variable (W : Wiring)

/-- The output wire `o_j = il + j` of gate `j`. -/
def gateWire (j : Fin W.n) : ℕ := W.il + j

/-- `w ∈ W_out`. -/
def IsOutWire (w : ℕ) : Prop := ∃ k : Fin W.ol, W.out k = w

/-- The conventions of the gate-list view: gates are topologically ordered, every output wire is
a wire of the circuit, and every gate reads only wires outside `W_out`. -/
def WellFormed : Prop :=
  (∀ j : Fin W.n, W.l j < W.il + j ∧ W.r j < W.il + j) ∧
  (∀ k : Fin W.ol, W.out k < W.il + W.n) ∧
  (∀ j : Fin W.n, ¬ W.IsOutWire (W.l j) ∧ ¬ W.IsOutWire (W.r j))

/-- Wire values after the first `k` gates when the gates of `S` are evaluated (with functions
`f`) and every other wire keeps its value under `ξ`. -/
def subVals (f : Fin W.n → Bool → Bool → Bool) (S : Finset (Fin W.n)) (ξ : ℕ → Bool) :
    ℕ → ℕ → Bool
  | 0 => ξ
  | k + 1 =>
      if h : k < W.n then
        if (⟨k, h⟩ : Fin W.n) ∈ S then
          Function.update (subVals f S ξ k) (W.il + k)
            (f ⟨k, h⟩ (subVals f S ξ k (W.l ⟨k, h⟩)) (subVals f S ξ k (W.r ⟨k, h⟩)))
        else subVals f S ξ k
      else subVals f S ξ k

/-- `w(ξ)`: the value at wire `w` when the gates of `S` are evaluated in topological order on the
boundary assignment `ξ` (for `w ∈ inp(S)` this is `ξ w`; for the output wire `o` of a gate of `S`
it is `o(ξ)`). With `S` = all gates and `ξ` extending an input assignment it is the evaluation of
the whole circuit. -/
def subVal (f : Fin W.n → Bool → Bool → Bool) (S : Finset (Fin W.n)) (ξ : ℕ → Bool) (w : ℕ) :
    Bool :=
  W.subVals f S ξ W.n w

/-- The input boundary `inp(S)`: wires read by gates of `S` that are not outputs of gates of `S`. -/
def inp (S : Finset (Fin W.n)) : Finset ℕ :=
  (S.biUnion fun j => ({W.l j, W.r j} : Finset ℕ)) \ S.image W.gateWire

/-- `o ∈ out(S)`: `o` is produced by a gate of `S` and read by a gate outside `S` or in `W_out`. -/
def IsOutBoundary (S : Finset (Fin W.n)) (o : ℕ) : Prop :=
  ∃ j ∈ S, o = W.gateWire j ∧
    ((∃ j' : Fin W.n, j' ∉ S ∧ (W.l j' = o ∨ W.r j' = o)) ∨ W.IsOutWire o)

/-- One step of a path through gates of `S`: a gate of `S` reads `a` and writes `b`. -/
def StepIn (S : Finset (Fin W.n)) (a b : ℕ) : Prop :=
  ∃ j ∈ S, b = W.gateWire j ∧ (W.l j = a ∨ W.r j = a)

/-- A path through gates of `S` leads from wire `a` to wire `b`. -/
def PathIn (S : Finset (Fin W.n)) (a b : ℕ) : Prop :=
  Relation.TransGen (W.StepIn S) a b

/-- `R_o` for `o` the output wire of gate `j`: the wires of `R` from which a path through gates of
`S` leads to `o`, as a type (it indexes the inputs of the describing circuits). -/
def Ro (S : Finset (Fin W.n)) (R : Finset ℕ) (j : Fin W.n) : Type :=
  {w : ℕ // w ∈ R ∧ W.PathIn S w (W.gateWire j)}

end Wiring

end ObfEF.Incremental


