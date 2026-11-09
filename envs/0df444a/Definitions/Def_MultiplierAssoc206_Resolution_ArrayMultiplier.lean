-- Prove2me | Definitions.Def_MultiplierAssoc206_Resolution_ArrayMultiplier
-- name    : MultiplierAssoc206_Resolution_ArrayMultiplier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:14:25.879885+00:00
-- url     : https://prove2.me/theorems/b11a7587-ce82-4a89-a1ba-e88c3bbfb379
-- title:
--   Gate-level circuits and the array multiplier of Figure 1
-- statement:
--   A **gate circuit** with $n$-bit inputs $x,y$ assigns to every wire a gate: an ordered list of inputs (input bits, other wires, or the constant $0$) and a Boolean function of them. Its CNF has, for each wire $w$ and each assignment $\beta$ of the non-constant gate inputs, the clause that is falsified exactly when the inputs equal $\beta$ and $w$ differs from the gate's value at $\beta$. The function computed by a wire is the evaluation of the circuit.
--
--   **Array multiplier (§2, Figure 1).** The $n$-bit array multiplier computes each partial product $t_{i,j}=x_i\wedge y_j$ by an AND gate, and has a full adder in box $(i,j)$, $0\le i,j<n$, lying in column $i+j$, with outputs
--   $$s_{i,j}=a_0\oplus a_1\oplus a_2,\qquad c_{i,j}=\mathrm{MAJ}(a_0,a_1,a_2)$$
--   on the inputs $a_0=t_{i,j}$, $a_1$ the sum bit arriving from the row above, and $a_2$ the carry arriving from the previous column:
--
--   1. $a_1=s_{i+1,j-1}$ (vertical arrow) for $j\ge1$, $i+1<n$; $a_1=c_{n-1,j-1}$ for $i=n-1$, $j\ge1$ (diagonal arrow); $a_1=0$ in row $0$;
--   2. $a_2=c_{i-1,j}$ (horizontal arrow) for $i\ge1$; $a_2=0$ for $i=0$.
--
--   The outputs are $(xy)_k=s_{0,k}$ for $k<n$, $(xy)_k=s_{k-n+1,\,n-1}$ for $n\le k<2n-1$, and $(xy)_{2n-1}=c_{n-1,n-1}$. Every wire is determined by at most three other variables, so the clauses have width at most four.
--
--   **Formalization Note** Figure 1 is the only definition of the array multiplier in the paper; the conventions for row $0$, for the first box of each row and for the diagonal arrows are read off the figure. A missing adder input is the constant $0$ (a full adder with constant inputs acts as a half adder or a wire). The wire functions are computed by evaluating the gates, unfolding at most as many gates as there are wires.
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF pp.5–6 (printed pp.4–5), §2 Array multiplier and Figure 1 (PDF pp.5–6)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_Multiplier

namespace MultiplierAssoc206.Resolution

/-! # Gate-level circuits and the array multiplier

Liew, *Associativity of Multiplication Is Hard for Resolution*, §2 "Array multiplier" and
Figure 1 (PDF pp. 5–6). A gate circuit lists, for every wire, its constant-fan-in gate: an
ordered list of inputs (an input bit, another wire, or the constant `0`) and the Boolean
function of them. Its CNF has, for every wire and every assignment `β` of the gate's non-constant
inputs, the clause falsified exactly when the inputs equal `β` and the wire differs from the
gate's value at `β`. -/

/-- The fan-in-bounded gate description of a multiplier circuit with `n`-bit inputs. An input
`none` of a gate is the constant `0`. -/
structure GateCircuit (n : ℕ) where
  /-- the wires -/
  W : Type
  [decEq : DecidableEq W]
  [fintype : Fintype W]
  /-- the ordered inputs of the gate computing each wire -/
  ins : W → List (Option (MulVar W n))
  /-- the Boolean function of its inputs computed by each gate -/
  op : W → List Bool → Bool
  /-- the `2n` output wires -/
  out : Fin (2 * n) → W

attribute [instance] GateCircuit.decEq GateCircuit.fintype

namespace GateCircuit

variable {n : ℕ} (C : GateCircuit n)

/-- Evaluation of the circuit at inputs `(x, y)`, unfolding at most `d` gates. -/
def evalFuel (x y : Fin n → Bool) : ℕ → MulVar C.W n → Bool
  | _, .x i => x i
  | _, .y i => y i
  | 0, .wire _ => false
  | d + 1, .wire w =>
      C.op w ((C.ins w).map fun o =>
        match o with
        | none => false
        | some v => evalFuel x y d v)

/-- The Boolean function computed by the wire `w`: evaluation with as many unfoldings as there
are wires (enough for any acyclic circuit). -/
def wireFn (w : C.W) (x y : Fin n → Bool) : Bool :=
  C.evalFuel x y (Fintype.card C.W + 1) (.wire w)

open Classical in
/-- The clauses of the gate `z = o(L)`: for each assignment `β` of the positions of `L` (with
the constant positions `0`), the clause `⋁_{L_k = v} (v ≠ β_k) ∨ (z = o(β))`. -/
noncomputable def gateClauses {α : Type} (L : List (Option α)) (o : List Bool → Bool) (z : α) :
    CNF α :=
  (Finset.univ.filter fun β : Fin L.length → Bool => ∀ k, L.get k = none → β k = false).image
    fun β =>
      insert (z, o (List.ofFn β))
        (Finset.univ.biUnion fun k : Fin L.length =>
          match L.get k with
          | none => ∅
          | some v => {(v, !β k)})

open Classical in
/-- The encoding of a gate circuit: the CNF of all its gates, with the functions computed by its
wires and its output wires. -/
noncomputable def toEncoding : MulEncoding n where
  W := C.W
  cnf := Finset.univ.biUnion fun w => gateClauses (C.ins w) (C.op w) (MulVar.wire w)
  fn := C.wireFn
  out := C.out

end GateCircuit

/-- `a₀ ⊕ a₁ ⊕ ⋯` -/
def xorList (l : List Bool) : Bool := l.foldl xor false

/-- `MAJ` with absent inputs read as `0`: at least two inputs are `1`. -/
def majList (l : List Bool) : Bool := decide (2 ≤ l.count true)

/-- The wires of the `n`-bit array multiplier: the partial product `t_{i,j}` (an AND gate) and
the sum and carry outputs of the full adder in box `(i, j)`. -/
inductive ArrayWire (n : ℕ) where
  | pp (i j : Fin n) : ArrayWire n
  | sum (i j : Fin n) : ArrayWire n
  | carry (i j : Fin n) : ArrayWire n
  deriving DecidableEq, Fintype

namespace ArrayMultiplier

variable {n : ℕ}

/-- The sum bit arriving at box `(i, j)` from the row above (Figure 1): none in row `0`; the sum
bit of box `(i+1, j−1)` (vertical arrow); for `i = n−1`, the carry out of box `(n−1, j−1)`, the
last box of the previous row (diagonal arrow). -/
def sumIn (i j : Fin n) : Option (MulVar (ArrayWire n) n) :=
  if hj : (j : ℕ) = 0 then none
  else if hi : (i : ℕ) + 1 < n then
    some (.wire (.sum ⟨i + 1, hi⟩ ⟨j - 1, by omega⟩))
  else some (.wire (.carry ⟨n - 1, by omega⟩ ⟨j - 1, by omega⟩))

/-- The carry arriving at box `(i, j)` from the previous column of its row (horizontal arrow):
the carry of box `(i−1, j)`; none for `i = 0`. -/
def carryIn (i j : Fin n) : Option (MulVar (ArrayWire n) n) :=
  if hi : (i : ℕ) = 0 then none else some (.wire (.carry ⟨i - 1, by omega⟩ j))

/-- The output wire for bit `k` of the product (Figure 1): the sum bit of box `(0, k)` for
`k < n`, the sum bit of box `(k−n+1, n−1)` of the bottom row for `n ≤ k < 2n − 1`, and the carry
out of box `(n−1, n−1)` for `k = 2n − 1`. -/
def out (k : Fin (2 * n)) : ArrayWire n :=
  if hk : (k : ℕ) < n then .sum ⟨0, by omega⟩ ⟨k, hk⟩
  else if hk' : (k : ℕ) < 2 * n - 1 then .sum ⟨k - n + 1, by omega⟩ ⟨n - 1, by omega⟩
  else .carry ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩

end ArrayMultiplier

open ArrayMultiplier in
/-- The `n`-bit array multiplier of Figure 1 as a gate circuit. Box `(i, j)` (`0 ≤ i, j < n`)
lies in column `i + j` and is a full adder `s = a₀ ⊕ a₁ ⊕ a₂`, `c = MAJ(a₀, a₁, a₂)` with
inputs `a₀ = t_{i,j} = x_i ∧ y_j`, `a₁ = sumIn i j`, `a₂ = carryIn i j`, a missing input being
the constant `0`. -/
def arrayCircuit (n : ℕ) : GateCircuit n where
  W := ArrayWire n
  ins := fun w =>
    match w with
    | .pp i j => [some (.x i), some (.y j)]
    | .sum i j => [some (.wire (.pp i j)), sumIn i j, carryIn i j]
    | .carry i j => [some (.wire (.pp i j)), sumIn i j, carryIn i j]
  op := fun w =>
    match w with
    | .pp _ _ => fun l => l.all id
    | .sum _ _ => xorList
    | .carry _ _ => majList
  out := ArrayMultiplier.out

/-- The array multiplier encodings, one for each bit-width `n` (§2, Figure 1). -/
noncomputable def arrayMultiplier (n : ℕ) : MulEncoding n := (arrayCircuit n).toEncoding

end MultiplierAssoc206.Resolution


