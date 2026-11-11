-- Prove2me | Definitions.Def_SparseLowFactors_BoundedDeg_Circuits
-- name    : SparseLowFactors_BoundedDeg_Circuits
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:22:55.152871+00:00
-- url     : https://prove2.me/theorems/15aaa9d5-3f6d-4bef-9836-9de98e9a3ab6
-- title:
--   Depth of an algebraic circuit; circuits with division gates
-- statement:
--   An **algebraic circuit** over $F$ (Definition 2.5) is a directed acyclic graph whose internal gates are labelled $+$ or $\times$ (arbitrary fan-in) and whose leaves are labelled by variables or elements of $F$; its size is the number of wires. This is the published definition `SetMultCost_Circuit`, reused here. This item adds:
--
--   1. The **depth** of a circuit: the length of the longest directed path from an input leaf to the output gate; a node with no children has depth $0$, any other node $1+$ the largest depth of a child.
--   2. A **circuit with division gates**: as above, except that a gate may also be labelled $\div$ with two children (numerator, denominator). It computes a rational function in $F(X)$, gate by gate from the leaves.
--   3. Such a circuit **computes** a polynomial $h$ when no division gate divides by the zero rational function and the rational function at the output equals $h$ ("this rational function will be promised to equal a polynomial"). Its **denominators** are the rational functions at the denominator children of its division gates. Size (number of wires) and depth are as for division-free circuits.
--
--   Constant-depth circuits, with and without division, are the output format of every algorithm of the paper.
--
--   **Formalization Note** Nodes are `Fin numNodes` in topological order, as in `SetMultCost_Circuit`. A circuit "computes" a polynomial as an element of $F[X]$ (respectively of $F(X)$), not as a function on $F^n$.
-- source:
--   Bhattacharjee, Kothary, Rai, Saraf, Deterministic Algorithms for Low Individual Degree Factors of Sparse Polynomials, arXiv:2606.27293 (held version, sha256 9837a932…), p. 16, Definition 2.5

import Mathlib
import Definitions.Def_SetMultCost_Circuit

set_option autoImplicit false

/-!
# Depth of an algebraic circuit, and circuits with division gates (Definition 2.5)

Bhattacharjee, Kothary, Rai, Saraf, arXiv:2606.27293 (held version, sha256 9837a932…), Definition 2.5,
p. 16. Division-free circuits and their size (number of wires) are the published
`SetMultCost.Circuit` (`Definitions.Def_SetMultCost_Circuit`); this file adds depth, and the
circuits with division gates.
-/

namespace SparseLowFactors.BoundedDeg

open SetMultCost

/-- The depth of a node: `0` for a node without children (a leaf), and `1 +` the largest depth of a
child otherwise, i.e. the length of the longest directed path from a leaf to the node. -/
def nodeDepth {σ F : Type*} (Φ : Circuit σ F) (v : Fin Φ.numNodes) : ℕ :=
  match h : (Φ.gate v).children with
  | [] => 0
  | c :: cs => 1 + ((c :: cs).attach.map fun x => nodeDepth Φ x.1).foldr max 0
termination_by v
decreasing_by exact Φ.acyclic v x.1 (by rw [h]; exact x.2)

/-- `depth(C)` (Definition 2.5): the length of the longest directed path from an input leaf to the
output gate. -/
def depth {σ F : Type*} (Φ : Circuit σ F) : ℕ := nodeDepth Φ Φ.root

/-- A node of a circuit with division gates: a leaf (variable or field constant), an addition or
multiplication gate of unbounded fan-in, or a division gate `num ÷ den`. -/
inductive DGate (σ F N : Type*) where
  | var (x : σ)
  | const (a : F)
  | add (children : List N)
  | mul (children : List N)
  | div (num den : N)

/-- The children of a node, with multiplicity; a division gate has the two children `num, den`. -/
def DGate.children {σ F N : Type*} : DGate σ F N → List N
  | .var _ => []
  | .const _ => []
  | .add cs => cs
  | .mul cs => cs
  | .div a b => [a, b]

/-- **Circuit with division gates** (Definition 2.5, last paragraph): as `SetMultCost.Circuit`
(nodes `Fin numNodes` in topological order, one root), with `÷` gates allowed. -/
structure DivCircuit (σ F : Type*) where
  numNodes : ℕ
  gate : Fin numNodes → DGate σ F (Fin numNodes)
  acyclic : ∀ v, ∀ c ∈ (gate v).children, c < v
  root : Fin numNodes

namespace DivCircuit

variable {σ F : Type*} [Field F]

/-- The rational function computed at a node, in the fraction field `F(X)` of `F[X]`. -/
noncomputable def nodeValue (Φ : DivCircuit σ F) (v : Fin Φ.numNodes) :
    FractionRing (MvPolynomial σ F) :=
  match h : Φ.gate v with
  | .var x => algebraMap (MvPolynomial σ F) (FractionRing (MvPolynomial σ F)) (MvPolynomial.X x)
  | .const a => algebraMap (MvPolynomial σ F) (FractionRing (MvPolynomial σ F)) (MvPolynomial.C a)
  | .add cs => (cs.attach.map fun c => nodeValue Φ c.1).sum
  | .mul cs => (cs.attach.map fun c => nodeValue Φ c.1).prod
  | .div a b => nodeValue Φ a / nodeValue Φ b
termination_by v
decreasing_by
  · exact Φ.acyclic v c.1 (by simp only [h, DGate.children]; exact c.2)
  · exact Φ.acyclic v c.1 (by simp only [h, DGate.children]; exact c.2)
  · exact Φ.acyclic v a (by simp [h, DGate.children])
  · exact Φ.acyclic v b (by simp [h, DGate.children])

/-- The rational function computed by the circuit (the value at the root). -/
noncomputable def value (Φ : DivCircuit σ F) : FractionRing (MvPolynomial σ F) :=
  Φ.nodeValue Φ.root

/-- The rational functions appearing as denominators at the division gates. -/
def IsDenominator (Φ : DivCircuit σ F) (q : FractionRing (MvPolynomial σ F)) : Prop :=
  ∃ v a b, Φ.gate v = .div a b ∧ Φ.nodeValue b = q

/-- The circuit is well defined: no division gate divides by the zero rational function. -/
def Defined (Φ : DivCircuit σ F) : Prop :=
  ∀ v a b, Φ.gate v = .div a b → Φ.nodeValue b ≠ 0

/-- The circuit computes the polynomial `h` ("this rational function will be promised to equal a
polynomial", Definition 2.5): it is well defined and its rational function is `h`. -/
def Computes (Φ : DivCircuit σ F) (h : MvPolynomial σ F) : Prop :=
  Φ.Defined ∧ Φ.value = algebraMap _ _ h

/-- Size: the number of wires (each occurrence of a child counts once). -/
def size {K : Type*} (Φ : DivCircuit σ K) : ℕ := ∑ v, (Φ.gate v).children.length

/-- Depth of a node (as for division-free circuits). -/
def nodeDepth {K : Type*} (Φ : DivCircuit σ K) (v : Fin Φ.numNodes) : ℕ :=
  match h : (Φ.gate v).children with
  | [] => 0
  | c :: cs => 1 + ((c :: cs).attach.map fun x => nodeDepth Φ x.1).foldr max 0
termination_by v
decreasing_by exact Φ.acyclic v x.1 (by rw [h]; exact x.2)

/-- Depth: the length of the longest directed path from a leaf to the output gate. -/
def depth {K : Type*} (Φ : DivCircuit σ K) : ℕ := Φ.nodeDepth Φ.root

end DivCircuit

end SparseLowFactors.BoundedDeg


