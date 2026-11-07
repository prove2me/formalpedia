-- Prove2me | Definitions.Def_SetMultCost_Circuit
-- name    : SetMultCost_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:54.214376+00:00
-- url     : https://prove2.me/theorems/167a70ef-241d-4995-8752-4730b8119889
-- title:
--   Algebraic circuit: DAG, value, size
-- statement:
--   An **algebraic circuit** over a commutative ring $F$ with variables $\sigma$ is a directed acyclic graph whose leaves are labelled with a variable or a constant of $F$, and whose internal nodes are addition or multiplication gates of unbounded fan-in. A child may occur several times. One node is the root.
--
--   The **value** of a node is the polynomial in $F[\sigma]$ computed bottom up, with an empty sum equal to $0$ and an empty product equal to $1$. The value of the circuit is the value at its root. The **size** of the circuit is its number of edges, each occurrence of a child counting once, so $x\cdot x\cdot x$ has three edges.
--
--   This is the model in which every lower bound of the mission is stated. Values are elements of the polynomial ring, not functions on $F^\sigma$, a distinction that matters over finite fields.
--
--   **Formalization Note** Nodes are `Fin numNodes` in a topological order: every child has a smaller index than its parent, which encodes acyclicity. No layering is assumed; product-depth is defined separately.
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), §2, p.7

import Mathlib

namespace SetMultCost

/-- A node of an algebraic circuit: a leaf labelled with a variable or a field constant, or an
addition or multiplication gate with a list of children (a child may be repeated). -/
inductive Gate (σ F N : Type*) where
  | var (x : σ)
  | const (a : F)
  | add (children : List N)
  | mul (children : List N)

/-- The children of a node; leaves have none. -/
def Gate.children {σ F N : Type*} : Gate σ F N → List N
  | .var _ => []
  | .const _ => []
  | .add cs => cs
  | .mul cs => cs

/-- **Algebraic circuit.** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), §2, p.7: "An algebraic circuit is a directed acyclic graph whose
leaves are labeled either with a variable or a field constant. Internal nodes are either addition
or multiplication gates."

**Formalization Note.** The nodes are `Fin numNodes` in a topological order (every child has a
smaller index than its parent), which is how acyclicity is encoded; every finite DAG has such an
order. Fan-in is unbounded and a child may occur several times. There is one designated root.
Layering is not assumed; see `Circuit.HasProductDepthLE`. -/
structure Circuit (σ F : Type*) where
  /-- The number of nodes. -/
  numNodes : ℕ
  /-- The label of each node. -/
  gate : Fin numNodes → Gate σ F (Fin numNodes)
  /-- Every child comes earlier than its parent. -/
  acyclic : ∀ v, ∀ c ∈ (gate v).children, c < v
  /-- The output node. -/
  root : Fin numNodes

namespace Circuit

variable {σ F : Type*} [CommRing F]

/-- The polynomial computed at a node, as an element of `MvPolynomial`: "Computation proceeds
bottom up" (p.7). An addition gate adds and a multiplication gate multiplies its children, with
multiplicity; an empty sum is `0` and an empty product is `1`. -/
noncomputable def nodeValue (Φ : Circuit σ F) (v : Fin Φ.numNodes) : MvPolynomial σ F :=
  match h : Φ.gate v with
  | .var x => MvPolynomial.X x
  | .const a => MvPolynomial.C a
  | .add cs => (cs.attach.map fun c => nodeValue Φ c.1).sum
  | .mul cs => (cs.attach.map fun c => nodeValue Φ c.1).prod
termination_by v
decreasing_by
  · exact Φ.acyclic v c.1 (by simp only [h, Gate.children]; exact c.2)
  · exact Φ.acyclic v c.1 (by simp only [h, Gate.children]; exact c.2)

/-- The polynomial computed by the circuit, the value at its root ("the root computes a
multivariate polynomial", p.7). -/
noncomputable def value (Φ : Circuit σ F) : MvPolynomial σ F := Φ.nodeValue Φ.root

/-- **Size** (p.7): "The size of a circuit is the number of edges". Each occurrence of a child
counts, so `x · x · x` has three edges. -/
def size {F : Type*} (Φ : Circuit σ F) : ℕ := ∑ v, (Φ.gate v).children.length

end Circuit

end SetMultCost


