-- Prove2me | Definitions.Def_ResultantVNP_Circuit
-- name    : ResultantVNP_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:25:02.193012+00:00
-- url     : https://prove2.me/theorems/8a8c7c4e-2db4-490f-87af-9da31095d437
-- title:
--   Arithmetic circuits over $\mathbb C$ (fan-in two, size = number of gates)
-- statement:
--   An **arithmetic circuit** over $\mathbb C$ in variables $\sigma$ is a directed acyclic graph whose leaves are variables and complex constants and whose internal nodes (**gates**) add or multiply two earlier values; intermediate values may be reused. The circuit computes the polynomial at its output node. Its **size** is the number of gates.
--
--   **Formalization Note** A circuit is a nonempty list of nodes in topological order (a straight-line program): a leaf `var x` or `const a`, or a gate `add i j` / `mul i j` reading two earlier positions ($i=j$ allowed). The output is the last node; leaves are not counted in the size.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Section 3.1, p.14

import Mathlib

namespace ResultantVNP

/-- A node of an arithmetic circuit over `ℂ` with variables `σ`: a leaf (a variable or a complex
constant), or a gate adding or multiplying the values of two earlier nodes (referred to by position). -/
inductive Node (σ : Type) where
  | var (x : σ)
  | const (a : ℂ)
  | add (i j : ℕ)
  | mul (i j : ℕ)

/-- The value of a node, given the list of values of the nodes before it. -/
noncomputable def Node.eval {σ : Type} (vals : List (MvPolynomial σ ℂ)) :
    Node σ → MvPolynomial σ ℂ
  | .var x => MvPolynomial.X x
  | .const a => MvPolynomial.C a
  | .add i j => vals.getD i 0 + vals.getD j 0
  | .mul i j => vals.getD i 0 * vals.getD j 0

/-- The node reads only nodes at positions below `k`. -/
def Node.ReadsBelow {σ : Type} (k : ℕ) : Node σ → Prop
  | .add i j => i < k ∧ j < k
  | .mul i j => i < k ∧ j < k
  | _ => True

/-- Whether a node is a gate (an addition or multiplication), as opposed to a leaf. -/
def Node.isGate {σ : Type} : Node σ → Bool
  | .add _ _ => true
  | .mul _ _ => true
  | _ => false

/-- An **arithmetic circuit** over `ℂ` in the variables `σ`: a directed acyclic graph whose leaves are
variables and complex constants and whose internal nodes (gates) add or multiply two earlier values;
intermediate values may be reused. It is given as a nonempty list of nodes in topological order
(each gate reads two earlier positions); the output is the last node.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Section 3.1, p.14: "An arithmetic circuit is a directed acyclic graph that has variables and
complex constants as leaves. Each internal node (gate) adds or multiplies two earlier values, and
intermediate values may be reused. The size of a circuit is the number of gates."

**Formalization Note** A straight-line program: `nodes[k]` may read any positions `i, j < k` (also
`i = j`), so values are reused freely. `Circuit.value` is the polynomial computed at the last node
and `Circuit.size` counts the gates (leaves are not counted), as on p.14. -/
structure Circuit (σ : Type) where
  /-- The nodes, in topological order. -/
  nodes : List (Node σ)
  /-- A circuit has at least one node (its output). -/
  nonempty : nodes ≠ []
  /-- Every gate reads two earlier nodes. -/
  wf : ∀ (k : ℕ) (hk : k < nodes.length), (nodes[k]'hk).ReadsBelow k

/-- The values of all nodes of a circuit, in order. -/
noncomputable def Circuit.values {σ : Type} (C : Circuit σ) : List (MvPolynomial σ ℂ) :=
  C.nodes.foldl (fun vals nd => vals ++ [nd.eval vals]) []

/-- The polynomial computed by a circuit: the value of its last node. -/
noncomputable def Circuit.value {σ : Type} (C : Circuit σ) : MvPolynomial σ ℂ :=
  C.values.getLastD 0

/-- The size of a circuit: its number of gates. -/
def Circuit.size {σ : Type} (C : Circuit σ) : ℕ :=
  C.nodes.countP Node.isGate

end ResultantVNP


