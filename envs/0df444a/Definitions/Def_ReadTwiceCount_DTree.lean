-- Prove2me | Definitions.Def_ReadTwiceCount_DTree
-- name    : ReadTwiceCount_DTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:27.244215+00:00
-- url     : https://prove2.me/theorems/70d3efca-a9bf-42e7-b7ee-b997e4e100e4
-- title:
--   Descriptor trees, frontier leaves, path derivatives $D_u$, cuts and EQ boundaries
-- statement:
--   A **descriptor tree** is a frontier input (a leaf), an exact constant $r$, or a node carrying a descriptor whose $j$-th input is the value of the $j$-th subtree. Nodes are addressed by paths of child indices from the root; repeated residual formulas are separate nodes.
--
--   1. The **value** of the tree at frontier inputs $x_u$ is computed bottom-up by the descriptors $\mathcal F$.
--   2. The **path derivative** $D_u$ of a frontier leaf $u$ is the product, along the root-to-$u$ path, of the absolute partial derivatives $|\partial\mathcal F/\partial y_j|$ of each node descriptor, each evaluated at the node's input values. By the chain rule this is the absolute derivative of the root with respect to $x_u$, the description the paper gives on p.5.
--   3. A tree is **well formed** if every node descriptor is nonsingular and every constant is at least $1$.
--   4. In a block, the **EQ boundary inputs** $E$ are the frontier leaves reached by an $\mathrm{EQ}$ edge, and the **cut inputs** $C$ are the other frontier leaves: those reached by a $\mathrm{NEQ}$ edge, and the root if it is a leaf.
--   5. A tree has the **shape of a positive block** if every $\mathrm{EQ}$ child of a node is a frontier leaf, so all internal edges are $\mathrm{NEQ}$.
--
--   **Formalization Note** $D_u$ is defined as the product of the local derivatives; it is $0$ on a path that is not a leaf.
-- source:
--   He, A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments, STOC 2027 submission (manuscript sha256 7a2a9dcd…), §4, p.5; §5.1, p.6

import Mathlib
import Definitions.Def_ReadTwiceCount_Descriptor

namespace ReadTwiceCount

/-- **A descriptor tree** (He, *A Deterministic Approximation Scheme for Counting Read-Twice CNF
Assignments*, STOC 2027 submission, manuscript sha256 7a2a9dcd…, §4, p.5 and §5.1, p.6): a frontier
input (`leaf`), an exact constant (`const r`), or a node carrying a descriptor (`t` free factors and
`n` labelled inputs) whose `j`-th input is the value of the subtree `child j`.

Nodes are addressed by paths: a list of child indices from the root. Repeated residual formulas are
separate nodes (p.5). -/
inductive DTree
  | leaf : DTree
  | const (r : ℝ) : DTree
  | node (t n : ℕ) (label : Fin n → Label) (child : Fin n → DTree) : DTree

namespace DTree

/-- The descriptor at a node. -/
def desc (t n : ℕ) (label : Fin n → Label) : Descriptor := ⟨t, n, label⟩

/-- **The value of the tree** at frontier inputs `x` (`x u` is the input at the leaf with path
`u`), computed bottom-up by the descriptors ℱ. -/
noncomputable def eval : DTree → (List ℕ → ℝ) → ℝ
  | .leaf, x => x []
  | .const r, _ => r
  | .node t n label child, x =>
      (desc t n label).value fun i => (child i).eval fun p => x (i.val :: p)

/-- The paths of the frontier leaves. -/
def leaves : DTree → Finset (List ℕ)
  | .leaf => {[]}
  | .const _ => ∅
  | .node _ n _ child => Finset.univ.biUnion fun j : Fin n => (child j).leaves.image (List.cons j.val)

/-- The label of the last edge on the path `u` (`none` for the root or a path that does not exist).
-/
def lastLabel : DTree → List ℕ → Option Label
  | .node _ n label _, [j] => if h : j < n then some (label ⟨j, h⟩) else none
  | .node _ n _ child, j :: p => if h : j < n then (child ⟨j, h⟩).lastLabel p else none
  | _, _ => none

/-- **The path derivative `D_u`** (He, STOC 2027 submission, manuscript sha256 7a2a9dcd…, §4, p.5:
"At a frontier node u, let D_u denote the absolute derivative of the root with respect to that
frontier input, with all other frontier inputs fixed. This derivative is a product along its path"):
the product, along the root-to-`u` path, of the absolute partial derivatives `|∂ℱ/∂y_j|` of each node
descriptor, each taken at the node's input values in the evaluation at `x`.

**Formalization Note** The product of local derivatives is the paper's own description of `D_u`
(the chain rule along the path). It is `0` on a path that is not a leaf. -/
noncomputable def pathDeriv : DTree → (List ℕ → ℝ) → List ℕ → ℝ
  | .leaf, _, [] => 1
  | .node t n label child, x, j :: p =>
      if h : j < n then
        |(desc t n label).partialDeriv (fun i => (child i).eval fun q => x (i.val :: q)) ⟨j, h⟩| *
          (child ⟨j, h⟩).pathDeriv (fun q => x (j :: q)) p
      else 0
  | _, _, _ => 0

/-- **A well-formed abstract tree**: every node descriptor is nonsingular and every constant is at
least `1`. -/
def WellFormed : DTree → Prop
  | .leaf => True
  | .const r => 1 ≤ r
  | .node t n label child => (desc t n label).Nonsingular ∧ ∀ j, (child j).WellFormed

/-- **The EQ boundary inputs** `E` of a block: frontier leaves reached by an `EQ` edge (§5.1, p.6). -/
def boundaries (T : DTree) : Finset (List ℕ) := T.leaves.filter fun u => T.lastLabel u = some .EQ

/-- **The cut inputs** `C` of a block: frontier leaves reached by a `NEQ` edge, and the root if it is
a leaf (§5.1, p.6: "The initial unresolved root is also a cut input"). -/
def cuts (T : DTree) : Finset (List ℕ) := T.leaves.filter fun u => T.lastLabel u ≠ some .EQ

/-- The shape of a **positive block** (§5.1, p.6: "A positive block is a partial computation tree
whose internal edges are all NEQ"): every `EQ` child of a node is a frontier leaf. -/
def EqChildrenAreLeaves : DTree → Prop
  | .leaf => True
  | .const _ => True
  | .node _ _ label child => ∀ j, (label j = .EQ → child j = .leaf) ∧ (child j).EqChildrenAreLeaves

end DTree

end ReadTwiceCount


