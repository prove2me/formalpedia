-- Prove2me | Definitions.Def_GraphIsoTesting_FixedGraph_ParityGadget
-- name    : GraphIsoTesting_FixedGraph_ParityGadget
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:34:04.225471+00:00
-- url     : https://prove2.me/theorems/53f6f4cd-6c43-49b6-baed-bc3c116c35a2
-- title:
--   Fixed-label parity gadgets, explicit ports, and preservation predicates
-- statement:
--   Fix a binary $m\times k$ matrix $A$ with row weight three and column weight six. List each row's nonzero columns in increasing order as $c_j(1),c_j(2),c_j(3)$, and order the six occurrences of each variable by row index. These choices depend only on $A$. The four fixed assignment labels are the lexicographic list $P_0=(000,011,101,110)$. A label $\alpha$ in row $j$ represents the actual assignment $\tau_\ell=\alpha_\ell+b_j$.
--
--   The graph $G_b$ has variable anchors $v_i$, value vertices $v_i^s$, constraint anchors $a_j$, and assignment vertices $a_j^\alpha$. Its edges are exactly
--
--   $$\{v_i,v_i^s\},\quad \{a_j,a_j^\alpha\},\quad
--   \{a_j^\alpha,v_{c_j(\ell)}^{\alpha_\ell+b_j}\}.$$
--
--   There are $3k+5m$ vertices, all labeled independently of $b$. Assignment ports 1–3 give the three values and port 4 the anchor. Value ports $2h-1,2h$ give the two lexicographically ordered matching assignments at occurrence $h$; port 13 gives the variable anchor. Variable anchors use ports 1–2; constraint anchors use ports 1–4. Higher unused ports give null. The query-coordinate function specifies the unique row bit needed, or no row for a constant answer; the local answer function has a concrete body.
--
--   A role-preserving bijection maps the entire variable-anchor and value classes onto themselves, without restricting the other vertices. A variable-preserving bijection additionally maps each whole variable gadget to a gadget indexed by a variable permutation, allowing its two values to be swapped. It places no restriction on constraint-gadget vertices. The mismatch count is the full unordered-edge symmetric difference between the transported $G_0$ and $G_b$.
--
--   These are the actual parity graphs and source preservation notions, without colors, rigidity overlays, hardness fields, or assumed graph properties. Zero-based ports subtract one from the paper's port numbers. Increasing row/occurrence orders are particular permitted choices of the source's fixed orderings. The graph definition is given for all matrices with the exact weights; independence is a separate property used for hardness.
-- source:
--   Amit Dror, STOC 2027 submission #130 (October 2026), pp. 7–11, §§3.1–3.4, equations (4)–(6)

import Mathlib
import Definitions.Def_GraphIsoTesting_FixedGraph_BinarySystems
import Definitions.Def_GraphIsoTesting_FixedGraph_GraphModel

namespace GraphIsoTesting.FixedGraph

/-- Fixed labels: k anchors, 2k values, m anchors, 4m even assignments. -/
abbrev GadgetVertex (m k : ℕ) :=
  (Fin k ⊕ (Fin k × Bit)) ⊕ (Fin m ⊕ (Fin m × Fin 4))

def variableAnchor {m k : ℕ} (i : Fin k) : GadgetVertex m k := .inl (.inl i)
def valueVertex {m k : ℕ} (i : Fin k) (s : Bit) : GadgetVertex m k := .inl (.inr (i, s))
def constraintAnchor {m k : ℕ} (j : Fin m) : GadgetVertex m k := .inr (.inl j)
def assignmentVertex {m k : ℕ} (j : Fin m) (a : Fin 4) : GadgetVertex m k := .inr (.inr (j, a))

/-- P₀ in lexicographic order: 000, 011, 101, 110. -/
def alphaBit (a : Fin 4) (l : Fin 3) : Bit :=
  ![![0, 0, 0], ![0, 1, 1], ![1, 0, 1], ![1, 1, 0]] a l

/-- The three nonzero columns, in increasing order; depends only on A. -/
noncomputable def rowColumn {m k : ℕ} (A : BinaryMatrix m k) (h : Sparse36 A)
    (j : Fin m) : Fin 3 → Fin k := by
  classical
  exact fun l => (Finset.univ.filter fun i => A j i ≠ 0).orderEmbOfFin (h.1 j) l

/-- Six occurrences, ordered by row; the second component is the position in that row. -/
noncomputable def occurrence {m k : ℕ} (A : BinaryMatrix m k) (h : Sparse36 A)
    (i : Fin k) (z : Fin 6) : Fin m × Fin 3 := by
  classical
  let row := (Finset.univ.filter fun j => A j i ≠ 0).orderIsoOfFin (h.2 i) z
  have hi : A row.val i ≠ 0 := (Finset.mem_filter.mp row.property).2
  let pos := ((Finset.univ.filter fun t => A row.val t ≠ 0).orderIsoOfFin
    (h.1 row.val)).symm ⟨i, by simp [hi]⟩
  exact (row.val, pos)

/-- Directed edge templates, symmetrized by SimpleGraph.fromRel. -/
def gadgetEdge {m k : ℕ} (c : Fin m → Fin 3 → Fin k) (b : Fin m → Bit) :
    GadgetVertex m k → GadgetVertex m k → Prop
  | .inl (.inl i), .inl (.inr (i', _)) => i = i'
  | .inr (.inl j), .inr (.inr (j', _)) => j = j'
  | .inr (.inr (j, a)), .inl (.inr (i, s)) =>
      ∃ l : Fin 3, c j l = i ∧ alphaBit a l + b j = s
  | _, _ => False

noncomputable def gadgetGraph {m k : ℕ} (A : BinaryMatrix m k) (h : Sparse36 A)
    (b : Fin m → Bit) : SimpleGraph (GadgetVertex m k) :=
  SimpleGraph.fromRel (gadgetEdge (rowColumn A h) b)

/-- Exactly the lexicographically ordered P₀ labels whose chosen coordinate is t. -/
def matchingAlphas (l : Fin 3) (t : Bit) : List (Fin 4) :=
  (List.finRange 4).filter fun a => alphaBit a l == t

/-- The source's ports 1,...,13 are represented by p.val = 0,...,12. -/
noncomputable def gadgetOracle {m k : ℕ} (A : BinaryMatrix m k) (h : Sparse36 A)
    (b : Fin m → Bit) : IncidenceOracle (GadgetVertex m k) 13
  | (.inl (.inl i), p) =>
      if p.val = 0 then some (valueVertex i 0)
      else if p.val = 1 then some (valueVertex i 1) else none
  | (.inr (.inl j), p) =>
      if hp : p.val < 4 then some (assignmentVertex j ⟨p.val, hp⟩) else none
  | (.inr (.inr (j, a)), p) =>
      if hp : p.val < 3 then
        some (valueVertex (rowColumn A h j ⟨p.val, hp⟩) (alphaBit a ⟨p.val, hp⟩ + b j))
      else if p.val = 3 then some (constraintAnchor j) else none
  | (.inl (.inr (i, s)), p) =>
      if hp : p.val < 12 then
        let occ := occurrence A h i ⟨p.val / 2, by omega⟩
        ((matchingAlphas occ.2 (s + b occ.1))[p.val % 2]?).map
          (fun a => assignmentVertex occ.1 a)
      else some (variableAnchor i)

/-- A bit index fixed by the query and A alone, or no bit for constant answers. -/
noncomputable def queryCoordinate {m k : ℕ} (A : BinaryMatrix m k) (h : Sparse36 A) :
    GadgetVertex m k × Fin 13 → Option (Fin m)
  | (.inr (.inr (j, _)), p) => if p.val < 3 then some j else none
  | (.inl (.inr (i, _)), p) =>
      if hp : p.val < 12 then some (occurrence A h i ⟨p.val / 2, by omega⟩).1 else none
  | _ => none

/-- Explicit local answer computation; a supplied bit is inserted only at the specified row. -/
noncomputable def emulateAnswer {m k : ℕ} (A : BinaryMatrix m k) (h : Sparse36 A)
    (query : GadgetVertex m k × Fin 13) (bit : Bit) : Option (GadgetVertex m k) :=
  gadgetOracle A h (fun _ => bit) query

/-- Maps both entire variable roles onto themselves, without any constraint-role condition. -/
def RolePreserving {m k : ℕ} (π : Equiv.Perm (GadgetVertex m k)) : Prop :=
  (∀ v, (∃ i, v = variableAnchor i) ↔ ∃ i, π v = variableAnchor i) ∧
  (∀ v, (∃ i s, v = valueVertex i s) ↔ ∃ i s, π v = valueVertex i s)

/-- Permute whole variable gadgets and optionally flip each pair; no constraint on other vertices. -/
def VariablePreserving {m k : ℕ} (π : Equiv.Perm (GadgetVertex m k)) : Prop :=
  ∃ ρ : Equiv.Perm (Fin k), ∀ i,
    π (variableAnchor i) = variableAnchor (ρ i) ∧
    ∀ s : Bit, ∃ t : Bit, π (valueVertex i s) = valueVertex (ρ i) t

noncomputable def gadgetMismatch {m k : ℕ} (A : BinaryMatrix m k) (h : Sparse36 A)
    (b : Fin m → Bit) (π : Equiv.Perm (GadgetVertex m k)) : ℕ :=
  edgeMismatch (gadgetGraph A h 0) (gadgetGraph A h b) π

end GraphIsoTesting.FixedGraph


