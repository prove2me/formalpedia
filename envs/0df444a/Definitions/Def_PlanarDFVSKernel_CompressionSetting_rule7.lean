-- Prove2me | Definitions.Def_PlanarDFVSKernel_CompressionSetting_rule7
-- name    : PlanarDFVSKernel_CompressionSetting_rule7
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:37:31.447381+00:00
-- url     : https://prove2.me/theorems/a5229c73-6163-408b-a8ef-3feb54f336ff
-- title:
--   Reduction Rule 7: merging vertices with equal distance records
-- statement:
--   In a compression setting, the **identification classes** are: each retained vertex forms its own class, and two vertices outside $W$ are in the same class when they lie in the same weakly connected component of $H$ and have the same distance record. **Reduction Rule 7** forms the quotient by these classes, preserving the grouping of reverse arcs, and normalizes it:
--   1. base loops are deleted and one copy of each base arc is kept;
--   2. from every group, loops, arcs already present as base arcs and repeated copies are deleted, and empty groups are discarded;
--   3. one ordinary group is kept for each distinct remaining ordinary reverse arc, and the remaining special groups keep their identities.
--
--   The budget $k$ is unchanged.
--
--   **Formalization Note** A retained vertex outside the component of $v$ has $d_L=\infty$ to $v$, so (component, full record) is the paper's (component, record over $W_C$).
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), Reduction Rule 7, p.18 (PDF 19); §1.2, p.5 (PDF 6)

import Mathlib
import Definitions.Def_PlanarDFVSKernel_CompressionSetting

set_option autoImplicit false

namespace PlanarDFVSKernel

namespace CompressionSetting

variable {V : Type*} [Fintype V] [DecidableEq V] (C : CompressionSetting V)

/-- **The identification class of a vertex** (Sheng, Xiao, *A Polynomial Kernel for Planar
Directed Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256 75cfca8f…), §5.1, p.18
(PDF 19)): "vertices outside W belong to the same class exactly when their records are equal, and
each vertex of W forms a singleton class"; merging is done "separately within each weakly connected
component C of H" with records over `W_C = W ∩ V(C)` (§1.2, p.5 (PDF 6)).

A retained vertex `w` gets the key `inl w`; a vertex `v ∉ W` gets the key formed by its weakly
connected component (as a vertex set) and its record `θ(v)`.

**Formalization Note** A retained `w` outside the component of `v` has `d_L(w, v) = ∞` (base arcs
and available arcs stay inside a component), so `θ_w(v) = k + 1` for all such `w`: the pair
(component, full record) is the paper's pair (component, record over `W_C`). -/
noncomputable def classKey (v : V) : V ⊕ (Finset V × (C.W → ℕ)) := by
  classical exact (if v ∈ C.W then Sum.inl v else
    Sum.inr (Finset.univ.filter fun u => ArcWeakReach C.I.base v u, C.theta v))

/-- The vertex set of the quotient graph: the identification classes, represented by their keys. -/
abbrev Q : Type _ := Set.range C.classKey

/-- The map `π : V(H) → V(H̄)` sending a vertex to its class (ibid., p.18 (PDF 19)). -/
noncomputable def proj (v : V) : C.Q := ⟨C.classKey v, v, rfl⟩

/-- **Reduction Rule 7** (Sheng, Xiao, arXiv:2609.23669 (held version, sha256 75cfca8f…), p.18
(PDF 19)): "Form the quotient by the identification classes defined above, preserving the grouping
of reverse arcs, and normalize it as follows. (i) Delete base loops and keep one copy of each
remaining base arc. (ii) From every group, delete loops, arcs already present as base arcs, and
repeated copies of an arc. Discard empty groups. (iii) Keep one ordinary group for each distinct
remaining reverse arc. Preserve the identities of the remaining special groups. Leave k unchanged."

The output is the GSCA instance on the classes whose base arcs are the images `π(u) → π(v)` of the
base arcs, without loops and repetitions; whose groups are the normalized images of the special
groups that remain nonempty (in their original order), followed by one single-arc group for each
distinct arc remaining in some normalized ordinary group; and whose budget is `k`.

**Formalization Note** The order of the groups in the list is immaterial for solvability. -/
noncomputable def rule7 : GSCA C.Q := by
  classical
  let pr : V × V → C.Q × C.Q := fun a => (C.proj a.1, C.proj a.2)
  let base' : List (C.Q × C.Q) := ((C.I.base.map pr).filter fun a => a.1 ≠ a.2).dedup
  let norm : Finset (V × V) → Finset (C.Q × C.Q) :=
    fun g => (g.image pr).filter fun a => a.1 ≠ a.2 ∧ a ∉ base'
  let special : List (Finset (C.Q × C.Q)) :=
    ((((List.finRange C.I.groups.length).filter fun i => i ∉ C.ordinary).map
      fun i => norm C.I.groups[i]).filter fun g => g.Nonempty)
  let ordArcs : Finset (C.Q × C.Q) := C.ordinary.biUnion fun i => norm C.I.groups[i]
  exact ⟨base', special ++ ordArcs.toList.map fun a => {a}, C.I.k⟩

end CompressionSetting

end PlanarDFVSKernel


