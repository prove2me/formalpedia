-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
-- name    : OAI_Combinatorics_Hamiltonian_ColoredDual
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:28:48.354234+00:00
-- url     : https://prove2.me/theorems/084ac8f9-51db-4f05-8fca-7263117577aa
-- title:
--   Coloured dual structures, rooted face-assignment states, and signed state cycles
-- statement:
--   Let $N$ be an oriented network with finite vertex set $V$, finite edge set $E$ and tail and head maps $t_N, h_N$, and let $D$ be an oriented network on the same edge set with finite vertex set $F$ and maps $t_D, h_D$. Write $(\nabla_N f)(e) = f(h_N(e)) - f(t_N(e))$ for the gradient, $(\partial x)(v)$ for the net inflow of an edge function $x$ at a vertex $v$ (the boundary operator), $\sigma_D(e, z)$ for $1$ if $t_D(e) = z$ and $-1$ otherwise, $\operatorname{star}(v)$ for the set of edges at $v$, and $\mathbf{1}_v$ for the indicator function of $v$.
--
--   1. **Coloured dual.** A coloured dual structure on $(N, D)$ consists of: (a) duality: the underlying simple graphs of $N$ and $D$ are connected, $\ker \partial_N = \operatorname{im} \nabla_D$ and $\ker \partial_D = \operatorname{im} \nabla_N$; (b) $N$ and $D$ are simple (no loops and no two edges with the same unordered endpoint pair); (c) the underlying graph of $N$ is $3$-regular; (d) a predicate "black" on $V$ such that every edge has exactly one black endpoint; (e) for every $v \in V$ a labelled triangle of $D$ on $\operatorname{star}(v)$, i.e. distinct corners $c^v_0, c^v_1, c^v_2 \in F$ and an enumeration $e^v_0, e^v_1, e^v_2$ of $\operatorname{star}(v)$ such that $e^v_i$ joins $c^v_i$ and $c^v_{i+1}$ in $D$ (indices mod $3$); (f) the orientation condition
--   $$
--   (\nabla_N \mathbf{1}_v)(e^v_i) = \sigma_D(e^v_i, c^v_i) \qquad \text{for all } v \in V,\ i \in \mathbb{Z}/3,
--   $$
--   which says that $e^v_i$ points into $v$ in $N$ exactly when it runs from $c^v_i$ to $c^v_{i+1}$ in $D$.
--
--   2. **Rooted states.** Fix a root $r \in V$ and let $B_r$ be the set of black vertices other than $r$. The triangles $(c^v_0, c^v_1, c^v_2)$, $v \in B_r$, form a triangle system on $F$: two of them never share two corners. Let $F_r = F \setminus \{c^r_0, c^r_1, c^r_2\}$ be the dual vertices that are not corners of the root triangle. A state is a choice of corner index $s(v) \in \mathbb{Z}/3$ for every $v \in B_r$ such that
--   $$
--   B_r \to F_r, \qquad v \mapsto c^v_{s(v)},
--   $$
--   is a bijection. The assignment of a state extends this map to all of $V$ by sending every vertex outside $B_r$ to the fixed default $c^r_0$.
--
--   3. **Weights.** For $\alpha \in \mathbb{R}^E$ and $v \in B_r$, the weight vector $w_v : \mathbb{Z}/3 \to \mathbb{R}$ is the potential of $\alpha$ along the triangle of $v$: $w_v(0) = 0$, $w_v(1) = \alpha(e^v_0)\, \sigma_D(e^v_0, c^v_0)$ and $w_v(2) = w_v(1) + \alpha(e^v_1)\, \sigma_D(e^v_1, c^v_1)$.
--
--   4. **State cycles, delta and slope.** For a state $s$, a state cycle consists of a cycle $z_0, \dots, z_{m-1}$ in the underlying simple graph of $D$ ($m \geq 3$, distinct vertices, $z_i$ adjacent to $z_{i+1}$, indices mod $m$) together with, for each $i$, a vertex $u_i \in B_r$ and a corner index $k_i \in \mathbb{Z}/3$ such that
--   $$
--   c^{u_i}_{s(u_i)} = z_i \qquad \text{and} \qquad c^{u_i}_{k_i} = z_{i+1};
--   $$
--   so the cycle passes from the face assigned to $u_i$ to another corner of the triangle of $u_i$. With the index step $\delta(i, j)$ equal to $0$ if $i = j$, $1$ if $j = i + 1$ and $-1$ if $j = i - 1$, its delta and slope are
--   $$
--   \Delta(C) = \sum_{i} \delta\bigl(s(u_i), k_i\bigr) \in \mathbb{Z}, \qquad \operatorname{slope}_\alpha(C) = \sum_{i} \bigl( w_{u_i}(k_i) - w_{u_i}(s(u_i)) \bigr) \in \mathbb{R}.
--   $$
--
--   A coloured dual structure packages the data that the proof extracts from a cubic bipartite plane graph: the colour classes, the dual network whose vertices are faces, and the triangle of faces around each vertex with a coherent orientation. States are bijections between the non-root black vertices and the faces away from the root. The key sign property, proved elsewhere, is that if $\partial_N \alpha$ equals the white charge (charge $1$ at every non-black vertex and an additional $-W$ at the root, $W$ the number of non-black vertices), then every state cycle has either $\Delta = -3$ and positive slope, or $\Delta = 3$ and negative slope.
--
--   **Formalization Note** `ColoredDual N D` is a data-carrying structure with fields `duality`, `simple`, `dual_simple`, `cubic`, `black`, `coloring`, `face` and `oriented`. `Black root` is the subtype of black vertices different from `root`; then `system root`, `nonroots root`, `State root`, `assignment` (with the simp lemma `assignment_apply`), `weights`, the structure `StateCycle s` (fields `cycle`, `face`, `corner`, `left_eq`, `right_eq`), `StateCycle.delta` and `StateCycle.slope`. The proof that the black triangles never share two corners is given inline, using the simplicity of $D$ and the colouring.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/ColoredDual.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/ColoredDual.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BarnetteHamiltonian mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem

namespace OAI

/-! Colored dual networks and signed directed state cycles. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

structure ColoredDual where
  duality : N.Duality D
  simple : N.Simple
  dual_simple : D.Simple
  cubic : N.graph.IsRegularOfDegree 3
  black : V → Prop
  coloring : ∀ e, black (N.tail e) ↔ ¬black (N.head e)
  face : ∀ v, D.Triangle (N.star v)
  oriented : ∀ v i, N.gradient (fun w => if w = v then 1 else 0) ((face v).edge i) =
    D.arcSign ((face v).edge i) ((face v).corner i)

namespace ColoredDual
variable {N D} (M : N.ColoredDual D)

abbrev Black (root : V) := {v : V // M.black v ∧ v ≠ root}

def system (root : V) : Barnette.TriangleSystem (M.Black root) F where
  vertex t := (M.face t.val).corner
  vertex_injective t := (M.face t.val).corner_injective
  edge_unique t u i j k l hij hkl hik hjl := by
    have he : (M.face t.val).side D i j = (M.face u.val).side D k l := by
      apply M.dual_simple.pair_injective
      dsimp only
      rw [(M.face t.val).side_ends D hij,(M.face u.val).side_ends D hkl,hik,hjl]
    have ht := N.blackEndpoint_eq M.black M.coloring t.property.1
      ((N.mem_star _ _).mp ((M.face t.val).side_mem D i j))
    have hu := N.blackEndpoint_eq M.black M.coloring u.property.1
      ((N.mem_star _ _).mp ((M.face u.val).side_mem D k l))
    apply Subtype.ext
    exact ht.symm.trans (he ▸ hu)

def nonroots (root : V) : Set F := (Set.range (M.face root).corner)ᶜ

abbrev State (root : V) := (M.system root).State (M.nonroots root)

def assignment {root : V} (s : M.State root) (v : V) : F :=
  if hv : M.black v ∧ v ≠ root then s.value ⟨v,hv⟩ else (M.face root).corner 0

omit [Fintype F] in
@[simp] lemma assignment_apply {root : V} (s : M.State root) (v : M.Black root) :
    M.assignment s v.val = s.value v := by simp [assignment,v.property]

def weights (α : E → ℝ) (root : V) (t : M.Black root) : Fin 3 → ℝ :=
  (M.face t.val).potential D α

end ColoredDual
end
end Barnette.Network
namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D)

structure StateCycle {root : V} (s : M.State root) where
  cycle : Barnette.CycleCoordinates D.graph
  face : Fin (cycle.n+3) → M.Black root
  corner : Fin (cycle.n+3) → Fin 3
  left_eq : ∀ i, s.value (face i) = cycle.vertex i
  right_eq : ∀ i, (M.face (face i).val).corner (corner i) = cycle.vertex (i+1)

namespace StateCycle
variable {M} {root : V} {s : M.State root} (C : M.StateCycle s)

def delta : ℤ := ∑ i, Barnette.TriangleSystem.indexDelta (s.val (C.face i)) (C.corner i)

def slope (α : E → ℝ) : ℝ :=
  ∑ i, (M.weights α root (C.face i) (C.corner i) - M.weights α root (C.face i) (s.val (C.face i)))

end StateCycle
end
end Barnette.Network.ColoredDual

end OAI


