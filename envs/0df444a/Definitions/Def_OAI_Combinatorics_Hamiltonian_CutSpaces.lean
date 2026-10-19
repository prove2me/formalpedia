-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
-- name    : OAI_Combinatorics_Hamiltonian_CutSpaces
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:18:15.391851+00:00
-- url     : https://prove2.me/theorems/e756bf51-dd72-4dbb-a36a-dc607b6458e0
-- title:
--   Edge cuts, simple networks, supports of edge functions, and labelled triangles
-- statement:
--   This file introduces basic combinatorial notions for an oriented network $N$ with vertex set $V$, edge set $E$, tail map $t : E \to V$ and head map $h : E \to V$ (a priori loops and parallel edges are allowed).
--
--   1. **Cut of a vertex set.** For finite $V$ and $E$ and a set $A \subseteq V$, the cut of $A$ is
--   $$
--   \delta_N(A) = \{ e \in E : t(e) \in A,\ h(e) \notin A \} \cup \{ e \in E : h(e) \in A,\ t(e) \notin A \},
--   $$
--   the set of edges with exactly one endpoint in $A$; loops never belong to a cut. Cuts are invariant under complementation: $\delta_N(V \setminus A) = \delta_N(A)$.
--
--   2. **Simple network.** $N$ is simple if it has no loops ($t(e) \neq h(e)$ for every $e$) and the map $e \mapsto \{t(e), h(e)\}$ to unordered pairs is injective, so that there are no parallel or antiparallel edges.
--
--   3. **Basis vectors, incidence and supports.** For $e \in E$, $\mathbf{1}_e \in \mathbb{R}^E$ is the standard basis vector ($\mathbf{1}_e(k) = 1$ if $k = e$ and $0$ otherwise). An edge $e$ is incident to a vertex $v$ if $v \in \{t(e), h(e)\}$. The support of an edge function $x \in \mathbb{R}^E$ is $\operatorname{supp}(x) = \{ e \in E : x_e \neq 0 \}$.
--
--   4. **Labelled triangle on an edge set.** For a finite set of edges $s \subseteq E$, a triangle on $s$ is the data of three pairwise distinct corners $c_0, c_1, c_2 \in V$ and three pairwise distinct edges $e_0, e_1, e_2$ with $\{e_0, e_1, e_2\} = s$, such that for every $i \in \mathbb{Z}/3$
--   $$
--   \{ t(e_i), h(e_i) \} = \{ c_i, c_{i+1} \} \qquad (\text{indices mod } 3).
--   $$
--   Thus $s$ consists of exactly three edges forming a triangle, and the labelling fixes a starting corner and a cyclic order; the same edge set may carry several labellings.
--
--   Cuts are the supports of gradients of indicator functions: if $\mathbf{1}_A$ denotes the indicator of $A$, then $\mathbf{1}_A(h(e)) - \mathbf{1}_A(t(e))$ equals $\pm 1$ exactly when $e \in \delta_N(A)$ and $0$ otherwise. Simplicity is later assumed both for a cubic plane graph and for its dual, and labelled triangles describe the faces of the dual: the three edges at a vertex of the cubic graph form a triangle in the dual network.
--
--   **Formalization Note** `cut A` is a `Finset E` for `A : Finset V`, with the simp lemma `mem_cut` and the lemma `cut_compl`. `Simple` is a `Prop`-valued structure that uses `Sym2` for unordered pairs. `basisVec`, `Incident` and `flowSupport` are as above (`flowSupport` takes the network only as an unused argument). `Triangle s` is a data-carrying structure indexed by `Fin 3`, whose addition wraps around mod 3.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/CutSpaces.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/CutSpaces.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BarnetteHamiltonian mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Cuts, simplicity, and connectivity of finite oriented networks. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

def cut (A : Finset V) : Finset E := Finset.univ.filter fun e =>
  (N.tail e ∈ A ∧ N.head e ∉ A) ∨ (N.head e ∈ A ∧ N.tail e ∉ A)

omit [Fintype V] in
@[simp] lemma mem_cut (A : Finset V) (e : E) : e ∈ N.cut A ↔
    (N.tail e ∈ A ∧ N.head e ∉ A) ∨ (N.head e ∈ A ∧ N.tail e ∉ A) := by
  simp [cut]

@[simp] lemma cut_compl (A : Finset V) : N.cut Aᶜ = N.cut A := by
  ext e
  simp only [mem_cut, Finset.mem_compl]
  tauto

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} (N : Network V E)

structure Simple : Prop where
  loopless : ∀ e, N.tail e ≠ N.head e
  pair_injective : Function.Injective (fun e => s(N.tail e, N.head e))

def basisVec (e : E) : E → ℝ := fun k => if k = e then 1 else 0

variable [Fintype V] [Fintype E]
variable {F : Type*} [Fintype F] (D : Network F E)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] [Fintype E] in
def Incident (e : E) (v : V) : Prop := N.tail e = v ∨ N.head e = v

def flowSupport (_N : Network V E) (x : E → ℝ) : Finset E := Finset.univ.filter fun e => x e ≠ 0

omit [Fintype V] in
@[simp] lemma mem_flowSupport (x : E → ℝ) (e : E) :
    e ∈ N.flowSupport x ↔ x e ≠ 0 := by simp [flowSupport]

structure Triangle (s : Finset E) where
  corner : Fin 3 → V
  corner_injective : Function.Injective corner
  edge : Fin 3 → E
  edge_injective : Function.Injective edge
  edge_range : Finset.univ.image edge = s
  edge_ends : ∀ i, s(N.tail (edge i), N.head (edge i)) = s(corner i, corner (i+1))

end
end Barnette.Network

end OAI


