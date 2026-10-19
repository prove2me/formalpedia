-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
-- name    : OAI_Combinatorics_Hamiltonian_Circulation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:25:26.30898+00:00
-- url     : https://prove2.me/theorems/e7401e90-3b5b-412e-96ee-e3bd47bf3b69
-- title:
--   Triangles as 3-cycles, reversed triangles, and the white-vertex charge
-- statement:
--   Let $D$ be an oriented network with vertex set $F$ and edge set $E$. A labelled triangle $\tau$ of $D$ on a set $s$ of edges consists of pairwise distinct corners $c_0, c_1, c_2 \in F$ and pairwise distinct edges $e_0, e_1, e_2$ with $\{e_0, e_1, e_2\} = s$, such that $e_i$ has endpoints $\{c_i, c_{i+1}\}$ in $D$ (indices in $\mathbb{Z}/3$).
--
--   1. **Triangle as a cycle.** Every labelled triangle defines a cycle of length $3$ in the underlying simple graph of $D$, with vertices $c_0, c_1, c_2$ in this cyclic order (consecutive corners are distinct and joined by an edge, hence adjacent).
--
--   2. **Reversed triangle.** The reverse of $\tau$ is the labelled triangle on the same edge set with
--   $$
--   c'_i = c_{-i}, \qquad e'_i = e_{-i-1} \qquad (i \in \mathbb{Z}/3),
--   $$
--   which runs through the same triangle in the opposite cyclic order; indeed $e'_i = e_{-i-1}$ joins $c_{-i-1} = c'_{i+1}$ and $c_{-i} = c'_i$.
--
--   3. **White charge.** Let $N$ be a network with finite vertex set $V$, let "black" be a predicate on $V$ (vertices that are not black are called white), let $W$ be the number of white vertices, and fix a root $r \in V$. The white charge is the function $\rho \in \mathbb{R}^V$ given by
--   $$
--   \rho(v) = [v \text{ is white}] - W \cdot [v = r],
--   $$
--   where $[P]$ is $1$ if $P$ holds and $0$ otherwise. Every white vertex carries charge $1$, the root carries an additional $-W$, and the total charge is $0$.
--
--   A flow $\alpha$ on $N$ whose net inflow at every vertex equals $\rho$ delivers one unit from the root to each white vertex. Pairing such an $\alpha$ with the gradient of the indicator function of a vertex set $A$ not containing the root counts the white vertices of $A$; this is the source of the strictly positive or negative slopes attached to cycles of states later in the argument. The conversion of triangles into $3$-cycles and their reversal let the faces of the dual be treated as oriented cycles.
--
--   **Formalization Note** `Triangle.coordinates` (a `CycleCoordinates` structure with `n = 0`), `Triangle.reverse`, and `whiteCharge black root`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Circulation.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Circulation.lean by skeleton subtraction
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

namespace OAI

/-! Oriented triangular faces and positive white-face charges. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype E] [Fintype F] in
def Triangle.coordinates {s : Finset E} (t : D.Triangle s) : Barnette.CycleCoordinates D.graph where
  n := 0
  vertex := ⟨t.corner,t.corner_injective⟩
  adjacent i := t.clique D (by
    intro hh
    have h1 : (1 : Fin 3) = 0 := add_left_cancel (by simpa using hh.symm : i+1=i+0)
    norm_num at h1)

omit [Fintype V] [Fintype E] [Fintype F] in
def Triangle.reverse {s : Finset E} (t : D.Triangle s) : D.Triangle s where
  corner i := t.corner (-i)
  corner_injective := t.corner_injective.comp neg_injective
  edge i := t.edge (-i-1)
  edge_injective := t.edge_injective.comp (by
    intro i j hh
    apply neg_injective
    simpa only [sub_add_cancel] using congrArg (fun k : Fin 3 => k+1) hh)
  edge_range := by
    have hh : Finset.univ.image (fun i : Fin 3 => t.edge (-i-1)) = Finset.univ.image t.edge := by
      ext e
      simp only [Finset.mem_image,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨i,rfl⟩; exact ⟨-i-1,rfl⟩
      · rintro ⟨i,rfl⟩
        refine ⟨-i-1,?_⟩
        congr 1
        abel
    exact hh.trans t.edge_range
  edge_ends i := by
    rw [t.edge_ends]
    have h1 : -i-1+1 = -i := sub_add_cancel _ _
    have h2 : -(i+1) = -i-1 := by abel
    rw [h1,h2,Sym2.eq_swap]

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

def whiteCharge (black : V → Prop) (root : V) : V → ℝ := fun v =>
  (if black v then 0 else 1) -
    (if v = root then ((Finset.univ.filter fun w => ¬black w).card : ℝ) else 0)

end
end Barnette.Network

end OAI


