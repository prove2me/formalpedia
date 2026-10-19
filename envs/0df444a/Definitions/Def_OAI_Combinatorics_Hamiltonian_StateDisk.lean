-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
-- name    : OAI_Combinatorics_Hamiltonian_StateDisk
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:23:37.616147+00:00
-- url     : https://prove2.me/theorems/39ba1b59-f1fb-47d4-a1f9-cbd91706394f
-- title:
--   Black endpoints, black cuts, and the pairing of the black indicator gradient with a dual cycle
-- statement:
--   Let $N$ be an oriented network with finite vertex set $V$, finite edge set $E$, tail and head maps $t_N, h_N : E \to V$, and let $D$ be a second network on the same edges with finite vertex set $F$ and tail and head maps $t_D, h_D : E \to F$. A colouring is a predicate "black" on $V$; it is proper if every edge has exactly one black endpoint ($t_N(e)$ is black if and only if $h_N(e)$ is not). For a cycle $C$ of length $m \geq 3$ in the underlying simple graph of $D$, given by distinct vertices $z_i$ ($i \in \mathbb{Z}/m$) with $z_i$ adjacent to $z_{i+1}$, let $e_i$ be the chosen edge of $D$ joining $z_i$ and $z_{i+1}$.
--
--   1. **Cycle vertices.** $V(C) = \{ z_i : i \in \mathbb{Z}/m \} \subseteq F$.
--
--   2. **Black endpoint.** For an edge $e$, $b(e) = t_N(e)$ if $t_N(e)$ is black, and $b(e) = h_N(e)$ otherwise. If the colouring is proper, then $b(e) = v$ for every black vertex $v$ incident to $e$.
--
--   3. **Black cut.** For $A \subseteq V$, the black cut is the part of the cut $\delta_N(A)$ (the edges with exactly one endpoint in $A$) whose black endpoint lies in $A$:
--   $$
--   \delta^{\bullet}_N(A) = \{ e \in \delta_N(A) : b(e) \in A \}.
--   $$
--
--   4. **Black delta of a dual cycle.** Let $\beta \in \mathbb{R}^V$ be the indicator function of the black vertices and let $\sigma_D(e, z)$ be $1$ if $t_D(e) = z$ and $-1$ otherwise. Then
--   $$
--   \Delta^{\bullet}(C) = \sum_{i \in \mathbb{Z}/m} \bigl( \beta(h_N(e_i)) - \beta(t_N(e_i)) \bigr)\, \sigma_D(e_i, z_i).
--   $$
--   Equivalently, $\Delta^{\bullet}(C) = \sum_{e \in E} (\nabla_N \beta)(e)\, \chi_C(e)$ is the pairing of the $N$-gradient $(\nabla_N\beta)(e) = \beta(h_N(e)) - \beta(t_N(e))$ with the signed cycle flow $\chi_C = \sum_i \sigma_D(e_i, z_i)\, \mathbf{1}_{e_i}$ of $C$ in $D$.
--
--   These quantities record how a cycle of the dual meets the black vertices of the original graph. When $N$ and $D$ are in duality, both are simple, $N$ is cubic, every vertex star of $N$ is a triangle of $D$ and the colouring is proper, and the cycle is compatible with a bijective assignment of the non-root black vertices to the faces away from the root, it is shown elsewhere that $\chi_C = c\, \nabla_N \mathbf{1}_A$ for a vertex set $A$ with $\delta_N(A) = E(C)$ and $c = \pm 1$, that $|\delta_N(A)| = 2\, |\delta^{\bullet}_N(A)| + 3$, and that $\Delta^{\bullet}(C) = -3c$.
--
--   **Formalization Note** `cycleVertices C`, `blackEndpoint black e` with the lemma `blackEndpoint_eq`, `blackCut black A` and `blackDelta black C`, which uses the chosen edges `D.cycleEdge C i` and `D.arcSign`. The colour predicate is decided classically.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/StateDisk.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/StateDisk.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Minimal links, incidence states, and the signed disk identity. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype E] in
def cycleVertices (C : Barnette.CycleCoordinates D.graph) : Finset F :=
  Finset.univ.image C.vertex

omit [Fintype V] [Fintype E] [Fintype F] in
def blackEndpoint (black : V → Prop) (e : E) : V :=
  if black (N.tail e) then N.tail e else N.head e

omit [Fintype V] [Fintype E] [Fintype F] in
lemma blackEndpoint_eq (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    {e : E} {v : V} (hv : black v) (he : N.Incident e v) :
    N.blackEndpoint black e = v := by
  rcases he with ht | hh
  · simp [blackEndpoint,ht,hv]
  · have hnt : ¬black (N.tail e) := fun ht => (hc e).mp ht (hh ▸ hv)
    simp [blackEndpoint,hnt,hh]

omit [Fintype V] [Fintype F] in
def blackCut (black : V → Prop) (A : Finset V) : Finset E :=
  (N.cut A).filter fun e => N.blackEndpoint black e ∈ A

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype E] [Fintype F] in
def blackDelta (black : V → Prop) (C : Barnette.CycleCoordinates D.graph) : ℝ :=
  ∑ i, N.gradient (fun v => if black v then 1 else 0) (D.cycleEdge C i) *
    D.arcSign (D.cycleEdge C i) (C.vertex i)

end
end Barnette.Network

end OAI


