-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_SquareGrid
-- name    : OAI_Combinatorics_Hamiltonian_SquareGrid
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:52:24.162988+00:00
-- url     : https://prove2.me/theorems/a2d96197-d538-43d1-a4e0-4acd4cbed33b
-- title:
--   Square lattice graph on $\mathbb{Z}^2$ and the grid cells meeting a planar set
-- statement:
--   1. **The square lattice.** The graph on $\mathbb{Z}^2$ in which $a=(a_1,a_2)$ and $b=(b_1,b_2)$ are adjacent iff they differ by $1$ in exactly one coordinate:
--   $$
--   a\sim b\iff\bigl(|a_1-b_1|=1\text{ and }a_2=b_2\bigr)\ \text{or}\ \bigl(|a_2-b_2|=1\text{ and }a_1=b_1\bigr).
--   $$
--   2. **Cells.** For $\delta\in\mathbb{R}$ and $z=(z_1,z_2)\in\mathbb{Z}^2$, the cell
--   $$
--   Q_\delta(z)=[\delta z_1,\ \delta(z_1+1)]\times[\delta z_2,\ \delta(z_2+1)]\subseteq\mathbb{R}^2;
--   $$
--   for $\delta>0$ this is the closed square of side $\delta$ with lower-left corner $\delta z$.
--   3. **Cells meeting a set.** For $K\subseteq\mathbb{R}^2$,
--   $$
--   \mathcal{C}_\delta(K)=\{z\in\mathbb{Z}^2:\ Q_\delta(z)\cap K\ne\emptyset\}.
--   $$
--
--   For $\delta>0$ the cells cover the plane, and the module shows that $\mathcal{C}_\delta(K)$ is finite for compact $K$, induces a connected subgraph of the lattice when $K$ is moreover connected, and that two sets whose open $\varepsilon$-neighbourhoods are disjoint have disjoint cell sets when $\delta<\varepsilon$. This discretizes compact connected pieces of a plane drawing into connected finite lattice corridors.
--
--   **Formalization Note** No sign condition on $\delta$ is built into the definitions: for $\delta<0$ every cell is empty and for $\delta=0$ every cell is the single point $(0,0)$; the results about cells assume $\delta>0$. Adjacency is written as $a_1+1=b_1$ or $b_1+1=a_1$ (and similarly for the second coordinate), and the Lean names are `SquareGrid.graph`, `SquareGrid.cell` and `SquareGrid.cells`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/SquareGrid.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/SquareGrid.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPolynomials
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Forest
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Contraction
import Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorDuality
import Definitions.Def_OAI_Combinatorics_Hamiltonian_BMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Matching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ForestMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ThreeCuts
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Gluing
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Traces

namespace OAI

/-! Ordinary square cells and connected finite lattice corridors. -/

namespace Barnette.SquareGrid

noncomputable section

def graph : SimpleGraph (ℤ × ℤ) where
  Adj a b := ((a.1 + 1 = b.1 ∨ b.1 + 1 = a.1) ∧ a.2 = b.2) ∨
    ((a.2 + 1 = b.2 ∨ b.2 + 1 = a.2) ∧ a.1 = b.1)
  symm := ⟨by
    intro a b h
    rcases h with ⟨h, he⟩ | ⟨h, he⟩
    · exact Or.inl ⟨h.symm, he.symm⟩
    · exact Or.inr ⟨h.symm, he.symm⟩⟩
  loopless := ⟨by intro a h; rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega⟩

def cell (δ : ℝ) (z : ℤ × ℤ) : Set (ℝ × ℝ) :=
  Set.Icc (δ * z.1) (δ * ((z.1 : ℝ) + 1)) ×ˢ
    Set.Icc (δ * z.2) (δ * ((z.2 : ℝ) + 1))

def cells (δ : ℝ) (K : Set (ℝ × ℝ)) : Set (ℤ × ℤ) :=
  {z | (cell δ z ∩ K).Nonempty}

end
end Barnette.SquareGrid
namespace Barnette.SquareGrid

noncomputable section

end
end Barnette.SquareGrid

end OAI


