-- Prove2me | Definitions.Def_OAI_Combinatorics_InfiniteMatroid_RankDescent
-- name    : OAI_Combinatorics_InfiniteMatroid_RankDescent
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:10:27.747426+00:00
-- url     : https://prove2.me/theorems/eea8b432-ff96-43aa-a93f-e99163d3c940
-- title:
--   Slices of vertex assignments and the enumeration of the two half-rays
-- statement:
--   Notation follows the double-ray definitions. For a type $\alpha$ the ground set is $\mathbb Z\times\alpha$, split into bundles $\{k\}\times\alpha$ that are viewed as the edges of a double ray whose vertices are the integers, the central edge being $-1$. Vertex $n$ carries the inward bundle $\beta(n,0)$ and the outward bundle $\beta(n,1)$, where $\beta(n,0)=n$, $\beta(n,1)=n-1$ for $n<0$ and $\beta(n,0)=n-1$, $\beta(n,1)=n$ for $n\ge0$. For $I\subseteq\mathbb Z\times\alpha$ the vertex assignment $A_n(I)\subseteq\alpha\times\{0,1\}$ is $\{(x,b):(\beta(n,b),x)\in I\}$ for even $n$ and $\{(x,b):(\beta(n,b),x)\notin I\}$ for odd $n$.
--
--   1. **Ray slice.** For $I\subseteq\mathbb Z\times\alpha$, $n\in\mathbb Z$ and $b\in\{0,1\}$,
--   $$S_{n,b}(I)=\{x\in\alpha:\ (x,b)\in A_n(I)\},$$
--   that is, $S_{n,b}(I)=\{x:(\beta(n,b),x)\in I\}$ if $n$ is even and $S_{n,b}(I)=\{x:(\beta(n,b),x)\notin I\}$ if $n$ is odd. So $S_{n,0}(I)$ and $S_{n,1}(I)$ are the inward and outward slices of the assignment at $n$, viewed as subsets of $\alpha$.
--   2. **Half-ray vertices.** For a side bit $\ell\in\{\text{left},\text{right}\}$ and $k\in\mathbb N$,
--   $$r(\ell,k)=\begin{cases}-k-1, & \ell=\text{left},\\ k, & \ell=\text{right},\end{cases}$$
--   so $r(\text{right},\cdot)$ lists the vertices $0,1,2,\dots$ and $r(\text{left},\cdot)$ lists $-1,-2,-3,\dots$; both half-rays start at an endpoint of the central edge.
--
--   These are the coordinates of the rank-descent argument for the two ray matroids on $\mathbb Z\times D$: a hypothetical set $I$ that is independent in the even ray matroid and whose complement is independent in the odd one is followed outward along one half-ray, consecutive vertices $r(\ell,k)$ and $r(\ell,k+1)$ sharing an edge, and the inward slices $S_{r(\ell,k),0}(I)$ are the subsets of $D$ whose ultrafilter membership and ranks are compared from one vertex to the next.
--
--   **Formalization Note** The definitions are `raySlice I n b` (the set `{d | (d,b) ∈ assignment I n}`) and `rayVertex left k` (with `left = true` for the left half-ray), where `Bool` plays the role both of $\{0,1\}$ and of the side bit; parity is tested by `n % 2 = 0`. The file also opens a section declaring the hypotheses of the descent lemmas (a matroid on `α × Bool`, an ultrafilter on `α`, a rank map into a well-founded linear order, and its antitonicity and basis-descent conditions), but no declarations from that section belong to this definition file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/RankDescent.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/RankDescent.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the InfiniteMatroid mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_InfiniteMatroid
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cardinality
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Ideals
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_OrdinalRank
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_FiniteCounting
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Basic
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BlockDensity
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Columns
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cesaro
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_ProbeLimits
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_SparsePerturbation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Interpolation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_LocalBases
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DensityIdeal
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Reservations
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BasisExtension
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Zones
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Separation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Prototype
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_PrototypeExtension
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Matroid
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_TransfiniteConstruction
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DoubleRay

namespace OAI

section
open Set Filter Matroid
namespace InfiniteMatroidCounterexample

def raySlice {α : Type*} (I : Set (ℤ × α)) (n : ℤ) (b : Bool) : Set α :=
  {d | (d,b) ∈ assignment I n}

def rayVertex (left : Bool) (k : ℕ) : ℤ := if left then -(k : ℤ)-1 else (k : ℤ)

section Descent
variable {α β : Type*} [LinearOrder β] [WellFoundedLT β]
variable (Q : Matroid (α × Bool)) (U : Ultrafilter α) (ρ : Set α → β)
variable (hanti : ∀ ⦃X Y : Set α⦄, X ∈ U → Y ∈ U → X ⊆ Y → ρ Y ≤ ρ X)
variable (hbasis : ∀ B, Q.IsBase B → (Prod.mk · false) ⁻¹' B ∈ U →
  ((Prod.mk · true) ⁻¹' B)ᶜ ∈ U ∧ ρ ((Prod.mk · true) ⁻¹' B)ᶜ < ρ ((Prod.mk · false) ⁻¹' B))
include hanti hbasis

end Descent
end InfiniteMatroidCounterexample
end

end OAI


