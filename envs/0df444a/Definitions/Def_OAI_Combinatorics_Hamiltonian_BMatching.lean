-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_BMatching
-- name    : OAI_Combinatorics_Hamiltonian_BMatching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:43:32.72223+00:00
-- url     : https://prove2.me/theorems/355b4f1e-b329-4ca2-b97c-4bb3232df4a3
-- title:
--   Gadget graph for two-factors of a bipartite relation and labelled two-factor data
-- statement:
--   Let $A$ and $B$ be finite sets and $R\subseteq A\times B$ a relation, viewed as a bipartite graph with sides $A$ and $B$. Write $\{0,1\}$ for a two-element index set and $\sqcup$ for disjoint union.
--
--   1. **Incidences.** $I_R=\{(a,b)\in A\times B:(a,b)\in R\}$ is the set of edges of the bipartite graph; for $e=(a,b)\in I_R$ write $e_1=a$ and $e_2=b$.
--   2. **The two sides of the gadget.** $\mathcal{L}_R=(A\times\{0,1\})\sqcup I_R$ and $\mathcal{R}_R=(B\times\{0,1\})\sqcup I_R$: each vertex of $A$, respectively $B$, appears twice, and each edge appears once on each side.
--   3. **The gadget relation.** $\Gamma_R\subseteq\mathcal{L}_R\times\mathcal{R}_R$ is given by
--   $$
--   (a,k)\ \Gamma_R\ e\iff e_1=a,\qquad e\ \Gamma_R\ (b,k)\iff e_2=b,\qquad e\ \Gamma_R\ f\iff e=f,
--   $$
--   for $a\in A$, $b\in B$, $k\in\{0,1\}$ and $e,f\in I_R$ (the left argument taken in $\mathcal{L}_R$ and the right one in $\mathcal{R}_R$), while no $(a,k)$ is related to any $(b,k')$.
--   4. **Two-factor data.** A two-factor datum for $R$ consists of injective maps $\lambda:A\times\{0,1\}\to I_R$ and $\mu:B\times\{0,1\}\to I_R$ with
--   $$
--   \lambda(a,k)_1=a,\qquad \mu(b,k)_2=b\qquad(a\in A,\ b\in B,\ k\in\{0,1\}),
--   $$
--   such that $\lambda$ and $\mu$ have the same image $S\subseteq I_R$. Equivalently, $S$ is a set of edges in which every vertex of $A$ and every vertex of $B$ has degree exactly $2$, together with a labelling by $0$ and $1$ of the two edges of $S$ at each vertex.
--
--   The gadget turns the degree-two constraint into a matching problem. In a perfect matching of the bipartite graph $\Gamma_R$, each edge $e$ is either matched to its own copy, or its copy in $\mathcal{R}_R$ is matched to a copy of $e_1$ and its copy in $\mathcal{L}_R$ to a copy of $e_2$; the edges of the second kind form a subgraph with all degrees equal to $2$, and the copies they are matched to give a two-factor datum. In the module this reduction, combined with Hall's marriage theorem, is used to produce pairs of partner incidence states.
--
--   **Formalization Note** `Inc`, `Left` and `Right` are abbreviations for a subtype of `A × B` and for sum types; `gadget` is defined by pattern matching on the sum types, and `FactorData` stores $\lambda$ and $\mu$ as embeddings `A × Fin 2 ↪ Inc R` and `B × Fin 2 ↪ Inc R` together with the equality of their ranges.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/BMatching.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/BMatching.lean by skeleton subtraction
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

namespace OAI

/-! Integral flows, capacitated matchings, and incidence-state pairs. -/

namespace Barnette.BMatching
noncomputable section
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]

abbrev Inc (R : A → B → Prop) := {z : A × B // R z.1 z.2}
abbrev Left (R : A → B → Prop) := (A × Fin 2) ⊕ Inc R
abbrev Right (R : A → B → Prop) := (B × Fin 2) ⊕ Inc R

def gadget (R : A → B → Prop) : Left R → Right R → Prop
  | .inl (a,_), .inr e => e.val.1 = a
  | .inr e, .inl (b,_) => e.val.2 = b
  | .inr e, .inr f => e = f
  | _, _ => False

end
end Barnette.BMatching
namespace Barnette.BMatching
noncomputable section
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]

structure FactorData (R : A → B → Prop) where
  left : A × Fin 2 ↪ Inc R
  right : B × Fin 2 ↪ Inc R
  left_coord : ∀ a k, (left (a,k)).val.1 = a
  right_coord : ∀ b k, (right (b,k)).val.2 = b
  same_range : Set.range left = Set.range right

end
end Barnette.BMatching
namespace Barnette.TriangleSystem.State
variable {A V : Type*} {T : TriangleSystem A V} {X : Set V}
end Barnette.TriangleSystem.State

namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D)

end
end Barnette.Network.ColoredDual

end OAI


