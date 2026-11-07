-- Prove2me | Definitions.Def_RandOrderCSP_compPartition
-- name    : RandOrderCSP_compPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:07:07.551354+00:00
-- url     : https://prove2.me/theorems/bd781f28-1e0c-4143-87cd-598178a3df06
-- title:
--   Incidence graph, acyclicity and the component partition $\mathcal P_H$
-- statement:
--   The **incidence graph** of $H$ is bipartite on $\mathcal E_H\sqcup\mathcal V_H$, with $j$ joined to each $M_H(j,\ell)$. $H$ is **acyclic**, $\mathrm{Acy}(H)$, if this graph is a forest, and $\mathrm{Acy}_A(H)$ says every component meeting $A\subseteq\mathcal V_H$ is acyclic. The **component partition** $\mathcal P_H$ groups vertices by component, with isolated vertices as singleton blocks.
--
--   The module also defines $H\setminus V^-$, which removes the edges meeting $V^-$ and keeps every vertex, and the boundary operator
--
--   $$(\partial_H\Omega)_i=\sum_{j,\ell:\,M_H(j,\ell)=i}\Omega_{j,\ell},$$
--
--   the transpose of the coboundary.
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), §3.2, p.13; §5.1, pp.22–23; §5.3, p.25

import Mathlib
import Definitions.Def_RandOrderCSP_Hypergraph

namespace RandOrderCSP

namespace Hypergraph

variable {k : ℕ} {V E : Type}

/-- The incidence graph `I_H` (§3.2, p.13): the bipartite graph with left vertex-set `ℰ_H`, right
vertex-set `𝒱_H`, and an edge joining `j` to `M_H(j,ℓ)` for every `j ∈ ℰ_H`, `ℓ ∈ [k]`. -/
def incidenceGraph (H : Hypergraph k V E) : SimpleGraph (E ⊕ V) :=
  SimpleGraph.fromRel fun a b => ∃ j ℓ, a = Sum.inl j ∧ b = Sum.inr (H.M j ℓ)

/-- `Acy(H)`: the incidence graph of `H` is a forest (§3.2, p.13). -/
def Acy (H : Hypergraph k V E) : Prop :=
  H.incidenceGraph.IsAcyclic

/-- `Acy_A(H)` (§5.3, p.25): every component of `H` whose vertex-set intersects `A` is acyclic,
i.e. no cycle of the incidence graph is reachable from a vertex of `A`. -/
def AcyOn (H : Hypergraph k V E) (A : Finset V) : Prop :=
  ∀ v ∈ A, ∀ (w : E ⊕ V) (c : H.incidenceGraph.Walk w w),
    c.IsCycle → ¬ H.incidenceGraph.Reachable (Sum.inr v) w

/-- Two vertices are equivalent when they lie in one component of the incidence graph. -/
def compSetoid (H : Hypergraph k V E) : Setoid V where
  r v w := H.incidenceGraph.Reachable (Sum.inr v) (Sum.inr w)
  iseqv := ⟨fun _ => SimpleGraph.Reachable.refl _, fun h => h.symm, fun h h' => h.trans h'⟩

/-- **The component partition `𝒫_H`** (§5.1, p.22).

Singer, Tulsiani, Velusamy, *A dichotomy theorem for approximating CSPs in random-order streams*,
STOC 2027 submission (manuscript sha256 3aca9d2f…), p.22: "Let C(H) be the collection of
subhypergraphs corresponding to the connected components of the incidence graph of H (including its
singleton isolated-variable components). … The corresponding partition of the vertex set is denoted
𝒫_H := {𝒱_C : C ∈ C(H)}."

**Formalization Note.** Two vertices are in one block iff they are joined in the incidence graph, so
an isolated vertex is a singleton block. This module also holds `incidenceGraph`, `Acy` and `AcyOn`. -/
noncomputable def compPartition [Fintype V] [DecidableEq V] (H : Hypergraph k V E) :
    Finpartition (Finset.univ : Finset V) := by
  classical
  exact Finpartition.ofSetoid H.compSetoid

/-- `H \ V⁻` (§5.1, p.23): the vertex set is unchanged and only the edges incident to `V⁻` are
removed. -/
def deleteVerts [DecidableEq V] (H : Hypergraph k V E) (Vm : Finset V) :
    Hypergraph k V {j : E // ∀ ℓ, H.M j ℓ ∉ Vm} where
  M := fun j => H.M j.1
  row_inj := fun j => H.row_inj j.1

/-- The boundary operator `∂_H : ℤ_q^{ℰ_H×[k]} → ℤ_q^{𝒱_H}` (5.1), p.22:
`(∂_H Ω)_i = ∑_{j, ℓ : M_H(j,ℓ) = i} Ω_{j,ℓ}`. -/
def boundary {q : ℕ} [Fintype E] [DecidableEq V] (H : Hypergraph k V E)
    (Ω : E × Fin k → ZMod q) (i : V) : ZMod q :=
  ∑ p : E × Fin k, if H.M p.1 p.2 = i then Ω p else 0

end Hypergraph

end RandOrderCSP


