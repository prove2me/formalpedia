-- Prove2me | Definitions.Def_OAI_Analysis_ForestSpace_FullDual
-- name    : OAI_Analysis_ForestSpace_FullDual
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:06:06.590192+00:00
-- url     : https://prove2.me/theorems/94702fe8-441f-4a60-ba90-02f58a9f92a9
-- title:
--   Coordinate functionals span a dense subspace of the dual of the forest space
-- statement:
--   Let $V$ be a partially ordered set, let $J(V)$ be the completion of the finitely supported functions on $V$ under the disjoint-segment norm, and let $J(V)^*$ be its full continuous dual. For $v\in V$ let $e_v\in J(V)$ be the indicator vector of $v$ and $e_v^*\in J(V)^*$ the coordinate functional, the continuous extension of $u\mapsto u(v)$. For a lower set $H\subseteq V$ let $R_H:J(V)\to J(V)$ be the head projection, the continuous extension of the restriction $u\mapsto u\,\mathbf 1_H$. Let $X(V)\subseteq J(V)^*$ be the norm closure of the linear span of $\{e_v^*:\ v\in V\}$, with the dual norm. Say that $V$ has *finite ancestor sets* if $\{w\in V:\ w\le v\}$ is finite for every $v\in V$. Let $\mathcal F$ be the disjoint forest of the trees of words over $\mathbb{N}$ of length at most $h$, $h\ge1$.
--
--   The file first establishes the following facts.
--
--   - For a finite lower set $H$ and $u\in J(V)$: $\displaystyle R_Hu=\sum_{v\in H}e_v^*(u)\,e_v$.
--   - If $V$ has finite ancestor sets, then for every $u\in J(V)$ and $\varepsilon>0$ there is a finite lower set $H$ with $\|u-R_Hu\|<\varepsilon$; consequently an element $u\in J(V)$ with $e_v^*(u)=0$ for all $v$ is zero.
--   - If $V$ has finite ancestor sets and $J(V)$ is reflexive, then $X(V)=J(V)^*$. Since $\mathcal F$ has finite ancestor sets and $J(\mathcal F)$ is reflexive, $X(\mathcal F)=J(\mathcal F)^*$.
--
--   It then defines:
--
--   1. **Identification with the full dual.** The linear isometric isomorphism
--   $$
--   X(\mathcal F)\ \xrightarrow{\ \cong\ }\ J(\mathcal F)^*
--   $$
--   given by the inclusion of the closed coordinate span, which is onto by the previous fact.
--   2. **Finite coordinate map.** For a finite set $H\subseteq\mathcal F$, the continuous linear map
--   $$
--   \pi_H:\ J(\mathcal F)^*\to\mathbb{R}^H,\qquad \pi_H(x)=\bigl(x(e_v)\bigr)_{v\in H}.
--   $$
--
--   The identification transfers everything proved for the coordinate completion $X(V)$ (head and tail projections, finite-coordinate kernels, coordinate bounds) to the full dual $J(\mathcal F)^*$, which is the space studied in the main theorem; the kernels of the maps $\pi_H$ are closed finite-codimensional subspaces of $J(\mathcal F)^*$.
--
--   **Formalization Note** $X(V)$ is the subtype of `coordinateSubspace V`, the head projection is `headJ H hH`, and the identification is `fullDualEquiv`, built with `LinearIsometryEquiv.ofSurjective` from the subtype inclusion; the finite coordinate map is `mainFiniteCoordinates H`. The hypothesis on ancestor sets is `(Set.Iic v).Finite` for all `v`, and reflexivity means surjectivity of the canonical map into the bidual.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/FullDual.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/FullDual.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ForestSpace mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar
import Definitions.Def_OAI_Analysis_ForestSpace_Projections
import Definitions.Def_OAI_Analysis_ForestSpace_Renorming
import Definitions.Def_OAI_Analysis_ForestSpace_Coordinates
import Definitions.Def_OAI_Analysis_ForestSpace_Trees
import Definitions.Def_OAI_Analysis_ForestSpace_Reflexivity
import Definitions.Def_OAI_Analysis_ForestSpace_Components

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section CoordinateDensity
variable {V : Type} [PartialOrder V]

 theorem headJ_finite_eq_sum (H : Finset V) (hH : IsLowerSet (H : Set V)) (u : J V) :
    headJ (H : Set V) hH u = ∑ v ∈ H, eStar v u • e v := by
  refine UniformSpace.Completion.induction_on u (isClosed_eq (headJ (H : Set V) hH).continuous
    (continuous_finsetSum _ (fun v hv => (eStar v).continuous.smul continuous_const))) ?_
  intro f
  rw [headJ_coe,TestVector.cut_finite_eq_sum]
  change (UniformSpace.Completion.toComplL : TestVector V →L[ℝ] J V) (∑ v ∈ H, f v • TestVector.single v 1) = _
  simp only [map_sum,map_smul,eStar_coe]
  rfl

 theorem exists_headJ_approx (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (u : J V) (ε : ℝ) (hε : 0 < ε) :
    ∃ H : Finset V, ∃ hH : IsLowerSet (H : Set V), ‖u-headJ (H : Set V) hH u‖ < ε := by
  obtain ⟨z,hz,hclose⟩ := Metric.mem_closure_iff.mp
    (UniformSpace.Completion.denseRange_coe u) ε hε
  obtain ⟨f,rfl⟩ := hz
  obtain ⟨H,hSH,hH⟩ := exists_finite_lower_hull hAnc f.toFinsupp.support
  have hf : SupportedOn f (H : Set V) := by
    intro v hv
    exact Finsupp.notMem_support_iff.mp (fun hs => hv (hSH hs))
  have he : tailJ (H : Set V) hH (f : J V) = 0 := by
    change (f : J V) - headJ (H : Set V) hH (f : J V) = 0
    rw [headJ_coe,TestVector.cut_eq_self hf,sub_self]
  have hn := norm_tailJ_le (H : Set V) hH (u - (f : J V))
  rw [map_sub,he,sub_zero] at hn
  refine ⟨H,hH,hn.trans_lt ?_⟩
  simpa only [dist_eq_norm] using hclose

 theorem eq_zero_of_coordinates_zero (hAnc : ∀ v : V, (Set.Iic v).Finite)
    {u : J V} (hu : ∀ v, eStar v u = 0) : u = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨H,hH,hh⟩ := exists_headJ_approx hAnc u ε hε
  have he : headJ (H : Set V) hH u = 0 := by
    rw [headJ_finite_eq_sum]
    simp only [hu,zero_smul,Finset.sum_const_zero]
  simpa only [he,sub_zero,zero_add] using hh

 theorem coordinateSubspace_eq_top_of_reflexive (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (hRefl : Reflexive (J V)) : coordinateSubspace V = ⊤ := by
  let M := coordinateSubspace V
  let : IsClosed (M : Set (FullDual V)) := Submodule.isClosed_topologicalClosure _
  let : NormedAddCommGroup ((FullDual V) ⧸ M) := inferInstance
  let : NormedSpace ℝ ((FullDual V) ⧸ M) := inferInstance
  apply top_unique
  intro x hx
  change x ∈ M
  apply (Submodule.Quotient.mk_eq_zero M).mp
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ)
  intro ψ
  obtain ⟨u,hu⟩ := hRefl (ψ.comp M.mkQL)
  have hz : ∀ v, eStar v u = 0 := by
    intro v
    have hv : eStar v ∈ M := Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨v,rfl⟩)
    have hh := congrArg (fun z : StrongDual ℝ (FullDual V) => z (eStar v)) hu
    change eStar v u = ψ (M.mkQ (eStar v)) at hh
    simpa only [Submodule.mkQ_apply,(Submodule.Quotient.mk_eq_zero M).mpr hv,map_zero] using hh
  have hu0 := eq_zero_of_coordinates_zero hAnc hz
  have hh := congrArg (fun z : StrongDual ℝ (FullDual V) => z x) hu
  change x u = ψ (M.mkQ x) at hh
  simpa only [Submodule.mkQ_apply,hu0,map_zero] using hh.symm

 theorem forest_coordinateSubspace_eq_top : coordinateSubspace Vertex = ⊤ :=
  coordinateSubspace_eq_top_of_reflexive Vertex.finiteAncestors reflexive_forest_J

noncomputable def fullDualEquiv : X Vertex ≃ₗᵢ[ℝ] FullDual Vertex :=
  LinearIsometryEquiv.ofSurjective (coordinateSubspace Vertex).subtypeₗᵢ (by
    intro x
    exact ⟨⟨x,by rw [forest_coordinateSubspace_eq_top]; trivial⟩,rfl⟩)

end CoordinateDensity

section MainNorm

noncomputable def mainFiniteCoordinates (H : Finset Vertex) : FullDual Vertex →L[ℝ] (H → ℝ) :=
  ContinuousLinearMap.pi (fun v : H => (ContinuousLinearMap.apply ℝ ℝ) (e (v : Vertex)))

end MainNorm

end

end ForestSpace

end OAI


