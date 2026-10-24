-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointClosure
-- name    : KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointClosure
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:09:57.212285+00:00
-- url     : https://prove2.me/theorems/b0c09c66-27d8-4840-97aa-abb785e7a8b2
-- title:
--   Closure and graph-limit identities for partial operators
-- statement:
--   The bundle records three Hilbert-space facts for partially defined operators: `apply_sub_of_eq_sub` evaluates an operator on a difference when separate domain witnesses are supplied; `exists_mem_domain_apply_eq_of_tendsto` states that a closed operator contains the limit of convergent graph points; and `inner_eq_inner_closure_apply` extends a weak inner-product identity from a closable operator to its closure. No measure, semigroup, or differential operator is involved.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/AdjointClosure.lean#L37-L85 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.AdjointClosure`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointClosure`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointComp
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Topology.Algebra.Module.LinearPMap

noncomputable section
open scoped LinearPMap RealInnerProductSpace
namespace FunctionalInequalities
namespace Analysis
namespace Semigroup
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
/-- `S` on a difference, with all three membership witnesses supplied separately.  Only proof
irrelevance and `LinearPMap.map_sub` are involved; the value is given by a hypothesis `z = x - y`
so that it can be produced by a rewrite without disturbing the witnesses. -/
theorem apply_sub_of_eq_sub {S : H₀ →ₗ.[ℝ] H₁} {x y z : H₀} (hx : x ∈ S.domain)
    (hy : y ∈ S.domain) (hz : z ∈ S.domain) (h : z = x - y) :
    S ⟨z, hz⟩ = S ⟨x, hx⟩ - S ⟨y, hy⟩ := by
  subst h
  exact S.map_sub ⟨x, hx⟩ ⟨y, hy⟩
/-- A closed operator absorbs graph limits: if `x n ∈ D(S)` for every `n`, `x n → a` in `H₀` and
`S (x n) → b` in `H₁`, then `a ∈ D(S)` and `S a = b`.

`LinearPMap.IsClosed` is closedness of the graph as a subset of `H₀ × H₁`, so this is
`IsClosed.mem_of_tendsto` applied to the pair sequence, followed by `LinearPMap.mem_graph_iff`
and proof irrelevance of the membership witness. Completeness is not used: the limits are
hypotheses. -/
theorem exists_mem_domain_apply_eq_of_tendsto {S : H₀ →ₗ.[ℝ] H₁} (hS : S.IsClosed)
    {x : ℕ → H₀} (hx : ∀ n, x n ∈ S.domain) {a : H₀} {b : H₁}
    (hxa : Filter.Tendsto x Filter.atTop (nhds a))
    (hSb : Filter.Tendsto (fun n => S ⟨x n, hx n⟩) Filter.atTop (nhds b)) :
    ∃ h : a ∈ S.domain, S ⟨a, h⟩ = b := by
  have hgraph : (a, b) ∈ S.graph :=
    hS.mem_of_tendsto (hxa.prodMk_nhds hSb)
      (Filter.Eventually.of_forall fun n => S.mem_graph ⟨x n, hx n⟩)
  obtain ⟨y, hy1, hy2⟩ := S.mem_graph_iff.mp hgraph
  have hy1' : (y : H₀) = a := hy1
  have hy2' : S y = b := hy2
  have hmem : a ∈ S.domain := by rw [← hy1']; exact y.2
  refine ⟨hmem, ?_⟩
  rw [show (⟨a, hmem⟩ : S.domain) = y from Subtype.ext hy1'.symm]
  exact hy2'
/-- A weak identity `⟪w, x⟫ = ⟪v, T x⟫` valid on the domain of a closable operator `T` persists on
the domain of its closure. -/
theorem inner_eq_inner_closure_apply {T : H₀ →ₗ.[ℝ] H₁} (hT : T.IsClosable) {w : H₀} {v : H₁}
    (h : ∀ x : T.domain, ⟪w, (x : H₀)⟫ = ⟪v, T x⟫) (x : T.closure.domain) :
    ⟪w, (x : H₀)⟫ = ⟪v, T.closure x⟫ := by
  have hmem : ((x : H₀), T.closure x) ∈ T.graph.topologicalClosure := by
    rw [hT.graph_closure_eq_closure_graph]
    exact T.closure.mem_graph x
  have hclosed : IsClosed {p : H₀ × H₁ | ⟪w, p.1⟫ = ⟪v, p.2⟫} :=
    isClosed_eq (continuous_const.inner continuous_fst) (continuous_const.inner continuous_snd)
  have hsub : (T.graph : Set (H₀ × H₁)) ⊆ {p : H₀ × H₁ | ⟪w, p.1⟫ = ⟪v, p.2⟫} := by
    intro p hp
    obtain ⟨y, rfl⟩ := T.mem_graph_iff'.mp hp
    exact h y
  have hcl := closure_minimal hsub hclosed
  rw [← Submodule.topologicalClosure_coe] at hcl
  exact hcl hmem
variable [CompleteSpace H₀]
end Semigroup
end Analysis
end FunctionalInequalities


