-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
-- name    : KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:38:35.947998+00:00
-- url     : https://prove2.me/theorems/5edb2f67-d843-4c10-af6f-bc37dc5528fb
-- title:
--   Closability and norm-square energies for partially defined operators
-- statement:
--   A partially defined linear map T between normed spaces is shown closable when the closure of its graph contains no pair with first component zero and nonzero second component; `mem_graph_topologicalClosure_iff` characterizes graph-closure membership by convergent sequences of graph points. `PreEnergy.ofLinearPMap` assigns the finite energy ‖T f‖² on the domain of T, while `PreEnergy.normSqEnergy` assigns the corresponding ENNReal value on the domain and ⊤ outside it. The embedded closure lemmas state that graph-norm cores and larger submodules satisfying the stated hypotheses have the same operator closure.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Relaxation/LinearPMap.lean#L171-L397 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Relaxation.LinearPMap`, definition bundle `KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section
open Filter Topology Set
namespace FunctionalInequalities
namespace Energy
section Closability
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
/-- A partially defined operator is closable as soon as the closure of its graph contains no
pair `(0, y)` with `y ≠ 0`. -/
theorem isClosable_of_graph_closure_snd_eq_zero (T : X →ₗ.[ℝ] H)
    (h : ∀ p ∈ T.graph.topologicalClosure, p.1 = 0 → p.2 = 0) : T.IsClosable :=
  ⟨T.graph.topologicalClosure.toLinearPMap, (Submodule.toLinearPMap_graph_eq _ h).symm⟩
/-- Membership in the closure of the graph is sequential convergence of graph points. -/
theorem mem_graph_topologicalClosure_iff (T : X →ₗ.[ℝ] H) (p : X × H) :
    p ∈ T.graph.topologicalClosure ↔
      ∃ f : ℕ → T.domain, Tendsto (fun n ↦ ((f n : X), T (f n))) atTop (𝓝 p) := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, mem_closure_iff_seq_limit]
  constructor
  · rintro ⟨q, hq, hqp⟩
    choose f hf using fun n ↦ (T.mem_graph_iff.mp (hq n))
    refine ⟨f, ?_⟩
    have : (fun n ↦ ((f n : X), T (f n))) = q := by
      funext n
      exact Prod.ext (hf n).1 (hf n).2
    rwa [this]
  · rintro ⟨f, hf⟩
    exact ⟨fun n ↦ ((f n : X), T (f n)), fun n ↦ T.mem_graph (f n), hf⟩
/-- If every graph point of `T` is a limit of graph points of the restriction of `T` to a
submodule `S` of its domain, then the restriction has the same closure as `T`. -/
theorem IsClosable.closure_domRestrict_eq {T : X →ₗ.[ℝ] H} (hT : T.IsClosable)
    {S : Submodule ℝ X} (hS : S ≤ T.domain)
    (hcore : ∀ f : T.domain, ∃ s : ℕ → S,
      Tendsto (fun n ↦ ((s n : X), T ⟨s n, hS (s n).2⟩)) atTop (𝓝 ((f : X), T f))) :
    (T.domRestrict S).closure = T.closure := by
  have hle : T.domRestrict S ≤ T := LinearPMap.domRestrict_le
  have hres : (T.domRestrict S).IsClosable := hT.leIsClosable hle
  apply le_antisymm (hT.closure_mono hle)
  apply LinearPMap.le_of_le_graph
  rw [← hT.graph_closure_eq_closure_graph, ← hres.graph_closure_eq_closure_graph]
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
  intro q hq
  obtain ⟨f, rfl⟩ := T.mem_graph_iff'.mp hq
  obtain ⟨s, hs⟩ := hcore f
  rw [mem_graph_topologicalClosure_iff]
  have hmem : ∀ n, (s n : X) ∈ (T.domRestrict S).domain := fun n ↦
    ⟨(s n).2, hS (s n).2⟩
  refine ⟨fun n ↦ ⟨s n, hmem n⟩, ?_⟩
  refine hs.congr fun n ↦ ?_
  refine Prod.ext rfl ?_
  exact (LinearPMap.domRestrict_apply rfl).symm
/-- Enlarging a graph-norm core inside the domain does not change the closure. -/
theorem IsClosable.closure_domRestrict_eq_of_le {T : X →ₗ.[ℝ] H} (hT : T.IsClosable)
    {S S' : Submodule ℝ X} (hSS' : S ≤ S') (_hS' : S' ≤ T.domain)
    (hS : (T.domRestrict S).closure = T.closure) :
    (T.domRestrict S').closure = T.closure := by
  have h1 : T.domRestrict S ≤ T.domRestrict S' := by
    refine ⟨fun x hx ↦ ⟨hSS' hx.1, hx.2⟩, ?_⟩
    intro x y hxy
    have hx : (x : X) ∈ S ⊓ T.domain := x.2
    have e1 : T.domRestrict S x = T ⟨x, hx.2⟩ :=
      LinearPMap.domRestrict_apply (x := x) (y := ⟨x, hx.2⟩) rfl
    have e2 : T.domRestrict S' y = T ⟨x, hx.2⟩ :=
      LinearPMap.domRestrict_apply (x := y) (y := ⟨x, hx.2⟩) hxy.symm
    rw [e1, e2]
  have h2 : T.domRestrict S' ≤ T := LinearPMap.domRestrict_le
  apply le_antisymm (hT.closure_mono h2)
  rw [← hS]
  exact (hT.leIsClosable h2).closure_mono h1
end Closability
section PreEnergy
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
/-- The finite pre-energy `f ↦ ‖T f‖²` of a partially defined operator, realized by inclusion of
the domain. -/
def PreEnergy.ofLinearPMap (T : X →ₗ.[ℝ] H) : PreEnergy X where
  Test := T.domain
  toAmbient := Subtype.val
  energy f := ‖T f‖₊ ^ 2
namespace PreEnergy
variable (T : X →ₗ.[ℝ] H)
instance : AddCommGroup (ofLinearPMap T).Test := inferInstanceAs (AddCommGroup T.domain)
instance : Module ℝ (ofLinearPMap T).Test := inferInstanceAs (Module ℝ T.domain)
omit [CompleteSpace H] in
@[simp]
theorem ofLinearPMap_toAmbient (f : T.domain) : (ofLinearPMap T).toAmbient f = (f : X) := rfl
omit [CompleteSpace H] in
@[simp]
theorem ofLinearPMap_energy (f : T.domain) : (ofLinearPMap T).energy f = ‖T f‖₊ ^ 2 := rfl
open Classical in
/-- The extended energy `x ↦ ‖S x‖²` of a partially defined operator, infinite off its domain. -/
def normSqEnergy {H' : Type*} [NormedAddCommGroup H'] [NormedSpace ℝ H'] (S : X →ₗ.[ℝ] H') :
    Functional X where
  toFun x := if h : x ∈ S.domain then ((‖S ⟨x, h⟩‖₊ ^ 2 : NNReal) : ENNReal) else ⊤
end PreEnergy
end PreEnergy
end Energy
end FunctionalInequalities


