-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_LinearPMap
-- name    : KLSModular_FunctionalInequalities_Energy_Relaxation_LinearPMap
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:25:47.241565+00:00
-- url     : https://prove2.me/theorems/2ed50aac-81dd-45da-b8c8-597e80695a44
-- title:
--   Closability and norm-square energies for partially defined operators
-- statement:
--   A partially defined linear map T between normed spaces is shown closable when the closure of its graph contains no pair with first component zero and nonzero second component; `mem_graph_topologicalClosure_iff` characterizes graph-closure membership by convergent sequences of graph points. `PreEnergy.ofLinearPMap` assigns the finite energy ‖T f‖² on the domain of T, while `PreEnergy.normSqEnergy` assigns the corresponding ENNReal value on the domain and ⊤ outside it. The embedded closure lemmas state that graph-norm cores and larger submodules satisfying the stated hypotheses have the same operator closure.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Energy.Form.QuadraticPreEnergy
--   import FunctionalInequalities.Energy.Relaxation.Basic
--   import Mathlib.Analysis.Convex.Combination
--   import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
--   import Mathlib.Analysis.Normed.Module.Convex
--   import Mathlib.Topology.Algebra.Module.LinearPMap
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def PreEnergy.ofLinearPMap (T : X →ₗ.[ℝ] H) : PreEnergy X where
--     Test := T.domain
--     toAmbient := Subtype.val
--     energy f := ‖T f‖₊ ^ 2
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Energy/Form/QuadraticPreEnergy`](https://prove2.me/theorems/221a35c5-e930-4b6f-81af-de80f2522bf5), [`Energy/Relaxation/Basic`](https://prove2.me/theorems/89c7a615-0c3d-45b2-8b60-f8b981228e0a).
--
--   Theorems in source order:
--
--   - [`exists_mem_of_isClosed_of_frequently_norm_le`](https://prove2.me/theorems/1b83220f-71fb-46f4-9e5b-6d66af812e52)
--   - [`sequentialRelaxation_ofLinearPMap_le`](https://prove2.me/theorems/2e69ddca-a539-4bb5-8778-3f0a7a70ba16)
--   - [`mem_closure_domain_of_frequently`](https://prove2.me/theorems/6c7672bb-0bd5-403e-8d31-fa2f5f6b54ca)
--   - [`sequentialRelaxation_ofLinearPMap_of_notMem`](https://prove2.me/theorems/e3ef01ee-0dd8-45ce-bd89-f6b6714c8f87)
--   - [`sequentialRelaxation_ofLinearPMap_of_mem`](https://prove2.me/theorems/416527b0-b0d6-435c-8137-3e2f122e7c5a)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Relaxation/LinearPMap.lean) · `FunctionalInequalities.Energy.Relaxation.LinearPMap` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Relaxation/LinearPMap.lean#L171-L397 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Relaxation.LinearPMap`, definition bundle `KLSModular_FunctionalInequalities_Energy_Relaxation_LinearPMap`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Algebra.Module.LinearPMap

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


