-- Prove2me | Definitions.Def_OAIQWMTW002
-- name    : OAIQWMTW002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T02:56:32.399977+00:00
-- url     : https://prove2.me/theorems/e376846b-b107-4080-a6b5-1968a5a82fcf
-- title:
--   OpenAI weak MTW split: definitions bundle OAIQWMTW002
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWGlobalSupport.current_main_convexity`. That theorem says that on a compact connected Riemannian manifold of dimension at least two satisfying the weak Ma–Trudinger–Wang condition, every tangent injectivity domain is convex (Villani's conjecture in this setting).
--
--   The bundle holds OpenAI's Lean definitions, structures and predicates from the modules `Coordinates_CostEndpointAction`, `Coordinates_FocalCoordinates`, `Coordinates_TangentCoordinates`, `Domains_Definitions`, `Geodesics_BundleMinimizerCompactness`, `Geodesics_IntrinsicExp`, `Geodesics_IntrinsicUniqueness`, `Geodesics_NonconjugateBranches`, `Support_ActiveCollisionExclusion`, `Support_ActiveRepresentation`, `Support_ActiveSupports`, `Support_CollisionBranches`, `Support_CollisionTangentCoordinates`, `Support_FiniteActiveGraph`, `Support_TangentHullCompact`, `Support_TotalInterior`, `Variations_ActionHessian`, `Variations_MTWConcavity`, `Variations_RadialSplitAction` of `lean/OAI/Geometry/WeakMTW` (OpenAI, *Global Support and Convex Injectivity Domains under Weak MTW*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0). They are ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas their bodies use. It imports no other bundle of this split.
--
--   Its definitions build on the published goal bundle `Def_WeakMTWGlobalSupport` (the model space, `exp`, the cost and the injectivity domains). Among them:
--   - charts of the tangent bundle and the cost in charts (`stateChart`, `chartCost`, `tangentChartLinear`, `verticalCoordinates`, `tangentCoordinateEquiv`);
--   - minimizing velocities and nonconjugacy (`minimizingDomain`, `totalMinimizingSet`, `Nonconjugate`, `baseExp`);
--   - the diagonal action Hessian, the initial cost and the radial split action (`actionHessianDiag`, `initialCost`, `radialSplitAction`);
--   - finite cost potentials with their active velocities, hulls, graphs and supports (`finitePotential`, `activeVelocities`, `activeHull`, `activeGraph`, `activeHullGraph`, `ActiveIndex`, `ActiveRepresentation`, `activeSupport`, `ActivePoint`, `activeProjection`, `tangentHull`, `totalInterior`).
--
--   The theorems the definitions do not need are proved in the solutions of this split. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/WeakMTW at commit adc7f12

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_CostEndpointAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M]

 def chartCost (x : M) (q : Model n × Model n) : ℝ :=
   cost ((chartAt (Model n) x).symm q.1) ((chartAt (Model n) x).symm q.2)

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_IntrinsicUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

omit [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M] in
theorem tangentBundle_t2Space : T2Space (TangentBundle 𝓘(ℝ, E) M) := by
  apply t2Space_iff_disjoint_nhds.mpr
  intro p q hpq
  by_cases hb : p.proj = q.proj
  · let e := trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ, E) x) p.proj
    have hp : p ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
    have hq : q ∈ e.source := e.mem_source.mpr (by
      rw [← hb]
      exact mem_baseSet_trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ, E) x) p.proj)
    have he : e p ≠ e q := fun h => hpq (e.toOpenPartialHomeomorph.injOn hp hq h)
    exact Filter.disjoint_of_map ((disjoint_nhds_nhds.mpr he).mono
      (e.toOpenPartialHomeomorph.continuousAt hp) (e.toOpenPartialHomeomorph.continuousAt hq))
  · exact Filter.disjoint_of_map ((disjoint_nhds_nhds.mpr hb).mono
      (FiberBundle.continuous_proj E (fun x : M => TangentSpace 𝓘(ℝ, E) x)).continuousAt
      (FiberBundle.continuous_proj E (fun x : M => TangentSpace 𝓘(ℝ, E) x)).continuousAt)

end
end RiemannianLocal

end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_TangentCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

 def stateChart (x : M) : OpenPartialHomeomorph (TangentBundle 𝓘(ℝ, E) M) (E × E) :=
  chartAt (ModelProd E E) (⟨x,0⟩ : TangentBundle 𝓘(ℝ, E) M)

end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Domains_Definitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open scoped Manifold ContDiff Topology
open Set Filter Manifold Bundle

namespace WeakMTW

noncomputable section

variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M]

def minimizingDomain (x : M) : Set (TangentSpace (model n) x) :=
  {v | dist x (exp x v) = ‖v‖}

end

end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_IntrinsicExp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def mulState (a : ℝ) (p : TangentBundle 𝓘(ℝ, E) M) : TangentBundle 𝓘(ℝ, E) M :=
  ⟨p.1, a • p.2⟩

end
end RiemannianLocal

end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_BundleMinimizerCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def totalMinimizingSet : Set (TangentBundle (model n) M) :=
  {p | dist p.1 (exp p.1 p.2) = ‖p.2‖}

 def baseExp (p : TangentBundle (model n) M) : M × M := (p.1,exp p.1 p.2)

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_MTWConcavity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold

namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def actionHessianDiag (x : M) (v ξ : TangentSpace (model n) x) : ℝ :=
  deriv (fun t : ℝ => deriv (fun t' : ℝ => cost (exp x (t'•ξ)) (exp x v)) t) 0

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_ActionHessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def initialCost (x y : M) (a : Model n) : ℝ := cost ((chartAt (Model n) x).symm a) y

 def tangentChartLinear (x : M) : TangentSpace (model n) x →L[ℝ] Model n :=
   mfderiv (model n) (model n) (chartAt (Model n) x) x

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_FocalCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]

 def verticalCoordinates (x : M) (v : TangentSpace (model n) x) : Model n × Model n :=
   (chartAt (Model n) x x,tangentChartLinear x v)

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_NonconjugateBranches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def Nonconjugate (x : M) (v : TangentSpace (model n) x) : Prop :=
    Function.Injective (fderiv ℝ (fun w => chartAt (Model n) (exp x v) (exp x w)) v)

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Support_FiniteActiveGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]
  {ι : Type*} [Fintype ι] [Nonempty ι]

 def finitePotential (y : ι → M) (h : ι → ℝ) (x : M) : ℝ :=
    Finset.univ.sup' Finset.univ_nonempty (fun i => h i - cost x (y i))

 def activeVelocities (y : ι → M) (h : ι → ℝ) (x : M) : Set (TangentSpace (model n) x) :=
    {a | a ∈ minimizingDomain x ∧ ∃ i, exp x a = y i ∧ finitePotential y h x = h i-cost x (y i)}

 def activeHull (y : ι → M) (h : ι → ℝ) (x : M) : Set (TangentSpace (model n) x) :=
    convexHull ℝ (activeVelocities y h x)

 def activeGraph (y : ι → M) (h : ι → ℝ) : Set (TangentBundle (model n) M) :=
    {p | p.2 ∈ activeVelocities y h p.1}

 def activeHullGraph (y : ι → M) (h : ι → ℝ) : Set (TangentBundle (model n) M) :=
    {p | p.2 ∈ activeHull y h p.1}

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Support_CollisionTangentCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M]

 def tangentCoordinateEquiv (x p : M) (hp : p ∈ (chartAt (Model n) x).source) :
    TangentSpace (model n) p ≃L[ℝ] Model n :=
  (trivializationAt (Model n) (TangentSpace (model n)) x).continuousLinearEquivAt ℝ p
    (by simpa only [TangentBundle.trivializationAt_baseSet] using hp)

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Support_ActiveRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]
  {ι : Type*} [Fintype ι] [Nonempty ι]

 abbrev ActiveIndex (n : ℕ) := Fin (Module.finrank ℝ (Model n)+1)

 structure ActiveRepresentation (y : ι → M) (h : ι → ℝ) (p : TangentBundle (model n) M) where
  a : ActiveIndex n → TangentSpace (model n) p.1
  θ : ActiveIndex n → ℝ
  active : ∀ i, a i ∈ activeVelocities y h p.1
  nonneg : ∀ i, 0 ≤ θ i
  sum_one : ∑ i, θ i = 1
  bary : ∑ i, θ i • a i = p.2

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Support_ActiveSupports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]
  {ι : Type*} [Fintype ι] [Nonempty ι]

 def activeSupport (y : ι → M) (h : ι → ℝ) (p : M)
    (a : TangentSpace (model n) p) (ℓ : ℝ) (z : M) : ℝ :=
    finitePotential y h p + (cost p (exp p (ℓ•a))-cost z (exp p (ℓ•a))) / ℓ

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Support_CollisionBranches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]
  {ι : Type*} [Fintype ι] [Nonempty ι]

 def scaledPoleValue (y : ι → M) (h : ι → ℝ) (s : ℝ) (p : TangentBundle (model n) M) : ℝ :=
  ‖s•p.2‖^2/2+s*finitePotential y h p.1

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_RadialSplitAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def radialSplitAction (x : M) (a : TangentSpace (model n) x) (s t : ℝ)
    (q : Model n × TangentSpace (model n) x) : ℝ :=
    cost ((chartAt (Model n) x).symm q.1) (exp x (s•a+q.2)) / s +
    cost (exp x (s•a+q.2)) (exp x (t•a)) / (t-s) -
    cost ((chartAt (Model n) x).symm q.1) (exp x (t•a)) / t

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Support_ActiveCollisionExclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]
  {ι : Type*} [Fintype ι] [Nonempty ι]

 abbrev ActivePoint (y : ι → M) (h : ι → ℝ) := ↥(activeHullGraph (n := n) y h)

 def activeProjection (y : ι → M) (h : ι → ℝ) (s : ℝ) (p : ActivePoint (n := n) y h) : M :=
   exp p.val.1 (s•p.val.2)

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Support_TangentHullCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def tangentHull (K : Set (TangentBundle (model n) M)) : Set (TangentBundle (model n) M) :=
    {p | p.2 ∈ convexHull ℝ {a | (⟨p.1,a⟩ : TangentBundle (model n) M) ∈ K}}

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Support_TotalInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def totalInterior : Set (TangentBundle (model n) M) := {p | p.2 ∈ injectivityDomain p.1}

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end


