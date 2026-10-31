-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P04
-- name    : QAlgorithms_Papers_Independent_Intake100_P04
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T12:42:05.580216+00:00
-- url     : https://prove2.me/theorems/c8153a8c-ca82-4f84-98bb-4230f8d52742
-- title:
--   Definitions for Lie Group Structures on Symmetry Groups of Principal Bundles
-- statement:
--   The objects the formalized statements of *Lie Group Structures on Symmetry Groups of Principal Bundles* (arXiv:math/0612522) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `RightBundleData`: Definitions 1.1 and A.20, PDF pp. 3 and 27: continuous free fiber-preserving right group action data. An OpenTrivialisingSystem below supplies local triviality and surjectivity for this very action.
--   - `OpenTrivialisingSystem`: Definition A.20, PDF p. 27: open cover, continuous sections and continuous fiber coordinates. Reconstruction and coordinate laws express actual principal local trivializations. Functions have arbitrary total extensions; all conditions and later uses restrict to the stated domains.
--   - `transitionFunction`: Definition A.20, equation (21), PDF p. 27: k_ij is the i-th fiber coordinate of the j-th section, so sigma_i(x) k_ij(x) = sigma_j(x) on the overlap. Values outside the overlap play no role.
--   - `Refines`: Definition A.20, PDF p. 27: refinement restricts original sections as well as refining open domains. No change of section is allowed.
--   - `trivialRightBundle`: A concrete family of principal bundles for A.20's sanity instance: projection X × K to X with the ordinary right action.
-- source:
--   Lie Group Structures on Symmetry Groups of Principal Bundles, arXiv:math/0612522v1, https://arxiv.org/abs/math/0612522v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P05

/-!
Draft statements from Wockel, arXiv:math/0612522v1.
The directional calculus, left velocity, exponential data and identity
differential are imported from inspected pinned accepted modules. Only the
continuous principal-bundle interfaces below are new paper-local definitions.
No normability or completeness is imposed.
Deferred nodes are inventoried in HARD.md and GAPS.json. Compilation and
independent moderation are pending batch handoff.
-/

namespace QAlgorithms.Papers.Independent.Intake100.P04

open Set Filter Topology
open QAlgorithms.Papers.Independent.Next46.P35
open QAlgorithms.Papers.Independent.Bridge50.P08 (HasLeftVelocity identityDifferential)
open QAlgorithms.Papers.Independent.Gap48.P05 (ExponentialLieData)

universe u v w z

/-- Product charts for smooth multiplication, Definition A.3, PDF p. 23. -/
local instance productCharts
    (E F M N : Type*) [TopologicalSpace E] [TopologicalSpace F]
    [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace E M] [ChartedSpace F N] : ChartedSpace (E × F) (M × N) :=
  prodChartedSpace E M F N

section DirectionalCalculus

variable {E : Type u} {F : Type v}
variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- Sanity: the zero function has the zero tower, including order zero. -/
example (U : Set E) : DirectionalSmoothOn U (fun _ : E => (0 : F)) := by
  refine ⟨fun _ _ _ => 0, ?_, ?_, ?_⟩
  · intro x hx
    rfl
  · intro n
    exact continuousOn_const
  · intro n x hx a h
    simpa only [sub_self, smul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : F))
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : F)))

end DirectionalCalculus

section Exponentials

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable {G : Type v} [Group G] [TopologicalSpace G] [ChartedSpace E G]

/-- Sanity: the constant identity curve has zero left velocity. -/
example (t : ℝ) : HasLeftVelocity (E := E) (fun _ : ℝ => (1 : G)) t 0 := by
  unfold HasLeftVelocity
  simp only [inv_one, one_mul, sub_self, smul_zero]
  exact tendsto_const_nhds

variable {F : Type w} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
variable {H : Type z} [Group H] [TopologicalSpace H] [ChartedSpace F H]

/-- Sanity: the imported differential of the trivial homomorphism is zero. -/
example [T2Space F] (x : E) :
    identityDifferential (E := E) (F := F) (1 : G →* H) x = 0 := by
  unfold identityDifferential
  change Filter.limUnder (𝓝[≠] (0 : ℝ)) (fun t : ℝ => t⁻¹ •
    (chartAt F (1 : H) 1 - chartAt F (1 : H) 1)) = 0
  simp only [sub_self, smul_zero]
  exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : F))
    (𝓝[≠] (0 : ℝ)) (𝓝 (0 : F))).limUnder_eq

end Exponentials

section ContinuousBundles

variable {K : Type u} {X : Type v} {P : Type w}
variable [Group K] [TopologicalSpace K] [TopologicalSpace X] [TopologicalSpace P]

/-- Definitions 1.1 and A.20, PDF pp. 3 and 27: continuous free
fiber-preserving right group action data. An OpenTrivialisingSystem below
supplies local triviality and surjectivity for this very action. -/
structure RightBundleData where
  projection : P → X
  projectionContinuous : Continuous projection
  rightAction : P → K → P
  rightActionContinuous : Continuous (fun p : P × K => rightAction p.1 p.2)
  actionOne : ∀ p, rightAction p 1 = p
  actionMul : ∀ p a b, rightAction (rightAction p a) b = rightAction p (a * b)
  projectionAction : ∀ p k, projection (rightAction p k) = projection p
  actionFree : ∀ p a b, rightAction p a = rightAction p b → a = b

/-- Definition A.20, PDF p. 27: open cover, continuous sections and
continuous fiber coordinates. Reconstruction and coordinate laws express
actual principal local trivializations. Functions have arbitrary total
extensions; all conditions and later uses restrict to the stated domains. -/
structure OpenTrivialisingSystem (B : RightBundleData (K := K) (X := X) (P := P))
    (I : Type z) where
  base : I → Set X
  baseOpen : ∀ i, IsOpen (base i)
  covers : ∀ x, ∃ i, x ∈ base i
  sectionMap : I → X → P
  sectionContinuous : ∀ i, ContinuousOn (sectionMap i) (base i)
  sectionProjection : ∀ i x, x ∈ base i → B.projection (sectionMap i x) = x
  coordinate : I → P → K
  coordinateContinuous : ∀ i, ContinuousOn (coordinate i) (B.projection ⁻¹' base i)
  sectionCoordinate : ∀ i x, x ∈ base i → coordinate i (sectionMap i x) = 1
  reconstruct : ∀ i p, B.projection p ∈ base i →
    B.rightAction (sectionMap i (B.projection p)) (coordinate i p) = p
  coordinateAction : ∀ i p k, B.projection p ∈ base i →
    coordinate i (B.rightAction p k) = coordinate i p * k

/-- Definition A.20, equation (21), PDF p. 27: k_ij is the i-th fiber
coordinate of the j-th section, so sigma_i(x) k_ij(x) = sigma_j(x) on
the overlap. Values outside the overlap play no role. -/
def transitionFunction {I : Type z}
    {B : RightBundleData (K := K) (X := X) (P := P)}
    (U : OpenTrivialisingSystem B I) (i j : I) (x : X) : K :=
  U.coordinate i (U.sectionMap j x)

/-- Definition A.20, PDF p. 27: refinement restricts original sections
as well as refining open domains. No change of section is allowed. -/
def Refines {I J : Type z}
    {B : RightBundleData (K := K) (X := X) (P := P)}
    (V : OpenTrivialisingSystem B J) (U : OpenTrivialisingSystem B I) : Prop :=
  ∃ a : J → I, ∀ j, V.base j ⊆ U.base (a j) ∧
    ∀ x ∈ V.base j, V.sectionMap j x = U.sectionMap (a j) x

/-- Sanity: the transition function has the source's multiplication order. -/
example {I : Type z} {B : RightBundleData (K := K) (X := X) (P := P)}
    (U : OpenTrivialisingSystem B I) (i j : I) (x : X)
    (hi : x ∈ U.base i) (hj : x ∈ U.base j) :
    B.rightAction (U.sectionMap i x) (transitionFunction U i j x) =
      U.sectionMap j x := by
  have hp := U.sectionProjection j x hj
  have hr := U.reconstruct i (U.sectionMap j x) (by simpa only [hp] using hi)
  simpa only [hp, transitionFunction] using hr

/-- Sanity: every system refines itself by the identity index map. -/
example {I : Type z} {B : RightBundleData (K := K) (X := X) (P := P)}
    (U : OpenTrivialisingSystem B I) : Refines U U := by
  exact ⟨id, fun _ => ⟨Subset.rfl, fun _ _ => rfl⟩⟩

/-- A concrete family of principal bundles for A.20's sanity instance:
projection X × K to X with the ordinary right action. -/
def trivialRightBundle [IsTopologicalGroup K] :
    RightBundleData (K := K) (X := X) (P := X × K) where
  projection := Prod.fst
  projectionContinuous := continuous_fst
  rightAction := fun p k => (p.1, p.2 * k)
  rightActionContinuous := continuous_fst.fst.prodMk (continuous_fst.snd.mul continuous_snd)
  actionOne := by intro p; exact Prod.ext rfl (mul_one p.2)
  actionMul := by intro p a b; exact Prod.ext rfl (mul_assoc p.2 a b)
  projectionAction := by intro p k; rfl
  actionFree := by
    intro p a b h
    exact mul_left_cancel (congrArg Prod.snd h)

/-- Sanity: the product bundle has a one-chart trivialising system with
section x ↦ (x,1) and fiber coordinate (x,k) ↦ k. -/
example [IsTopologicalGroup K] :
    OpenTrivialisingSystem (trivialRightBundle (K := K) (X := X)) (Fin 1) where
  base := fun _ => Set.univ
  baseOpen := fun _ => isOpen_univ
  covers := fun _ => ⟨0, Set.mem_univ _⟩
  sectionMap := fun _ x => (x, 1)
  sectionContinuous := fun _ => (continuous_id.prodMk continuous_const).continuousOn
  sectionProjection := by intro i x hx; rfl
  coordinate := fun _ p => p.2
  coordinateContinuous := fun _ => continuous_snd.continuousOn
  sectionCoordinate := by intro i x hx; rfl
  reconstruct := by intro i p hp; exact Prod.ext rfl (one_mul p.2)
  coordinateAction := by intro i p k hp; rfl

end ContinuousBundles

end QAlgorithms.Papers.Independent.Intake100.P04


