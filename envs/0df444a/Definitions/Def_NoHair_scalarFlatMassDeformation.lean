-- Prove2me | Definitions.Def_NoHair_scalarFlatMassDeformation
-- name    : NoHair_scalarFlatMassDeformation
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T10:47:18.179047+00:00
-- url     : https://prove2.me/theorems/15b5a8de-c795-43af-8875-dbfaa5299c18
-- title:
--   ADM mass deformation and Euclidean developing covers
-- statement:
--   Scalar-flat asymptotically flat ends with prescribed mass, Ricci curvature in the atlas, and a Euclidean developing cover with its asymptotic sheet.
-- source:
--   R. Schoen and S.-T. Yau, On the proof of the positive mass conjecture in general relativity, Comm. Math. Phys. 65 (1979), 45–76, https://doi.org/10.1007/BF01940959. R. Bartnik, The mass of an asymptotically flat manifold, Comm. Pure Appl. Math. 39 (1986), 661–693, https://doi.org/10.1002/cpa.3160390505.

import Definitions.Def_NoHair_riemannianMassRigidity
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Normed.Affine.MazurUlam

noncomputable section
open Set Filter Bundle
open scoped Bundle Topology Manifold ContDiff
namespace NoHair

/-- Scalar-flat one-ended asymptotically flat geometry with a prescribed ADM mass. -/
def HasScalarFlatADMEnd (Q : Type*) [MetricSpace Q] [ChartedSpace ADMPoint Q]
    [IsManifold 𝓘(ℝ,ADMPoint) ∞ Q] [RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)] (mass : ℝ) : Prop :=
  (∀ e ∈ atlas ADMPoint Q, ∀ x ∈ e.target, spatialScalarCurvature (riemannianEndCoeffs e.symm) x = 0) ∧
  ∃ (R C : ℝ) (e : OpenPartialHomeomorph ADMPoint Q), 0 < R ∧ 0 < C ∧
    e.source = {x | R < ‖x‖} ∧ (∀ s : ℝ, R ≤ s → IsCompact (e '' {x | s < ‖x‖})ᶜ) ∧
    ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ e e.source ∧
    ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ e.symm e.target ∧
    (∀ k : ℕ, k ≤ 2 → ∀ x ∈ e.source, ∀ i j : Fin 3,
      ‖iteratedFDeriv ℝ k (fun y => riemannianEndCoeffs e y i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) x‖
        ≤ C / ‖x‖^(1+k)) ∧ Tendsto (staticADMFlux (riemannianEndCoeffs e)) atTop (𝓝 mass)

/-- Mass realized by a smooth complete connected scalar-flat Riemannian three-manifold. -/
def IsScalarFlatADMMass (mass : ℝ) : Prop :=
  ∃ (Q : Type) (mI : MetricSpace Q) (ch : ChartedSpace ADMPoint Q),
    letI := mI
    letI := ch
    ∃ (sm : IsManifold 𝓘(ℝ,ADMPoint) ∞ Q) (rb : RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)),
      letI := sm
      letI := rb
      IsContMDiffRiemannianBundle 𝓘(ℝ,ADMPoint) ∞ ADMPoint (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q) ∧
        IsRiemannianManifold 𝓘(ℝ,ADMPoint) Q ∧ CompleteSpace Q ∧ ConnectedSpace Q ∧ SecondCountableTopology Q ∧ HasScalarFlatADMEnd Q mass

/-- Vanishing of each Ricci component throughout the smooth atlas. -/
def RicciFlatInADMCharts (Q : Type*) [MetricSpace Q] [ChartedSpace ADMPoint Q]
    [IsManifold 𝓘(ℝ,ADMPoint) ∞ Q] [RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)] : Prop :=
  ∀ e ∈ atlas ADMPoint Q, ∀ x ∈ e.target, ∀ i j : Fin 3,
    spatialRicciTensor (riemannianEndCoeffs e.symm) x i j = 0

/-- Data from the Euclidean developing cover of a flat complete AF manifold.
The end has a lifted sheet containing all points sufficiently far out in the cover. -/
structure FlatEndDevelopingMap (Q : Type) [MetricSpace Q] [ChartedSpace ADMPoint Q]
    [IsManifold 𝓘(ℝ,ADMPoint) ∞ Q] [RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)] where
  proj : ADMPoint → Q
  localDiffeo : IsLocalDiffeomorph 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ proj
  innerMap : ∀ x v w : ADMPoint, inner ℝ (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) proj x v)
    (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) proj x w) = inner ℝ v w
  liftDistance : ∀ x : ADMPoint, ∀ q : Q, ∃ y : ADMPoint, proj y = q ∧ dist x y = dist (proj x) q
  deck : ∀ x y, proj x = proj y → ∃ d : ADMPoint ≃ᵢ ADMPoint, d x = y ∧ ∀ z, proj (d z) = proj z
  sheet : ∃ R : ℝ, Set.InjOn proj {x | R < ‖x‖}

end NoHair


