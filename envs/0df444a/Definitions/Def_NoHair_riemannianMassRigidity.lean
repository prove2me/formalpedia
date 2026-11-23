-- Prove2me | Definitions.Def_NoHair_riemannianMassRigidity
-- name    : NoHair_riemannianMassRigidity
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T08:02:55.835978+00:00
-- url     : https://prove2.me/theorems/81cd02cd-3831-4fd3-9102-88205575226e
-- title:
--   One-ended scalar-flat Riemannian data for zero-mass rigidity
-- statement:
--   The scalar curvature is computed from the spatial Levi-Civita connection of the actual Riemannian metric in atlas charts. The asymptotic chart has metric decay through second derivatives, and the ADM flux there tends to zero. All exterior truncations have compact complement. Three-dimensional zero-mass rigidity asserts the existence of a smooth global Euclidean isometry for complete connected Riemannian manifolds with these properties.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Theorem 5.2 (p. 22 of the preprint) and its use after (5.6) on p. 24, https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. The scalar-flat one-ended case is used here. The metric falloff is (2.1) with exponent one and two derivatives.

import Definitions.Def_NoHair_staticSliceADM
import Mathlib.Geometry.Manifold.Riemannian.Basic

noncomputable section

open Set Filter Bundle
open scoped Bundle Topology Manifold ContDiff

namespace NoHair

/-- Three-dimensional Levi-Civita coefficients in a Cartesian model chart. -/
def spatialLeviCivita (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (x : ADMPoint) (a b c : Fin 3) : ℝ :=
  (1/2 : ℝ) * ∑ l : Fin 3, (h x)⁻¹ a l * (spatialADMPartial b (fun z => h z l c) x +
    spatialADMPartial c (fun z => h z l b) x - spatialADMPartial l (fun z => h z b c) x)

/-- The spatial Ricci tensor in these coordinates. -/
def spatialRicciTensor (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (x : ADMPoint) (i j : Fin 3) : ℝ :=
  ∑ a : Fin 3, (spatialADMPartial a (fun z => spatialLeviCivita h z a j i) x -
    spatialADMPartial j (fun z => spatialLeviCivita h z a a i) x +
    ∑ l : Fin 3, (spatialLeviCivita h x a a l * spatialLeviCivita h x l j i -
      spatialLeviCivita h x a j l * spatialLeviCivita h x l a i))

def spatialScalarCurvature (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) (x : ADMPoint) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, (h x)⁻¹ i j * spatialRicciTensor h x i j

/-- Pullback of the actual Riemannian inner product to a spatial coordinate chart. -/
def riemannianEndCoeffs {Q : Type*} [MetricSpace Q] [ChartedSpace ADMPoint Q]
    [IsManifold 𝓘(ℝ, ADMPoint) ∞ Q] [RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    (e : ADMPoint → Q) (x : ADMPoint) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => inner ℝ (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) e x (EuclideanSpace.single i 1))
    (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) e x (EuclideanSpace.single j 1))

/-- Scalar flatness and a single asymptotically flat end with zero ADM mass.
Every sufficiently far truncation has compact complement, so the end is the only infinity. -/
def HasScalarFlatZeroADMEnd (Q : Type*) [MetricSpace Q] [ChartedSpace ADMPoint Q]
    [IsManifold 𝓘(ℝ,ADMPoint) ∞ Q] [RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)] : Prop :=
  (∀ e ∈ atlas ADMPoint Q, ∀ x ∈ e.target, spatialScalarCurvature (riemannianEndCoeffs e.symm) x = 0) ∧
  ∃ (R C : ℝ) (e : OpenPartialHomeomorph ADMPoint Q), 0 < R ∧ 0 < C ∧
    e.source = {x | R < ‖x‖} ∧ (∀ s : ℝ, R ≤ s → IsCompact (e '' {x | s < ‖x‖})ᶜ) ∧
    ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ e e.source ∧
    ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ e.symm e.target ∧
    (∀ k : ℕ, k ≤ 2 → ∀ x ∈ e.source, ∀ i j : Fin 3,
      ‖iteratedFDeriv ℝ k (fun y => riemannianEndCoeffs e y i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) x‖
        ≤ C / ‖x‖^(1+k)) ∧ Tendsto (staticADMFlux (riemannianEndCoeffs e)) atTop (𝓝 0)

/-- The scalar-flat, one-ended, three-dimensional equality case of the positive mass theorem. -/
def ThreeDimensionalZeroMassRigidity : Prop :=
  ∀ (Q : Type) [m : MetricSpace Q] [ch : ChartedSpace ADMPoint Q] [sm : IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [rb : RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [sr : IsContMDiffRiemannianBundle 𝓘(ℝ,ADMPoint) ∞ ADMPoint (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [rm : IsRiemannianManifold 𝓘(ℝ,ADMPoint) Q] [cm : CompleteSpace Q] [cn : ConnectedSpace Q]
    [sc : SecondCountableTopology Q], HasScalarFlatZeroADMEnd Q →
    ∃ f : Q ≃ᵢ ADMPoint, ContMDiff 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ f ∧
      ContMDiff 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ f.symm ∧
      ∀ (q : Q) (v w : TangentSpace 𝓘(ℝ,ADMPoint) q),
        inner ℝ (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) f q v)
          (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) f q w) = inner ℝ v w

end NoHair


