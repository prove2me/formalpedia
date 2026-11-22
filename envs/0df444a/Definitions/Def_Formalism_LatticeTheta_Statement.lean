-- Prove2me | Definitions.Def_Formalism_LatticeTheta_Statement
-- name    : Formalism_LatticeTheta_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:46:04.225445+00:00
-- url     : https://prove2.me/theorems/07468a24-e6a3-46d6-9c7a-cf9262535fdb
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/Statement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap
noncomputable section
namespace Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]
abbrev dual (Λ : Submodule ℤ V) : Submodule ℤ V :=
  LinearMap.BilinForm.dualSubmodule (innerₗ V) Λ
def theta (Λ : Submodule ℤ V) (t : ℝ) : ℝ :=
  ∑' l : Λ, Real.exp (-Real.pi * t * ‖(l : V)‖ ^ 2)
def thetaShift (Λ : Submodule ℤ V) (t : ℝ) (x : V) : ℝ :=
  ∑' l : Λ, Real.exp (-Real.pi * t * ‖(l : V) + x‖ ^ 2)
variable (V) in

def DualIsLattice [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
    DiscreteTopology (dual Λ) ∧ ∀ [DiscreteTopology (dual Λ)], IsZLattice ℝ (dual Λ)
variable (V) in

def CovolumeDual [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    [DiscreteTopology (dual Λ)] [IsZLattice ℝ (dual Λ)],
    ZLattice.covolume (dual Λ) = (ZLattice.covolume Λ)⁻¹
variable (V) in

def DualDual [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ], dual (dual Λ) = Λ
variable (V) in

def PoissonDecay [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : V → ℂ), Continuous f →
    ∀ b : ℝ, (Module.finrank ℝ V : ℝ) < b →
    f =O[cocompact V] (fun v => ‖v‖ ^ (-b)) →
    (𝓕 f : V → ℂ) =O[cocompact V] (fun v => ‖v‖ ^ (-b)) →
    ∀ x : V,
      Summable (fun μ : dual Λ =>
          (𝓕 f : V → ℂ) μ * Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ))) ∧
      HasSum (fun l : Λ => f ((l : V) + x))
        ((ZLattice.covolume Λ : ℂ)⁻¹ * ∑' μ : dual Λ,
          (𝓕 f : V → ℂ) μ * Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ)))
variable (V) in

def PoissonSchwartz [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : 𝓢(V, ℂ)) (x : V),
      Summable (fun μ : dual Λ =>
          (𝓕 (f : V → ℂ) : V → ℂ) μ * Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ))) ∧
      HasSum (fun l : Λ => f ((l : V) + x))
        ((ZLattice.covolume Λ : ℂ)⁻¹ * ∑' μ : dual Λ,
          (𝓕 (f : V → ℂ) : V → ℂ) μ * Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ)))
variable (V) in

def ThetaSummable [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (t : ℝ), 0 < t → ∀ x : V,
    Summable (fun l : Λ => Real.exp (-Real.pi * t * ‖(l : V) + x‖ ^ 2))
variable (V) in
def ThetaPos [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (t : ℝ), 0 < t → 1 ≤ theta Λ t
variable (V) in

def ThetaInversion [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (t : ℝ), 0 < t →
    theta Λ (1 / t) =
      (ZLattice.covolume Λ)⁻¹ * t ^ ((Module.finrank ℝ V : ℝ) / 2) * theta (dual Λ) t
variable (V) in

def ThetaShiftInversion [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (t : ℝ), 0 < t → ∀ x : V,
    Summable (fun μ : dual Λ => (Real.exp (-Real.pi * ‖(μ : V)‖ ^ 2 / t) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ))) ∧
    (thetaShift Λ t x : ℂ) =
      (ZLattice.covolume Λ : ℂ)⁻¹ * ((t ^ (-(Module.finrank ℝ V : ℝ) / 2) : ℝ) : ℂ) *
        ∑' μ : dual Λ, (Real.exp (-Real.pi * ‖(μ : V)‖ ^ 2 / t) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ))
end Formalism.H


