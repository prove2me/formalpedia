-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_HermitianTensorPowers
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_HermitianTensorPowers
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:19.003842+00:00
-- url     : https://prove2.me/theorems/2d1d8cc1-702a-4435-89e6-90ed39579bf9
-- title:
--   Hermitian Tensor Powers
-- statement:
--   Definitions and structural lemmas for Hermitian Tensor Powers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/HermitianTensorPowers.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
def herm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) : ℂ := z ⬝ᵥ Hm.mulVec (star w)
def factor {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (l z : Fin g → ℂ) : ℂ :=
  c * Complex.exp (Real.pi * herm Hm z l + Real.pi / 2 * herm Hm l l)
def IsThetaFn {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (n : ℕ)
    (θ : (Fin g → ℂ) → ℂ) : Prop :=
  Differentiable ℂ θ ∧ ∀ (l : Λ) (z : Fin g → ℂ), θ (z + l) = factor Hm (χ l) l z ^ n * θ z
abbrev tpow {X : Scheme.{0}} (L : LB X) (n : ℕ) : LB X :=
  LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => (n : ℤ))
def IsFnPow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (n : ℕ)
    (s : (tpow L n).Sec) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ (j : (tpow L n).ι) (z : Fin g → ℂ), ⊤ ≤ (u.ex z).left ⁻¹ᵁ (tpow L n).U j →
    valAt' (u.ex z).left ((tpow L n).U j) (s.f j) = θ z * u.fr (j PUnit.unit) z ^ n
def commVal {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (k : ℕ) (v w : Fin g → ℂ) : ℂˣ :=
  Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I * (k * ((herm Hm v w).im : ℂ))))) (Complex.exp_ne_zero _)
def ThetaUniformisation : Prop :=
  ∀ (P : Out.PolAV (Sp ℂ)) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen →
    ∃ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ),

      u.IsAH Hm χ ∧ u.IsRig rig ∧

      (∀ l, χ l = 1 ∨ χ l = -1) ∧
      (∀ l m : u.Λ, χ (l + m) = χ l * χ m * Complex.exp (Real.pi * Complex.I * ((herm Hm l m).im : ℂ))) ∧

      (∀ v : epsR ℂ ⟶ P.A, IsTangent v → ∃! w : Fin P.g → ℂ, u.IsDiff w v) ∧
      (∀ w : Fin P.g → ℂ, ∃! v : epsR ℂ ⟶ P.A, IsTangent v ∧ u.IsDiff w v) ∧

      (∀ f : P.A ⟶ P.A, IsMonHom f → ∃ M : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ),
        (∀ l ∈ u.Λ, M l ∈ u.Λ) ∧ ∀ z, u.ex (M z) = u.ex z ≫ f) ∧

      (∀ n : ℕ,
        (∀ s : (tpow P.L n).Sec, ∃! θ, IsThetaFn u.Λ Hm χ n θ ∧ IsFnPow u n s θ) ∧
        (∀ θ, IsThetaFn u.Λ Hm χ n θ → ∃! s : (tpow P.L n).Sec, IsFnPow u n s θ)) ∧

      (∀ l m : u.Λ, ∃ a : ℤ, (herm Hm l m).im = a) ∧
      (∀ φ : u.Λ →ₗ[ℤ] ℤ, ∃! l : u.Λ, ∀ m : u.Λ, (herm Hm l m).im = φ m) ∧

      (∀ k : ℕ, 0 < k → ∀ v w : Fin P.g → ℂ, k • v ∈ u.Λ → k • w ∈ u.Λ →
        Out.WeilIs P.A P.L (k : ℤ) (u.ex v) (u.ex w) (unitOn (commVal Hm k v w)))
def shift {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (k : ℕ) (v : Fin g → ℂ) (θ : (Fin g → ℂ) → ℂ) :
    (Fin g → ℂ) → ℂ := fun z => Complex.exp (-(k * Real.pi * herm Hm z v)) * θ (z + v)
end GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers


