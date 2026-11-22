-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:35:59.709031+00:00
-- url     : https://prove2.me/theorems/b4eede0d-222a-4b02-b31f-50437fbfa16a
-- title:
--   Theta Unif AV
-- statement:
--   Definitions and structural lemmas for Theta Unif AV, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ThetaUnifAV.lean

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
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
abbrev lbPow {X : Scheme.{0}} (L : LB X) (n : ℕ) : LB X :=
  LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => (n : ℤ))
def hermForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) : ℂ := z ⬝ᵥ Hm.mulVec (star w)
namespace HolUnif
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
def IsFnPow (n : ℕ) (s : (lbPow L n).Sec) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ (j : (lbPow L n).ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U j →
    valAt' (u.ex z).left ((lbPow L n).U j) (s.f j) = θ z * u.fr (j PUnit.unit) z ^ n
def IsThetaFn (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (n : ℕ) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  Differentiable ℂ θ ∧ ∀ (l : u.Λ) z, θ (z + l) =
    (χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l)) ^ n * θ z
end HolUnif
def ThetaUnifAV : Prop :=
  ∀ (P : Out.PolAV (Sp ℂ)) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen →
    ∃ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ),
      u.IsAH Hm χ ∧ u.IsRig rig ∧
      (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧
      (∀ f : P.A ⟶ P.A, IsMonHom f → ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f) ∧
      (∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧
        ∀ θ, u.IsThetaFn Hm χ n θ → ∃! s, u.IsFnPow n s θ) ∧
      (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef ∧
      ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k →
        (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) →
        Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn c)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


