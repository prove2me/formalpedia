-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_StTransl
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_StTransl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:59:17.886007+00:00
-- url     : https://prove2.me/theorems/75163bea-8b4c-415d-9ff3-84780559f368
-- title:
--   St Transl
-- statement:
--   Definitions and structural lemmas for St Transl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/StTransl.lean

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix ReciprocityTheory.PTheta
namespace ReciprocityTheory.ChartRestriction.G.Key
def halfVec {g : ℕ} (n : Fin g → ℤ) : Fin g → ℝ := fun i => (n i : ℝ) / 2
def TranslShiftStatement : Prop :=
  ∀ (g : ℕ) (a' b' a b : Fin g → ℝ) (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ),
    τ ∈ SiegelH (Fin g) →
    theta (a' + a) (b' + b) z τ =
      eC (ofRealVec a ⬝ᵥ (τ *ᵥ ofRealVec a) / 2 + ofRealVec a ⬝ᵥ (z + ofRealVec b + ofRealVec b')) *
        theta a' b' (z + τ *ᵥ ofRealVec a + ofRealVec b) τ
def TranslSignStatement : Prop :=
  ∀ (g : ℕ) (n n' m m' : Fin g → ℤ),
    eC (4 * (ofRealVec (halfVec n) ⬝ᵥ (ofRealVec (halfVec n') + ofRealVec (halfVec m')))) = 1 ∧
    (eC (ofRealVec (halfVec m) ⬝ᵥ ofIntVec n' - ofRealVec (halfVec m') ⬝ᵥ ofIntVec n) = 1 ∨
      eC (ofRealVec (halfVec m) ⬝ᵥ ofIntVec n' - ofRealVec (halfVec m') ⬝ᵥ ofIntVec n) = -1)
def TranslFourthStatement : Prop :=
  ∀ (g : ℕ) (n n' m m' : Fin g → ℤ) (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ),
    τ ∈ SiegelH (Fin g) →
    (autFactor (halfVec m) (halfVec m') τ n n' 0)⁻¹ * eC (4 * (ofRealVec (halfVec n) ⬝ᵥ z)) *
        theta (halfVec m) (halfVec m')
          (z + τ *ᵥ ofRealVec (halfVec n) + ofRealVec (halfVec n')) τ ^ 4 =
      eC (-(ofRealVec (halfVec m) ⬝ᵥ ofIntVec n' - ofRealVec (halfVec m') ⬝ᵥ ofIntVec n)) *
        theta (halfVec m + halfVec n) (halfVec m' + halfVec n') z τ ^ 4
def TranslFourthSignStatement : Prop :=
  ∀ (g : ℕ) (n n' m m' : Fin g → ℤ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) →
    ∃ s : ℂ, (s = 1 ∨ s = -1) ∧ ∀ z : Fin g → ℂ,
      (autFactor (halfVec m) (halfVec m') τ n n' 0)⁻¹ * eC (4 * (ofRealVec (halfVec n) ⬝ᵥ z)) *
          theta (halfVec m) (halfVec m')
            (z + τ *ᵥ ofRealVec (halfVec n) + ofRealVec (halfVec n')) τ ^ 4 =
        s * theta (halfVec m + halfVec n) (halfVec m' + halfVec n') z τ ^ 4
end ReciprocityTheory.ChartRestriction.G.Key


