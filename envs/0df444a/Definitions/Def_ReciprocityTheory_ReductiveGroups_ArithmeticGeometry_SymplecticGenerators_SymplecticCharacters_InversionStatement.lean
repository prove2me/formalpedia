-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_InversionStatement
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_InversionStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:04:37.240434+00:00
-- url     : https://prove2.me/theorems/40aae85c-538d-4991-b363-c64fe1b2acd5
-- title:
--   Inversion Statement
-- statement:
--   Definitions and structural lemmas for Inversion Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/InversionStatement.lean

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_StTransl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SpGenStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
def cMat {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :
    Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ :=
  γ.map (fun x : ℤ => (x : ℂ))
def jAut {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    Matrix (Fin g) (Fin g) ℂ :=
  (cMat γ).toBlocks₂₁ * τ + (cMat γ).toBlocks₂₂
def spAct {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    Matrix (Fin g) (Fin g) ℂ :=
  ((cMat γ).toBlocks₁₁ * τ + (cMat γ).toBlocks₁₂) * (jAut γ τ)⁻¹
def zAct {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (τ : Matrix (Fin g) (Fin g) ℂ)
    (z : Fin g → ℂ) : Fin g → ℂ :=
  ((jAut γ τ)⁻¹)ᵀ *ᵥ z
def expArg {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (τ : Matrix (Fin g) (Fin g) ℂ)
    (z : Fin g → ℂ) : ℂ :=
  z ⬝ᵥ (((jAut γ τ)⁻¹ * (cMat γ).toBlocks₂₁) *ᵥ z)
def SpActStatement : Prop :=
  ∀ (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ), γ ∈ Matrix.symplecticGroup (Fin g) ℤ →
    ∀ τ ∈ SiegelH (Fin g), IsUnit (jAut γ τ).det ∧ spAct γ τ ∈ SiegelH (Fin g)
def ChiAt (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) : Prop :=
  ∀ n n' : Fin g → ℤ, ∃ (k k' : Fin g → ℤ) (c : ℂ),
    (∀ i, k i = 0 ∨ k i = 1) ∧ (∀ i, k' i = 0 ∨ k' i = 1) ∧ c ^ 4 = 1 ∧
    ∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ,
      theta (halfVec k) (halfVec k') (zAct γ τ z) (spAct γ τ) ^ 2 =
        c * (jAut γ τ).det * eC (expArg γ τ z) * theta (halfVec n) (halfVec n') z τ ^ 2
def ChiStatement : Prop :=
  ∀ (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ), γ ∈ Matrix.symplecticGroup (Fin g) ℤ →
    ChiAt g γ
def ChiGenStatement : Prop :=
  ∀ (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ), γ ∈ spGens g → ChiAt g γ
def InversionStatement : Prop :=
  ∀ (g : ℕ) (a b : Fin g → ℝ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) →
    ∀ z : Fin g → ℂ,
      theta a b (τ⁻¹ *ᵥ z) (-τ⁻¹) ^ 2 =
        (-I) ^ g * τ.det * eC (z ⬝ᵥ (τ⁻¹ *ᵥ z)) * eC (2 * (ofRealVec a ⬝ᵥ ofRealVec b)) *
          theta b (-a) z τ ^ 2
end ReciprocityTheory.ChartRestriction.G.Key.Chi


