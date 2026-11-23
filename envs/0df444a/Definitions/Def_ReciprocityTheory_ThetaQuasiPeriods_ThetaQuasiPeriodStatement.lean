-- Prove2me | Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
-- name    : ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:24.812751+00:00
-- url     : https://prove2.me/theorems/d566f81f-b31a-4481-9a59-e051d538ac4f
-- title:
--   Theta Quasi Period Statement
-- statement:
--   Definitions and structural lemmas for Theta Quasi Period Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/ThetaQuasiPeriodStatement.lean

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
namespace ReciprocityTheory.PTheta
def SiegelSubDomainStatement : Prop :=
  ∀ (ι : Type) [Fintype ι], SiegelH ι ⊆ ThetaDomain ι
def DomainOpenStatement : Prop :=
  ∀ (ι : Type) [Fintype ι], IsOpen {t : ι → ι → ℂ | Matrix.of t ∈ ThetaDomain ι}
def ThetaSummableStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (a b : ι → ℝ) (z : ι → ℂ) (τ : Matrix ι ι ℂ), τ ∈ ThetaDomain ι →
    Summable (fun l => ‖thetaTerm a b z τ l‖)
def ThetaMTestStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (a : ι → ℝ) (K : Set ((ι → ℂ) × (ι → ι → ℂ))), IsCompact K →
    (∀ p ∈ K, Matrix.of p.2 ∈ ThetaDomain ι) →
    ∃ u : (ι → ℤ) → ℝ, Summable u ∧
      ∀ (b : ι → ℝ), ∀ p ∈ K, ∀ l, ‖thetaTerm a b p.1 (Matrix.of p.2) l‖ ≤ u l
def ThetaHoloStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (a b : ι → ℝ),
    DifferentiableOn ℂ (fun p : (ι → ℂ) × (ι → ι → ℂ) => theta a b p.1 (Matrix.of p.2))
      {p | Matrix.of p.2 ∈ ThetaDomain ι}
def ThetaQuasiPeriodStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (a b : ι → ℝ) (z : ι → ℂ) (τ : Matrix ι ι ℂ) (n n' : ι → ℤ), τ.IsSymm →
    theta a b (z + τ *ᵥ ofIntVec n + ofIntVec n') τ = autFactor a b τ n n' z * theta a b z τ
def ThetaIntCharStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (a b : ι → ℝ) (n n' : ι → ℤ) (z : ι → ℂ) (τ : Matrix ι ι ℂ),
    theta (a + fun i => (n i : ℝ)) (b + fun i => (n' i : ℝ)) z τ =
      eC (ofRealVec a ⬝ᵥ ofIntVec n') * theta a b z τ
def ThetaRealTranslStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (a b u v : ι → ℝ) (z : ι → ℂ) (τ : Matrix ι ι ℂ), τ.IsSymm →
    theta a b (z + τ *ᵥ ofRealVec u + ofRealVec v) τ =
      eC (-(ofRealVec u ⬝ᵥ (τ *ᵥ ofRealVec u)) / 2 - ofRealVec u ⬝ᵥ (z + ofRealVec b + ofRealVec v)) *
        theta (a + u) (b + v) z τ
def ThetaCharShiftStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (a b a' b' : ι → ℝ) (z : ι → ℂ) (τ : Matrix ι ι ℂ), τ.IsSymm →
    theta (a' + a) (b' + b) z τ =
      eC (ofRealVec a ⬝ᵥ (τ *ᵥ ofRealVec a) / 2 + ofRealVec a ⬝ᵥ (z + ofRealVec b + ofRealVec b')) *
        theta a' b' (z + τ *ᵥ ofRealVec a + ofRealVec b) τ
def ThetaNegStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (a b : ι → ℝ) (z : ι → ℂ) (τ : Matrix ι ι ℂ),
    theta (-a) (-b) (-z) τ = theta a b z τ
def ThetaHalfParityStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (n n' : ι → ℤ) (z : ι → ℂ) (τ : Matrix ι ι ℂ),
    theta (fun i => (n i : ℝ) / 2) (fun i => (n' i : ℝ) / 2) (-z) τ =
      (-1) ^ (n ⬝ᵥ n') * theta (fun i => (n i : ℝ) / 2) (fun i => (n' i : ℝ) / 2) z τ
def ThetaTranslTauStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (a b : ι → ℝ) (z : ι → ℂ) (τ : Matrix ι ι ℂ) (B : Matrix ι ι ℤ), B.IsSymm →
    theta a b z (τ + B.map (fun x : ℤ => (x : ℂ))) =
      eC (-(ofRealVec a ⬝ᵥ (B.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec a)) / 2 -
          ofRealVec a ⬝ᵥ (fun i => ((B i i : ℤ) : ℂ) / 2)) *
        theta a (b + B.map (fun x : ℤ => (x : ℝ)) *ᵥ a + fun i => ((B i i : ℤ) : ℝ) / 2) z τ
def ThetaGLStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (U : (Matrix ι ι ℤ)ˣ) (a b : ι → ℝ) (z : ι → ℂ)
    (τ : Matrix ι ι ℂ),
    theta a b ((U : Matrix ι ι ℤ).map (fun x : ℤ => (x : ℂ)) *ᵥ z)
        ((U : Matrix ι ι ℤ).map (fun x : ℤ => (x : ℂ)) * τ *
          ((U : Matrix ι ι ℤ).map (fun x : ℤ => (x : ℂ)))ᵀ) =
      theta (((U : Matrix ι ι ℤ).map (fun x : ℤ => (x : ℝ)))ᵀ *ᵥ a)
        (((U⁻¹ : (Matrix ι ι ℤ)ˣ) : Matrix ι ι ℤ).map (fun x : ℤ => (x : ℝ)) *ᵥ b) z τ
def ThetaBlockStatement : Prop :=
  ∀ (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] (a₁ b₁ : ι₁ → ℝ) (a₂ b₂ : ι₂ → ℝ) (z₁ : ι₁ → ℂ)
    (z₂ : ι₂ → ℂ) (τ₁₁ : Matrix ι₁ ι₁ ℂ) (τ₁₂ : Matrix ι₁ ι₂ ℂ) (τ₂₂ : Matrix ι₂ ι₂ ℂ),
    Matrix.fromBlocks τ₁₁ τ₁₂ τ₁₂ᵀ τ₂₂ ∈ SiegelH (ι₁ ⊕ ι₂) →
    theta (Sum.elim a₁ a₂) (Sum.elim b₁ b₂) (Sum.elim z₁ z₂) (Matrix.fromBlocks τ₁₁ τ₁₂ τ₁₂ᵀ τ₂₂) =
      ∑' l₂ : ι₂ → ℤ, eC (shiftVec a₂ l₂ ⬝ᵥ (τ₂₂ *ᵥ shiftVec a₂ l₂) / 2 +
          shiftVec a₂ l₂ ⬝ᵥ (z₂ + ofRealVec b₂)) *
        theta a₁ b₁ (z₁ + τ₁₂ *ᵥ shiftVec a₂ l₂) τ₁₁
def ThetaGenusOneStatement : Prop :=
  ∀ z τ : ℂ, theta (ι := Fin 1) 0 0 (fun _ => z) (Matrix.of fun _ _ => τ) = jacobiTheta₂ z τ
end ReciprocityTheory.PTheta


