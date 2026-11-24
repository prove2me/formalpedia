-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:32:38.8038+00:00
-- url     : https://prove2.me/theorems/81a5757e-71f8-4d14-a1d9-64d2c1abe617
-- title:
--   Unitriangular Inverse Polynomial Bound
-- statement:
--   Definitions and structural lemmas for Unitriangular Inverse Polynomial Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/UnitriangularInversePolynomialBound.lean

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
open scoped ComplexConjugate
noncomputable section
namespace PI.PolynomialProperness
def nsq {n : ℕ} (x : Fin n → ℂ) : ℝ := ∑ i, Complex.normSq (x i)
def gramOf {n : ℕ} {ι : Type} [Fintype ι] (H : Matrix (Fin n) (Fin n) ℂ) (m : ι → Fin n → ℂ) :
    Matrix ι ι ℂ :=
  Matrix.of fun i j => herm H (m j) (m i)
def fmul (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (b : Fin (r + 1)) : Fin (2 * r + k + 1) → ℂ :=
  ∑ a, c a b • fvec k r z a
def HpkInvol : Prop := ∀ k r : ℕ, (Hpk k r)ᴴ = Hpk k r ∧ Hpk k r * Hpk k r = 1
def GVGroup : Prop :=
  ∀ k r : ℕ, (∀ g ∈ B.GV k r, ∀ h ∈ B.GV k r, g * h ∈ B.GV k r) ∧
    ∀ g ∈ B.GV k r, g⁻¹ = Hpk k r * gᴴ * Hpk k r ∧ g⁻¹ ∈ B.GV k r ∧ g * g⁻¹ = 1 ∧ g⁻¹ * g = 1
def GVHerm : Prop :=
  ∀ (k r : ℕ), ∀ g ∈ B.GV k r, ∀ v w : Fin (2 * r + k + 1) → ℂ,
    herm (Hpk k r) (g *ᵥ v) (g *ᵥ w) = herm (Hpk k r) v w
def GNFacts : Prop :=
  ∀ (k r : ℕ), (∀ g : B.Mat k r, 0 ≤ B.gN g) ∧
    (∀ g h : B.Mat k r, B.gN (g * h) ≤ B.gN g * B.gN h) ∧
    (∀ (g : B.Mat k r) (x : Fin (2 * r + k + 1) → ℂ), nsq (g *ᵥ x) ≤ B.gN g ^ 2 * nsq x) ∧
    (∀ g : B.Mat k r, B.gN g ^ 2 = ∑ j, nsq (g *ᵥ bvec j))
def FmulBound : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), ∃ C : ℝ, ∀ c b, nsq (fmul k r z c b) ≤ C * mx c ^ 2
def ZhatMove : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ σ s' : B.Mat k r)
    (v u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ), σ ∈ B.GV k r → s' ∈ B.GV k r →
    (∀ b, σ *ᵥ fvec k r z b = fmul k r z v b) → (∀ b, s' *ᵥ fvec k r z' b = fmul k r z' u' b) →
    Zhat k r z z' (σ⁻¹ * γ * s') = vᴴ * Zhat k r z z' γ * u'
def FrameS : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), StdZ k r z → ∀ s ∈ Sset k r z, s ∈ B.GV k r ∧
    ∃ u ∈ UTset (r + 1), ∀ b, s *ᵥ fvec k r z b = fmul k r z u b
def FrameSg : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' →
    ∀ σ ∈ Sg k r z z' γ, σ ∈ B.GV k r ∧ ∃ v ∈ UTset (r + 1), vᴴ ∈ LPg (Zhat k r z z' γ) ∧
      ∀ b, σ *ᵥ fvec k r z b = fmul k r z v b
def FrameSg' : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' →
    ∀ σ ∈ Sg' k r z z' γ, σ ∈ B.GV k r ∧ ∃ v ∈ UTset (r + 1),
      Zhat k r z z' γ * v * (Zhat k r z z' γ)⁻¹ ∈ UTset (r + 1) ∧
      ∀ b, σ *ᵥ fvec k r z' b = fmul k r z' v b
def UnitriangularInversePolynomialBound : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), IsMonomial (Zhat k r z z' γ) →
    ∃ C : ℝ,
    (∀ v ∈ UTset (r + 1), vᴴ ∈ LPg (Zhat k r z z' γ) → ∀ u' ∈ UTset (r + 1), ∀ g : B.Mat k r,
      1 ≤ B.gN g → Zhat k r z z' g = vᴴ * Zhat k r z z' γ * u' →
      mx v⁻¹ ≤ C * B.gN g ^ (r * (r + 1)) ∧ mx u'⁻¹ ≤ C * B.gN g ^ (r * (r + 1))) ∧
    (∀ u ∈ UTset (r + 1), ∀ v' ∈ UTset (r + 1),
      Zhat k r z z' γ * v' * (Zhat k r z z' γ)⁻¹ ∈ UTset (r + 1) → ∀ g : B.Mat k r,
      1 ≤ B.gN g → Zhat k r z z' g = uᴴ * Zhat k r z z' γ * v' →
      mx u⁻¹ ≤ C * B.gN g ^ (r * (r + 1)) ∧ mx v'⁻¹ ≤ C * B.gN g ^ (r * (r + 1)))
def IsoCore : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → Fin n → ℂ),
    Hᴴ = H → H * H = 1 → IsUnit (gramOf H m).det →
    (∀ x, (∀ i, herm H x (m i) = 0) → 0 ≤ (herm H x x).re) →
    ∃ C : ℝ, ∀ s : Matrix (Fin n) (Fin n) ℂ, sᴴ * H * s = H → ∀ K : ℝ, 0 ≤ K →
      (∀ i, nsq (s *ᵥ m i) ≤ K) → ∀ x, nsq (s *ᵥ x) ≤ C * (1 + K) ^ 2 * nsq x
def CoreInst : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    ∃ C : ℝ, ∀ s ∈ B.GV k r, ∀ K : ℝ, 0 ≤ K → (∀ i, nsq (s *ᵥ gramVec k r z z' γ i) ≤ K) →
      B.gN s ^ 2 ≤ C * (1 + K) ^ 2
end PI.PolynomialProperness


