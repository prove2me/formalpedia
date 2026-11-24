-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFibreBoundDefs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFibreBoundDefs
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T19:46:26.268677+00:00
-- url     : https://prove2.me/theorems/60544371-1a6a-4548-b61c-f66477234f8a
-- title:
--   PFibre Bound Defs
-- statement:
--   Definitions and structural lemmas for PFibre Bound Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PFibreBoundDefs.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PTopDensCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnipotentFixesFrameVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
noncomputable section
namespace PI.UnitaryGroupMassFormula.DLm
def tN {m n : ℕ} (v : Fin m → Fin n → ℂ) : ℝ := Real.sqrt (∑ b, ∑ i, Complex.normSq (v b i))
def Mf (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (v : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  fun a b => herm (Hpk k r) (v b) (fvec k r z a)
def XF (k r : ℕ) : ℝ := ((2 * r + k + 2 : ℕ) : ℝ) ^ 2 + (r : ℝ) ^ 3
def OneSide : Prop :=
  ∃ C : ℕ, ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ0 : Measure (Mt k r)),
    1 ≤ k → 1 ≤ r → C2.StdZ k r z → B.IsHaarOn (C2.N0set k r z) μ0 →
    ∀ (ε B' : ℝ), 0 < ε → (C : ℝ) * XF k r ≤ B' → ∃ K : ℝ, 0 ≤ K ∧
      ∀ v : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ, ε ≤ Complex.normSq (Mf k r z v).det →
        ∫⁻ x, ENNReal.ofReal (tN (fun b => (Matrix.of x : B.Mat k r)⁻¹ *ᵥ v b) ^ (-B')) ∂μ0 ≤
          ENNReal.ofReal (K * (1 + zN (Mf k r z v)) ^ (-(B' - (C : ℝ) * XF k r)))
def PtBound : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' →
    ∃ c : ℝ, 0 < c ∧ ∀ (x : B.SS k r) (g : B.Mat k r),
      Matrix.of x.1.1 ∈ UWset k r z → Matrix.of x.1.2 ∈ C2.N0set k r z →
      Matrix.of x.2.1 ∈ UWset k r z' → Matrix.of x.2.2 ∈ C2.N0set k r z' → g ∈ B.GV k r →
      c * (tN (fun b => (Matrix.of x.1.2 : B.Mat k r)⁻¹ *ᵥ (g *ᵥ fvec k r z' b)) *
          tN (fun a => (Matrix.of x.2.2 : B.Mat k r)⁻¹ *ᵥ (g⁻¹ *ᵥ fvec k r z a))) ≤ B.gN (B.sgs x g) ^ 2
def ZhatAdj : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r), g ∈ B.GV k r →
    Mf k r z' (fun a => g⁻¹ *ᵥ fvec k r z a) = (Zhat k r z z' g)ᴴ
def DetBound : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (ε : ℝ), C2.StdZ k r z → C2.StdZ k r z' →
    ε ≤ Gf k r z z' g → ε ≤ Complex.normSq (Zhat k r z z' g).det
def UWFin : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ : Measure (Mt k r)), 1 ≤ k → C2.StdZ k r z →
    B.IsHaarOn (UWset k r z) μ → μ Set.univ < ⊤
def PosP : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (n : B.Mat k r) (v : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ),
    n ∈ B.GV k r → (Mf k r z v).det ≠ 0 → 0 < tN (fun b => n⁻¹ *ᵥ v b)
def ZNAdj : Prop := ∀ (m : ℕ) (Z : Matrix (Fin m) (Fin m) ℂ), zN Zᴴ = zN Z
end PI.UnitaryGroupMassFormula.DLm


