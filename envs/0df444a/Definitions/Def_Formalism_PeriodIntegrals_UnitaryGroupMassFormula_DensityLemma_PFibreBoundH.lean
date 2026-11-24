-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFibreBoundH
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFibreBoundH
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T20:34:49.854546+00:00
-- url     : https://prove2.me/theorems/fe3db5e1-e260-4a15-a741-ac9fe5a84cef
-- title:
--   PFibre Bound H
-- statement:
--   Definitions and structural lemmas for PFibre Bound H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PFibreBoundH.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFibreBoundVDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open scoped ENNReal NNReal
noncomputable section
namespace PI.UnitaryGroupMassFormula.DLm
def skewOf {r : ℕ} (T : Fin r → Fin r → ℝ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => ((T a b - T b a : ℝ) : ℂ) + Complex.I * ((T a b + T b a : ℝ) : ℂ)
def Pz (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  1 - ((∑ j, Complex.normSq (zW k r z j) : ℝ) : ℂ)⁻¹ • Matrix.vecMulVec (zW k r z) (star (zW k r z))
def psiZ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (p : (Fin r → Fin (k + 1) → ℂ) × (Fin r → Fin r → ℝ)) : Mt k r :=
  unipotentBlockMatrix k r (Matrix.of p.1 * Pz k r z) (skewOf p.2)
def rhoZ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (B0 : Fin r → Fin (k + 1) → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(∑ a, Complex.normSq ((Matrix.of B0 *ᵥ zW k r z) a))))
def nuZ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Measure (Mt k r) :=
  (((volume : Measure (Fin r → Fin (k + 1) → ℂ)).withDensity (rhoZ k r z)).prod
    (volume : Measure (Fin r → Fin r → ℝ))).map (psiZ k r z)
def UnipotentHaarMultipleExplicit : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ0 : Measure (Mt k r)), 1 ≤ k → 1 ≤ r → C2.StdZ k r z →
    B.IsHaarOn (C2.N0set k r z) μ0 → ∃ c : ℝ≥0, 0 < c ∧ nuZ k r z = c • μ0
def ExplicitUnipotentVolumeBound : Prop :=
  ∃ C : ℕ, ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z →
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 ≤ K ∧
      ∀ v : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ, ε ≤ Complex.normSq (Mf k r z v).det → ∀ R : ℝ, 0 ≤ R →
        nuZ k r z {x | (Matrix.of x : B.Mat k r) ∈ C2.N0set k r z ∧
            tN (fun b => (Matrix.of x : B.Mat k r)⁻¹ *ᵥ v b) ≤ R} ≤
          ENNReal.ofReal (K * (1 + zN (Mf k r z v)) ^ ((C : ℝ) * XF k r) * (1 + R) ^ ((C : ℝ) * XF k r))
end PI.UnitaryGroupMassFormula.DLm


