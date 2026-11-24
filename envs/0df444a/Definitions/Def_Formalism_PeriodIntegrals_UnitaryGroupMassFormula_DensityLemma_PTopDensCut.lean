-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PTopDensCut
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PTopDensCut
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T19:29:08.949846+00:00
-- url     : https://prove2.me/theorems/2a2202d2-3eb3-458d-97be-d14d22c875eb
-- title:
--   PTop Dens Cut
-- statement:
--   Definitions and structural lemmas for PTop Dens Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PTopDensCut.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PTopSlice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
namespace PI.UnitaryGroupMassFormula.DLm
def zN {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℂ) : ℝ := Real.sqrt (∑ a, ∑ b, Complex.normSq (Z a b))
def FibreBound : Prop :=
  ∃ C : ℕ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r)),
    1 ≤ r → B.IsHaarOn (C2.N0set k r D.z) μ0 → B.IsHaarOn (C2.N0set k r D.z') μ0' →
    ∀ (ε A : ℝ), 0 < ε → (C : ℝ) * (((2 * r + k + 2 : ℕ) : ℝ) ^ 2 + (r : ℝ) ^ 3) ≤ A → ∃ K : ℝ, 0 ≤ K ∧
      ∀ g ∈ B.GV k r, ε ≤ Gf k r D.z D.z' g →
        ∫⁻ x : B.SS k r, ENNReal.ofReal (B.gN (B.sgs x g) ^ (-A)) ∂((D.μW.prod μ0).prod (D.μW'.prod μ0')) ≤
          ENNReal.ofReal (K * (1 + zN (Zhat k r D.z D.z' g)) ^
            (-(A - (C : ℝ) * (((2 * r + k + 2 : ℕ) : ℝ) ^ 2 + (r : ℝ) ^ 3))))
def DensFramesOf : Prop := FibreBound → TopDensEx
end PI.UnitaryGroupMassFormula.DLm


