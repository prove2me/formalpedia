-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_IoExistsOfCap
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_IoExistsOfCap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:15.863227+00:00
-- url     : https://prove2.me/theorems/9abcdee0-4b7e-4f5d-b576-1c2ed9a72586
-- title:
--   Io Exists Of Cap
-- statement:
--   Definitions and structural lemmas for Io Exists Of Cap, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/IoExistsOfCap.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
import Definitions.Def_Formalism_PeriodIntegrals_GTBranch
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WGL
open Formalism.BasicNotions MvPolynomial
def capP {n : ℕ} (mu : DomWeight n) (u : ℂ) : ℂ :=
  ∏ k : Fin n, (u - ((k : ℕ) : ℂ) + ((mu.w k : ℤ) : ℂ))
def CapFacts : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∃ C : ℂ → Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ),
      (∀ mu : DomWeight n, Interlace h lam mu →
        ∀ φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ, IsEqv h mu lam φ →
          ∀ s ∈ nablaSq ℂ n mu, ∀ u, C u (φ s) = capP mu u • φ s) ∧
      ∀ u, C u (xi ℂ h lam sg) = capP sg u • xi ℂ h lam sg
def ioSqActL (k : ℕ) (mu : DomWeight k) (g : GL (Fin k) ℂ) :
    MvPolynomial (Fin k × Fin k) ℂ →ₗ[ℂ] MvPolynomial (Fin k × Fin k) ℂ :=
  detPow ℂ k g mu.detShift • (Formalism.GradedWeylDivisibility.rowAct ℂ (n := k) (g : Matrix (Fin k) (Fin k) ℂ).transpose).toLinearMap
end PI.WGL


