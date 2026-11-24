-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobVol
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobVol
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T22:13:14.29171+00:00
-- url     : https://prove2.me/theorems/6b16d1eb-12b5-40d5-9a81-e9f9ec27d248
-- title:
--   Glob Vol
-- statement:
--   Definitions and structural lemmas for Glob Vol, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/GlobVol.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_IdealPowPrincipal
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_theta_mem
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_theta_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NumberField ComplexConjugate
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
section Vol
variable (F : IntermediateField ℚ ℂ) {m : Type} [Fintype m] [DecidableEq m]
end Vol
def thetaO {a : ℕ} {b c : ℤ} {d : ℕ} (hok : UnitDetRootDefs.CmOK a b c d) : 𝓞 (KF b d) :=
  ⟨⟨UnitDetRootDefs.cmTheta b d, theta_mem b d⟩, by
    rw [mem_integralClosure_iff]
    refine ⟨Polynomial.X ^ 2 - Polynomial.C b * Polynomial.X + Polynomial.C ((a : ℤ) * c), ?_, ?_⟩
    · monicity!
    · apply (KF b d).val.injective
      have h : ((KF b d).val.toRingHom) ((Polynomial.X ^ 2 - Polynomial.C b * Polynomial.X +
          Polynomial.C ((a : ℤ) * c)).eval₂ (algebraMap ℤ (KF b d)) ⟨UnitDetRootDefs.cmTheta b d, theta_mem b d⟩)
          = (Polynomial.X ^ 2 - Polynomial.C b * Polynomial.X +
          Polynomial.C ((a : ℤ) * c)).eval₂ (Int.castRingHom ℂ) (UnitDetRootDefs.cmTheta b d) := by
        rw [Polynomial.hom_eval₂, RingHom.ext_int ((KF b d).val.toRingHom.comp (algebraMap ℤ (KF b d)))
          (Int.castRingHom ℂ)]
        rfl
      change ((KF b d).val.toRingHom) _ = (KF b d).val 0
      rw [h, map_zero]
      rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
        Polynomial.eval₂_C, Polynomial.eval₂_C, Polynomial.eval₂_X]
      simp only [eq_intCast, Int.cast_mul, Int.cast_natCast]
      linear_combination theta_sq hok⟩
end PI.UnitaryGroupMassFormula.UnitDetRoot


