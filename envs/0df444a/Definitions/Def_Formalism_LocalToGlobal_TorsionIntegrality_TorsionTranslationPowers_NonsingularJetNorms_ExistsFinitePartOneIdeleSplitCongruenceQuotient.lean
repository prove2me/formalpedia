-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ExistsFinitePartOneIdeleSplitCongruenceQuotient
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ExistsFinitePartOneIdeleSplitCongruenceQuotient
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:58:50.742461+00:00
-- url     : https://prove2.me/theorems/e67a280a-8c02-559f-b101-9ab255c33611
-- title:
--   Exists Finite Part One Idele Split Congruence Quotient
-- statement:
--   Definitions and structural lemmas for Exists Finite Part One Idele Split Congruence Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ExistsFinitePartOneIdeleSplitCongruenceQuotient.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Theorems.Thm_Formalism_L2_Th1_F_discNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Th1.E
namespace AddThm
open Formalism.L2.Th1
section Analytic
variable (L : PeriodPair)
end Analytic
variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
theorem disc_ne : (curveL l L ι).Δ ≠ 0 := by
  have h := Formalism.L2.Th1.F.discNeZero L
  have e : (curveL l L ι).Δ = ι (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
    simp only [curveL, Formalism.L2.Th1.A.shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, map_sub, map_mul, map_pow,
      map_ofNat]
    ring
  rw [e]
  exact (map_ne_zero ι).mpr h
theorem nonsing (t : ℂ) (ht : t ∉ L.lattice) :
    (curveL l L ι).toAffine.Nonsingular (ι (L.weierstrassP t)) (ι (L.derivWeierstrassP t) / 2) := by
  haveI : (curveL l L ι).IsElliptic := ⟨(disc_ne l L ι).isUnit⟩
  rw [← WeierstrassCurve.Affine.equation_iff_nonsingular, WeierstrassCurve.Affine.equation_iff]
  have h := congrArg ι (L.derivWeierstrassP_sq t ht)
  simp only [map_sub, map_mul, map_pow, map_ofNat, map_add] at h
  simp only [curveL, Formalism.L2.Th1.A.shortW]
  linear_combination (1 / 4 : ℂ_[l]) * h
end AddThm
variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
section Law
variable [DecidableEq ℂ_[l]]
end Law
end Formalism.L2.Th1.E


