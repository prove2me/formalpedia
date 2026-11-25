-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockCore
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockCore
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T09:54:28.495099+00:00
-- url     : https://prove2.me/theorems/6d1f0da2-4154-5b76-83ae-0041e8d2e646
-- title:
--   Fock Core
-- statement:
--   Definitions and structural lemmas for Fock Core, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockCore.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
import Theorems.Thm_PI_FHS_fockInner_add_left
import Theorems.Thm_PI_FHS_fockInner_conj
import Theorems.Thm_PI_FHS_fockInner_self_eq_zero
import Theorems.Thm_PI_FHS_fockInner_self_re_nonneg
import Theorems.Thm_PI_FHS_fockInner_smul_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace PI.FHS
variable {σ : Type*}
def FockV (σ : Type*) : Type _ := MvPolynomial σ ℂ
instance : AddCommGroup (FockV σ) := inferInstanceAs (AddCommGroup (MvPolynomial σ ℂ))
instance : Module ℂ (FockV σ) := inferInstanceAs (Module ℂ (MvPolynomial σ ℂ))
@[instance_reducible]
def fockCore : InnerProductSpace.Core ℂ (FockV σ) where
  inner P Q := FockH1Action.fockInner (σ := σ) P Q
  conj_inner_symm x y := fockInner_conj (σ := σ) x y
  re_inner_nonneg x := by simpa using fockInner_self_re_nonneg (σ := σ) x
  add_left x y z := fockInner_add_left (σ := σ) x y z
  smul_left x y r := fockInner_smul_left (σ := σ) r x y
  definite _ h := fockInner_self_eq_zero (σ := σ) h
end PI.FHS


