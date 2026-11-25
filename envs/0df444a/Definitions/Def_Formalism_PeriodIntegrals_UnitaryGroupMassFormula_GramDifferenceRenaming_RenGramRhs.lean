-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramDifferenceRenaming_RenGramRhs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramDifferenceRenaming_RenGramRhs
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T11:27:40.434965+00:00
-- url     : https://prove2.me/theorems/756290d7-9e15-457a-9125-1c9ec0dc3b93
-- title:
--   Ren Gram Rhs
-- statement:
--   Definitions and structural lemmas for Ren Gram Rhs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramDifferenceRenaming/RenGramRhs.lean

import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_BeMulByZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_expMv_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_good_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_good_sub
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_int_one
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_simeq_iff_good
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_cc_lin
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_C
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_PhOn
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_X
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_be
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_lin
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_psubst
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_simeq_ren

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
namespace PI.UnitaryGroupMassFormula.SDiffGram
open PI.FglGram MvPowerSeries
open PI.UnitaryGroupMassFormula.PhDualGram (ren ren_apply ren_psubst ren_X ren_C simeq_ren cc_lin ren_lin ren_be ren_PhOn)
open PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram (Good simeq_iff_good good_add good_sub expMv_zero int_one)
variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]}
def PhVF (l ex ph : PowerSeries ℂ_[p]) {κ T σ : Type} [Fintype κ] [Fintype T]
    (B : T → κ → ℂ_[p] × ℂ_[p]) (w : T → MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  ∑ k, phAt ph (lin l ex (fun e => (B e k).1) w)
def GR (l ex ph : PowerSeries ℂ_[p]) {κ T σ : Type} [Fintype κ] [Fintype T] {m : ℕ} (o : T → Fin m)
    (B : T → κ → ℂ_[p] × ℂ_[p]) (w : T → MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  ∑ x, C (hP (B x) (B x)).1 * phAt ph (w x) +
    ∑ x, ∑ y, if o x < o y then be l ex ph (mulBy l ex (hP (B x) (B y)).1 (w x)) (w y) else 0
def sdRF (l ex ph : PowerSeries ℂ_[p]) {κ ι ι' : Type} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries (ι ⊕ ι') ℂ_[p] :=
  ∑ f, ∑ f', be l ex ph (mulBy l ex (hP (a f) (a' f')).1 (X (Sum.inl f))) (X (Sum.inr f'))
def sdRF' (l ex ph : PowerSeries ℂ_[p]) {κ ι ι' : Type} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries (ι ⊕ ι') ℂ_[p] :=
  ∑ f, ∑ f', be l ex ph (X (Sum.inl f)) (mulBy l ex (hP (a f) (a' f')).2 (X (Sum.inr f')))
end PI.UnitaryGroupMassFormula.SDiffGram
end


