-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsIntegralGaugedFormalGroupLawSelfConjugateSquar
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsIntegralGaugedFormalGroupLawSelfConjugateSquar
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-27T05:03:35.908835+00:00
-- url     : https://prove2.me/theorems/8fd471e0-0c14-5039-b6f2-0c3a4f87c2f5
-- title:
--   Is Integral Gauged Formal Group Law Self Conjugate Squar
-- statement:
--   Definitions and structural lemmas for Is Integral Gauged Formal Group Law Self Conjugate Squar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IsIntegralGaugedFormalGroupLawSelfConjugateSquar.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_neg
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_neg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_add
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MvPowerSeries Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace GlobalTheory.RowLawSquare
section Series
variable {C : Type} [Field C] {σ τ : Type}
def intSer (V : VF C) (σ : Type) : Subring (MvPowerSeries σ C) where
  carrier := {f | IntS V f}
  mul_mem' := by
    classical
    intro f g hf hg μ
    rw [coeff_mul]
    exact VF.Ge.sum fun p _ => (hf _).mul_int (hg _)
  one_mem' := by
    classical
    intro μ
    rw [coeff_one]
    split_ifs
    · exact VF.Ge.one
    · exact VF.Ge.zero 0
  add_mem' := fun hf hg μ => by rw [map_add]; exact (hf μ).add (hg μ)
  zero_mem' := fun μ => by rw [map_zero]; exact VF.Ge.zero 0
  neg_mem' := fun hf μ => by rw [map_neg]; exact (hf μ).neg
variable {dd : ℕ}
def sb {n : ℕ} (a : Fin n → Fin dd → MvPowerSeries τ C) (f : PS C n dd) : MvPowerSeries τ C :=
  subst (fun p : Fin n × Fin dd => a p.1 p.2) f
def Zc {ι : Type} (a : ι → MvPowerSeries τ C) : Prop := ∀ i, constantCoeff (a i) = 0
end Series
section Chart
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd) {τ : Type}
def law (a b : Fin dd → MvPowerSeries τ C) : Fin dd → MvPowerSeries τ C := fun i => sb ![a, b] (Y.B.G.F i)
variable {d : ℕ} {I0 : Type} [Fintype I0] (p : SelfData Y d I0)
def colOf (a : Fin 2 × Fin dd → MvPowerSeries τ C) (col : Fin 2) : Fin dd → MvPowerSeries τ C := fun x => a (col, x)
end Chart
end GlobalTheory.RowLawSquare


