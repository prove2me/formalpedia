-- Prove2me | Definitions.Def_OAIQ019N041
-- name    : OAIQ019N041
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:06:51.348645+00:00
-- url     : https://prove2.me/theorems/e7e9c09e-c172-4982-b88a-648e35b4359b
-- title:
--   Definitions bundle OAIQ019N041 of the split of OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 45 declarations of OpenAI's Lean: 19 definitions, 7 instances and 19 theorems. The definitions and types are `OAI.NuclearUltrapower.MainStatement`, `OAI.NuclearUltrapower.SL3Certificate.columns`, `OAI.NuclearUltrapower.SL3Certificate.gram`, `OAI.NuclearUltrapower.SOS.gramData`, `OAI.NuclearUltrapower.UniversalGNS`, `OAI.NuclearUltrapower.VariableUltra.gapQuotientOrder`, `OAI.NuclearUltrapower.VariableUltra.gapSeqOrder`, `OAI.NuclearUltrapower.VariableUltra.normQuotientOrder`, `OAI.NuclearUltrapower.VariableUltra.operatorQuotientOrder`, `OAI.NuclearUltrapower.VariableUltra.quotientOrder`, `OAI.NuclearUltrapower.boundedSeqToLp`, `OAI.NuclearUltrapower.finiteSubspaceRep`, `OAI.NuclearUltrapower.normUltraToCStar`, `OAI.NuclearUltrapower.restrictSubgroup`, `OAI.NuclearUltrapower.scalarHilbert`, `OAI.NuclearUltrapower.supportHilbert`, `OAI.NuclearUltrapower.tensorPiIsometry`, `OAI.NuclearUltrapower.tensorPiUnitary`, `OAI.NuclearUltrapower.universalGNS`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `NuclearUltrapower_FaithfulGNS`, `NuclearUltrapower_FiniteInduction`, `NuclearUltrapower_FullGroupAlgebra`, `NuclearUltrapower_HilbertInduction`, `NuclearUltrapower_InitialMatching`, `NuclearUltrapower_IntegralCertificate`, `NuclearUltrapower_NormUltrapower`, `NuclearUltrapower_Obstruction`, `NuclearUltrapower_SOSCertificate`, `NuclearUltrapower_Schur`, `NuclearUltrapower_TensorGap`, `NuclearUltrapower_TensorNorms`, `NuclearUltrapower_VariableUltraproduct`.
--
--   **Imports.** It imports the published bundle `Def_NuclearUltrapower`; the bundles `OAIQ019N000`, `OAIQ019N001`, `OAIQ019N002`, `OAIQ019N003`, `OAIQ019N004`, `OAIQ019N005`, `OAIQ019N006`, `OAIQ019N007`, `OAIQ019N008`, `OAIQ019N009`, `OAIQ019N010`, `OAIQ019N011`, `OAIQ019N012`, `OAIQ019N013`, `OAIQ019N014`, `OAIQ019N015`, `OAIQ019N016`, `OAIQ019N017`, `OAIQ019N018`, `OAIQ019N019`, `OAIQ019N020`, `OAIQ019N021`, `OAIQ019N022`, `OAIQ019N023`, `OAIQ019N024`, `OAIQ019N025`, `OAIQ019N026`, `OAIQ019N027`, `OAIQ019N028`, `OAIQ019N029`, `OAIQ019N030`, `OAIQ019N031`, `OAIQ019N032`, `OAIQ019N033`, `OAIQ019N034`, `OAIQ019N035`, `OAIQ019N036`, `OAIQ019N037` and `OAIQ019N038` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ019N043`; the statements `OAI.NuclearUltrapower.SL3Certificate.gram_row_100`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_101`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_102`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_103`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_104`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_105`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_106`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_107`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_108`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_109`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_110`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_111`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_112`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_113`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_114`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_115`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_116`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_117`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_118`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_119`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_120`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_20`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_21`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_22`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_23`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_24`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_25`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_26`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_27`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_28`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_29`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_30`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_31`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_32`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_33`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_34`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_35`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_36`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_37`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_38`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_39`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_40`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_41`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_42`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_43`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_44`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_45`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_46`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_47`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_48`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_49`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_50`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_51`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_52`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_53`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_54`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_55`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_56`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_57`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_58`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_59`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_60`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_61`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_62`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_63`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_64`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_65`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_66`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_67`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_68`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_69`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_70`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_71`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_72`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_73`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_74`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_75`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_76`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_77`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_78`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_79`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_80`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_81`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_82`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_83`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_84`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_85`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_86`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_87`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_88`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_89`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_90`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_91`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_92`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_93`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_94`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_95`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_96`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_97`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_98`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_99`, `OAI.NuclearUltrapower.SOS.gramData_eq`, `OAI.NuclearUltrapower.SOS.gramData_roots`, `OAI.NuclearUltrapower.main_statement` and `OAI.NuclearUltrapower.universalGNS_injective`; the proofs of `OAI.NuclearUltrapower.CuntzAveraging.commutingEval_norm_le_min`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_100`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_101`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_102`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_103`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_104`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_105`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_106`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_107`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_108`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_109`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_110`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_111`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_112`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_113`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_114`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_115`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_116`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_117`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_118`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_119`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_120`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_20`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_21`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_22`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_23`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_24`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_25`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_26`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_27`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_28`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_29`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_30`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_31`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_32`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_33`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_34`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_35`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_36`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_37`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_38`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_39`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_40`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_41`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_42`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_43`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_44`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_45`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_46`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_47`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_48`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_49`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_50`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_51`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_52`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_53`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_54`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_55`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_56`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_57`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_58`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_59`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_60`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_61`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_62`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_63`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_64`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_65`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_66`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_67`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_68`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_69`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_70`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_71`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_72`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_73`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_74`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_75`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_76`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_77`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_78`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_79`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_80`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_81`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_82`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_83`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_84`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_85`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_86`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_87`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_88`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_89`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_90`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_91`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_92`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_93`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_94`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_95`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_96`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_97`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_98`, `OAI.NuclearUltrapower.SL3Certificate.gram_row_99`, `OAI.NuclearUltrapower.SOS.gramData_eq`, `OAI.NuclearUltrapower.SOS.gramData_roots`, `OAI.NuclearUltrapower.main_no_embedding` and `OAI.NuclearUltrapower.universalGNS_injective`.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_NuclearUltrapower
import Definitions.Def_OAIQ019N000
import Definitions.Def_OAIQ019N001
import Definitions.Def_OAIQ019N002
import Definitions.Def_OAIQ019N003
import Definitions.Def_OAIQ019N004
import Definitions.Def_OAIQ019N005
import Definitions.Def_OAIQ019N006
import Definitions.Def_OAIQ019N007
import Definitions.Def_OAIQ019N008
import Definitions.Def_OAIQ019N009
import Definitions.Def_OAIQ019N010
import Definitions.Def_OAIQ019N011
import Definitions.Def_OAIQ019N012
import Definitions.Def_OAIQ019N013
import Definitions.Def_OAIQ019N014
import Definitions.Def_OAIQ019N015
import Definitions.Def_OAIQ019N016
import Definitions.Def_OAIQ019N017
import Definitions.Def_OAIQ019N018
import Definitions.Def_OAIQ019N019
import Definitions.Def_OAIQ019N020
import Definitions.Def_OAIQ019N021
import Definitions.Def_OAIQ019N022
import Definitions.Def_OAIQ019N023
import Definitions.Def_OAIQ019N024
import Definitions.Def_OAIQ019N025
import Definitions.Def_OAIQ019N026
import Definitions.Def_OAIQ019N027
import Definitions.Def_OAIQ019N028
import Definitions.Def_OAIQ019N029
import Definitions.Def_OAIQ019N030
import Definitions.Def_OAIQ019N031
import Definitions.Def_OAIQ019N032
import Definitions.Def_OAIQ019N033
import Definitions.Def_OAIQ019N034
import Definitions.Def_OAIQ019N035
import Definitions.Def_OAIQ019N036
import Definitions.Def_OAIQ019N037
import Definitions.Def_OAIQ019N038

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_FullGroupAlgebra
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped MonoidAlgebra
namespace NuclearUltrapower.GroupStarAlgebra
variable {Γ : Type*} [Group Γ]

instance instStarRingMonoidAlgebraComplex_solutions : StarRing ℂ[Γ] where
  star_add := star_add'
  star_mul x y := by
    induction x using MonoidAlgebra.induction_on with
    | of a =>
      induction y using MonoidAlgebra.induction_on with
      | of b => simp only [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single,
          one_mul, star_single, star_one, mul_inv_rev]
      | add y z hy hz => simp only [mul_add, star_add, hy, hz, add_mul]
      | smul c y hy => simp only [mul_smul_comm, star_smul, hy, smul_mul_assoc]
    | add x z hx hz => simp only [add_mul, star_add, hx, hz, mul_add]
    | smul c x hx => simp only [smul_mul_assoc, star_smul, hx, mul_smul_comm]

end NuclearUltrapower.GroupStarAlgebra

namespace NuclearUltrapower.GroupStarAlgebra
open scoped MonoidAlgebra
variable {Γ : Type} [Group Γ]

instance instNormedStarGroupMonoidAlgebraComplex_solutions : NormedStarGroup ℂ[Γ] where
  norm_star_le x := by
    apply universalNorm_le
    intro D _ ρ
    simpa only [map_star, norm_star, norm_eq_universalNorm] using model_norm_le x D ρ

/-- C*-identity at the seminorm level, which survives separated completion. -/
theorem norm_mul_self_le (x : ℂ[Γ]) : ‖x‖ * ‖x‖ ≤ ‖star x * x‖ := by
  have h : ‖x‖ ≤ Real.sqrt ‖star x * x‖ := by
    apply universalNorm_le
    intro D _ ρ
    apply (Real.le_sqrt (norm_nonneg _) (norm_nonneg _)).mpr
    have hm := model_norm_le (star x*x) D ρ
    simpa only [map_mul, map_star, CStarRing.norm_star_mul_self, pow_two, norm_eq_universalNorm] using hm
  nlinarith [Real.sq_sqrt (norm_nonneg (star x*x)), norm_nonneg x]

/-- Every model evaluation is contractive for the universal seminorm. -/
theorem evaluate_continuous {D : Type} [CStarAlgebra D] (ρ : Γ →* unitary D) :
    Continuous (evaluate ρ) := by
  apply (evaluate ρ).toLinearMap.mkContinuous 1 ?_ |>.continuous
  intro x
  change ‖evaluate ρ x‖ ≤ 1 * universalNorm x
  simpa only [one_mul] using model_norm_le x D ρ

end NuclearUltrapower.GroupStarAlgebra

noncomputable section
open UniformSpace
namespace NuclearUltrapower.UniversalCompletion

variable {R : Type*} [SeminormedRing R] [StarRing R] [NormedStarGroup R]

instance completionNormedStar : NormedStarGroup (Completion R) where
  norm_star_le x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) continuous_norm
    | ih x => simp

end NuclearUltrapower.UniversalCompletion

end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_FaithfulGNS
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
universe u
open scoped ComplexOrder ENNReal
namespace NuclearUltrapower
variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

attribute [local instance] OAI.NuclearUltrapower.gnsSpectralOrder
attribute [local instance] OAI.NuclearUltrapower.gnsSpectralOrderedRing
/-- Universal GNS Hilbert space, with all positive functionals as coordinates. -/
abbrev UniversalGNS (A : Type u) [CStarAlgebra A] :=
  lp (fun f : A →ₚ[ℂ] ℂ => f.GNS) 2

/-- The faithful unital Hilbert representation obtained by summing the GNS
representations of all positive functionals. -/
def universalGNS : A →⋆ₐ[ℂ] (UniversalGNS A →L[ℂ] UniversalGNS A) where
  toFun a := hilbertDiagonal (fun f : A →ₚ[ℂ] ℂ => f.gnsStarAlgHom a) ‖a‖
    (norm_nonneg a) (fun f => NonUnitalStarAlgHom.norm_apply_le f.gnsStarAlgHom a)
  map_zero' := by ext x f; simp
  map_one' := by ext x f; simp
  map_add' a b := by ext x f; simp
  map_mul' a b := by ext x f; simp
  commutes' c := by
    ext x f
    change f.gnsStarAlgHom (algebraMap ℂ A c) (x f) = c • x f
    exact congrArg (fun T : f.GNS →L[ℂ] f.GNS => T (x f)) (f.gnsStarAlgHom.commutes c)
  map_star' a := by
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    simp only [lp.inner_eq_tsum, hilbertDiagonal_apply]
    apply tsum_congr
    intro f
    calc
      _ = inner ℂ ((star (f.gnsStarAlgHom a)) (x f)) (y f) :=
        congrArg (fun T : f.GNS →L[ℂ] f.GNS => inner ℂ (T (x f)) (y f)) (map_star f.gnsStarAlgHom a)
      _ = _ := ContinuousLinearMap.adjoint_inner_left _ _ _

@[simp] theorem universalGNS_apply (a : A) (x : UniversalGNS A) (f : A →ₚ[ℂ] ℂ) :
    universalGNS a x f = f.gnsStarAlgHom a (x f) := rfl

end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_HilbertInduction
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped ENNReal InnerProductSpace
namespace NuclearUltrapower
universe u v

section Induction
variable {G : Type u} [Group G] (H : Subgroup G)

variable {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (α : H →* (V ≃ₗᵢ[ℂ] V))

@[simp] theorem cosetRep_smul_identity (i : G ⧸ H) :
    cosetRep H i • (QuotientGroup.mk 1 : G ⧸ H) = i := by
  change (QuotientGroup.mk (cosetRep H i * 1) : G ⧸ H) = i
  simpa using cosetRep_mk H i

end Induction
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_Schur
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End
noncomputable section
open scoped CStarAlgebra
noncomputable section
open Filter
open scoped Topology ENNReal
noncomputable section
open scoped InnerProductSpace

namespace NuclearUltrapower
open scoped TensorProduct

section FiniteSubspace
variable {Γ : Type u} [Group Γ]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (σ : Γ →* (K ≃ₗᵢ[ℂ] K))
  (W : Submodule ℂ K) [Nontrivial W] [FiniteDimensional ℂ W]
  (hW : ∀ g x, x ∈ W → σ g x ∈ W)

/-- The honest finite-dimensional subrepresentation on an invariant subspace. -/
def finiteSubspaceRep : FiniteUnitaryRep.{u,v} Γ where
  carrier := W
  action := {
    toFun g := {
      toFun x := ⟨σ g x, hW g x x.property⟩
      invFun x := ⟨σ g⁻¹ x, hW g⁻¹ x x.property⟩
      left_inv x := by ext; change (σ g⁻¹ * σ g) x.val = x.val; rw [← map_mul]; simp
      right_inv x := by ext; change (σ g * σ g⁻¹) x.val = x.val; rw [← map_mul]; simp
      map_add' x y := by ext; simp
      map_smul' c x := by ext; simp
      norm_map' x := (σ g).norm_map x }
    map_one' := by ext; simp
    map_mul' g h := by ext; simp [map_mul] }

end FiniteSubspace
end NuclearUltrapower

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_FiniteInduction
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace ENNReal
namespace NuclearUltrapower
universe u

section FiniteInduction
variable {Γ : Type u} [Group Γ] (H : Subgroup Γ) [Finite (Γ ⧸ H)]
    (α : FiniteUnitaryRep.{u,u} H)

/-- Restriction changes only the action, not the Hilbert carrier. -/
def restrictSubgroup (σ : FiniteUnitaryRep.{u,u} Γ) : FiniteUnitaryRep.{u,u} H :=
  { σ with action := σ.action.comp H.subtype }

end FiniteInduction
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_VariableUltraproduct
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.instStarRingNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End
noncomputable section
open scoped CStarAlgebra
noncomputable section
open Filter
open scoped Topology ENNReal
namespace NuclearUltrapower

namespace VariableUltra
variable {ι : Type u} (A : ι → Type v) [∀ i, CStarAlgebra (A i)]
  [∀ i, Nontrivial (A i)] (ω : Ultrafilter ι)

instance instNontrivialAlgebra : Nontrivial (Algebra A ω) := by
  apply nontrivial_of_ne (1 : Algebra A ω) 0
  intro h
  have hn : ‖(1 : Algebra A ω)‖ = 1 := by
    change ‖mk A ω 1‖ = 1
    rw [mk_norm]
    exact tendsto_nhds_unique (seqNorm_tendsto A ω 1) (by
      change Tendsto (fun i : ι => ‖(1 : A i)‖) (ω : Filter ι) (𝓝 1)
      simpa only [norm_one] using
        (tendsto_const_nhds : Tendsto (fun _ : ι => (1 : ℝ)) (ω : Filter ι) (𝓝 1)))
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

end VariableUltra
end NuclearUltrapower

namespace NuclearUltrapower
namespace VariableUltra
open scoped WithCStarModule

variable {ι : Type u} (A : ι → Type v) [∀ i, CStarAlgebra (A i)]
  [∀ i, Nontrivial (A i)] (ω : Ultrafilter ι)
variable (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n]

local instance quotientOrder : PartialOrder (Algebra A ω) := CStarAlgebra.spectralOrder _
attribute [local instance] OAI.NuclearUltrapower.VariableUltra.entryOrder
local instance quotientStarOrder : StarOrderedRing (Algebra A ω) := CStarAlgebra.spectralOrderedRing _

end VariableUltra
end NuclearUltrapower

namespace NuclearUltrapower

namespace VariableUltra
variable {ι : Type u} (A : ι → Type v) [∀ i, CStarAlgebra (A i)]
  [∀ i, Nontrivial (A i)] (ω : Ultrafilter ι)
variable (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n]
local instance normQuotientOrder : PartialOrder (Algebra A ω) := CStarAlgebra.spectralOrder _
attribute [local instance] OAI.NuclearUltrapower.VariableUltra.normEntryOrder
local instance seqOrder_r7786b5_1 : PartialOrder (Seq A) := CStarAlgebra.spectralOrder _
local instance seqStarOrder_r7786b5_1 : StarOrderedRing (Seq A) := CStarAlgebra.spectralOrderedRing _
local instance normQuotientStarOrder : StarOrderedRing (Algebra A ω) := CStarAlgebra.spectralOrderedRing _

end VariableUltra
end NuclearUltrapower

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_TensorGap
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.instStarRingNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End
noncomputable section
open scoped CStarAlgebra
noncomputable section
open Filter
open scoped Topology ENNReal
noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower

open scoped TensorProduct
section TensorMatrix
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

@[simp] theorem tensorPiLinearEquiv_tmul (b : OrthonormalBasis n ℂ F)
    (x : E) (y : F) (i : n) : tensorPiLinearEquiv b (x ⊗ₜ[ℂ] y) i = b.repr y i • x := by
  simp [tensorPiLinearEquiv]

theorem tensorPiLinearEquiv_inner (b : OrthonormalBasis n ℂ F) (z w : E ⊗[ℂ] F) :
    inner ℂ (tensorPiLinearEquiv b z) (tensorPiLinearEquiv b w) = inner ℂ z w := by
  induction z using OAI.tensorInductionOn with
  | add z z' hz hz' => simp [hz, hz', TensorProduct.inner_def]
  | tmul x y =>
    induction w using OAI.tensorInductionOn with
    | add w w' hw hw' => simp [hw, hw', TensorProduct.inner_def]
    | tmul x' y' =>
      simp only [PiLp.inner_apply, tensorPiLinearEquiv_tmul, inner_smul_left, inner_smul_right,
        TensorProduct.inner_tmul]
      calc
        _ = (∑ i, starRingEnd ℂ (b.repr y i) * b.repr y' i) * inner ℂ x x' := by
          simp only [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = inner ℂ y y' * inner ℂ x x' := by
          congr 1
          simpa only [PiLp.inner_apply, RCLike.inner_apply, mul_comm] using b.repr.inner_map_map y y'
        _ = _ := mul_comm _ _

def tensorPiIsometry (b : OrthonormalBasis n ℂ F) :
    E ⊗[ℂ] F ≃ₗᵢ[ℂ] PiLp 2 (fun _ : n => E) :=
  (tensorPiLinearEquiv b).isometryOfInner (tensorPiLinearEquiv_inner b)

@[simp] theorem tensorPiIsometry_tmul (b : OrthonormalBasis n ℂ F)
    (x : E) (y : F) (i : n) : tensorPiIsometry b (x ⊗ₜ[ℂ] y) i = b.repr y i • x :=
  tensorPiLinearEquiv_tmul b x y i

end TensorMatrix
end NuclearUltrapower

namespace NuclearUltrapower
open scoped TensorProduct
section MatrixGap
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

def tensorPiUnitary (b : OrthonormalBasis n ℂ F) (U : E ≃ₗᵢ[ℂ] E) (V : F ≃ₗᵢ[ℂ] F) :
    PiLp 2 (fun _ : n => E) ≃ₗᵢ[ℂ] PiLp 2 (fun _ : n => E) :=
  ((tensorPiIsometry b).symm.trans (TensorProduct.congrIsometry U V)).trans (tensorPiIsometry b)

omit [CompleteSpace E] in
@[simp] theorem tensorPiUnitary_apply_tensorPi (b : OrthonormalBasis n ℂ F)
    (U : E ≃ₗᵢ[ℂ] E) (V : F ≃ₗᵢ[ℂ] F) (z : E ⊗[ℂ] F) :
    tensorPiUnitary b U V (tensorPiIsometry b z) =
      tensorPiIsometry b (TensorProduct.congrIsometry U V z) := by
  simp [tensorPiUnitary]

end MatrixGap
end NuclearUltrapower

namespace NuclearUltrapower

section CoefficientMatrix
variable {A B Γ n : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [Fintype n] [DecidableEq n]

@[simp] theorem map_laplacian (φ : A →⋆ₐ[ℂ] B) (S : Finset Γ) (a : Γ → A) :
    φ (laplacian S a) = laplacian S (fun s => φ (a s)) := by
  simp only [laplacian, map_sum, map_mul, map_star, map_sub, map_one]

@[simp] theorem map_laplacian_complement (φ : A →⋆ₐ[ℂ] B) (S : Finset Γ)
    (a : Γ → A) (R : ℝ) :
    φ (R • (1 : A) - laplacian S a) = R • (1 : B) - laplacian S (fun s => φ (a s)) := by
  rw [map_sub, show φ (R • (1 : A)) = R • φ 1 from φ.toAlgHom.map_smul_of_tower _ _]
  simp only [map_one, map_laplacian]

end CoefficientMatrix

namespace VariableUltra
variable {ι : Type u} (A : ι → Type v) [∀ i, CStarAlgebra (A i)]
  [∀ i, Nontrivial (A i)] (ω : Ultrafilter ι)

variable (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n]
local instance gapSeqOrder : PartialOrder (Seq A) := CStarAlgebra.spectralOrder _
local instance gapQuotientOrder : PartialOrder (Algebra A ω) := CStarAlgebra.spectralOrder _
attribute [local instance] OAI.NuclearUltrapower.VariableUltra.gapEntryOrder
local instance gapSeqStarOrder_r7786b5_1 : StarOrderedRing (Seq A) := CStarAlgebra.spectralOrderedRing _
local instance gapQuotientStarOrder : StarOrderedRing (Algebra A ω) := CStarAlgebra.spectralOrderedRing _

end VariableUltra
end NuclearUltrapower

namespace NuclearUltrapower
open scoped TensorProduct

namespace VariableUltra
variable {ι : Type u} (E : ι → Type v)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)] [∀ i, Nontrivial (E i)] (ω : Ultrafilter ι)

variable {K F : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

local instance operatorQuotientOrder : PartialOrder (operatorQuotient E ω) :=
  CStarAlgebra.spectralOrder _
end VariableUltra
end NuclearUltrapower

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_TensorNorms
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End
noncomputable section
open scoped CStarAlgebra
noncomputable section
open Filter
open scoped Topology ENNReal
noncomputable section
open scoped InnerProductSpace
noncomputable section
open scoped TensorProduct InnerProductSpace
noncomputable section
open scoped TensorProduct

noncomputable section
open scoped InnerProductSpace TensorProduct

namespace NuclearUltrapower
open scoped TensorProduct

section SpatialSupport
variable {B : Type u} {C : Type v} [CStarAlgebra B] [CStarAlgebra C]

local instance tensorSupportBoundedSMul_r7786b5_1 (H K : ComplexHilbert.{w}) :
    IsBoundedSMul ℂ (H ⊗[ℂ] K) := NormedSpace.toIsBoundedSMul
abbrev supportHilbert (H : ComplexHilbert.{w}) (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    ComplexHilbert.{w} where
  carrier := representationSupport ρ

end SpatialSupport
end NuclearUltrapower

end
end
end
end
end
end
end
end

section

noncomputable section
open scoped TensorProduct
namespace NuclearUltrapower

section Bounds
variable {A C : Type} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra C]

attribute [local instance] OAI.NuclearUltrapower.instIsBoundedSMulComplexTensorProductCarrier
def scalarHilbert : ComplexHilbert.{0} := ⟨ℂ⟩

end Bounds
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_InitialMatching
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Topology InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u v

section Bounds
variable {Γ : Type u} [Group Γ] {B E : Type v} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (S : Finset Γ) (u : Γ → unitary B)
attribute [local instance] OAI.NuclearUltrapower.instPartialOrder_solutions
local instance instStarOrderedRing_solutions : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

end Bounds
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSCertificate
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/- Exact rational SOS data. All asserted computed identities reduce in the
   stock Lean kernel; the numerical program and these literals are untrusted. -/
namespace NuclearUltrapower.SL3Certificate
def columns : List (List ℤ) := [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31, q32, q33, q34, q35, q36, q37, q38, q39, q40, q41, q42, q43, q44, q45, q46, q47, q48, q49, q50, q51, q52, q53, q54, q55, q56, q57, q58, q59, q60, q61, q62, q63, q64, q65, q66, q67, q68, q69, q70, q71, q72, q73, q74, q75, q76, q77, q78, q79, q80, q81, q82, q83, q84, q85, q86, q87, q88, q89, q90, q91, q92, q93, q94, q95, q96, q97, q98, q99, q100, q101, q102, q103, q104, q105, q106, q107, q108, q109, q110, q111, q112, q113, q114, q115, q116, q117, q118, q119, q120]
def gram : List (List ℤ) := [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47, g48, g49, g50, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61, g62, g63, g64, g65, g66, g67, g68, g69, g70, g71, g72, g73, g74, g75, g76, g77, g78, g79, g80, g81, g82, g83, g84, g85, g86, g87, g88, g89, g90, g91, g92, g93, g94, g95, g96, g97, g98, g99, g100, g101, g102, g103, g104, g105, g106, g107, g108, g109, g110, g111, g112, g113, g114, g115, g116, g117, g118, g119, g120]
end NuclearUltrapower.SL3Certificate
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_IntegralCertificate
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SL3Certificate
variable {A : Type*} [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]

@[simp] theorem dot_nil_left (r : List ℤ) : dot [] r = 0 := by cases r <;> rfl
@[simp] theorem dot_nil_right (q : List ℤ) : dot q [] = 0 := by cases q <;> rfl

end NuclearUltrapower.SL3Certificate
end

section

namespace NuclearUltrapower.SOS
open NuclearUltrapower.SL3Certificate
def gramData : List (List ℤ) := [gramRow0, gramRow1, gramRow2, gramRow3, gramRow4, gramRow5, gramRow6, gramRow7, gramRow8, gramRow9, gramRow10, gramRow11, gramRow12, gramRow13, gramRow14, gramRow15, gramRow16, gramRow17, gramRow18, gramRow19, gramRow20, gramRow21, gramRow22, gramRow23, gramRow24, gramRow25, gramRow26, gramRow27, gramRow28, gramRow29, gramRow30, gramRow31, gramRow32, gramRow33, gramRow34, gramRow35, gramRow36, gramRow37, gramRow38, gramRow39, gramRow40, gramRow41, gramRow42, gramRow43, gramRow44, gramRow45, gramRow46, gramRow47, gramRow48, gramRow49, gramRow50, gramRow51, gramRow52, gramRow53, gramRow54, gramRow55, gramRow56, gramRow57, gramRow58, gramRow59, gramRow60, gramRow61, gramRow62, gramRow63, gramRow64, gramRow65, gramRow66, gramRow67, gramRow68, gramRow69, gramRow70, gramRow71, gramRow72, gramRow73, gramRow74, gramRow75, gramRow76, gramRow77, gramRow78, gramRow79, gramRow80, gramRow81, gramRow82, gramRow83, gramRow84, gramRow85, gramRow86, gramRow87, gramRow88, gramRow89, gramRow90, gramRow91, gramRow92, gramRow93, gramRow94, gramRow95, gramRow96, gramRow97, gramRow98, gramRow99, gramRow100, gramRow101, gramRow102, gramRow103, gramRow104, gramRow105, gramRow106, gramRow107, gramRow108, gramRow109, gramRow110, gramRow111, gramRow112, gramRow113, gramRow114, gramRow115, gramRow116, gramRow117, gramRow118, gramRow119, gramRow120]
end NuclearUltrapower.SOS
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_NormUltrapower
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology ENNReal
namespace NuclearUltrapower
universe u
variable (B : Type u) [CStarAlgebra B] [Nontrivial B] (ω : Ultrafilter ℕ)

/-- The two standard bounded-sequence presentations agree coordinatewise. -/
def boundedSeqToLp : BoundedSeq B →⋆ₐ[ℂ] VariableUltra.Seq (fun _ : ℕ => B) where
  toFun x := ⟨(fun n => x n), memℓp_infty ⟨‖x‖, by
    rintro _ ⟨n,rfl⟩
    exact x.norm_coe_le_norm n⟩⟩
  map_zero' := by ext n; rfl
  map_add' _ _ := by ext n; rfl
  map_one' := by ext n; rfl
  map_mul' _ _ := by ext n; rfl
  map_star' _ := by ext n; rfl
  commutes' _ := by ext n; rfl

@[simp] theorem boundedSeqToLp_apply (x : BoundedSeq B) (n : ℕ) :
    boundedSeqToLp B x n = x n := rfl

/-- Endow the norm-null ring quotient with its canonical C*-model,
without replacing the norm-null ideal by any algebraic relation. -/
def normUltraToCStar : NormUltrapower B ω →⋆ₐ[ℂ] VariableUltra.Algebra (fun _ : ℕ => B) ω where
  toFun := Quotient.map (boundedSeqToLp B) (by
    intro x y h
    exact (ultraRel_iff_norm B ω x y).mp h)
  map_zero' := rfl
  map_add' x y := by
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y => rfl
  map_one' := rfl
  map_mul' x y := by
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y => rfl
  map_star' x := by
    induction x using Quotient.inductionOn with | h x => rfl
  commutes' _ := rfl

@[simp] theorem normUltraToCStar_mk (x : BoundedSeq B) :
    normUltraToCStar B ω (normUltrapowerMk B ω x) =
      VariableUltra.mk (fun _ : ℕ => B) ω (boundedSeqToLp B x) := rfl

@[simp] theorem boundedSeqToLp_unitary (u : ℕ → unitary B) :
    boundedSeqToLp B (boundedUnitarySeq u) = VariableUltra.unitarySequence (fun _ : ℕ => B) u := by
  ext n
  rfl

end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_Obstruction
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
universe u v w
namespace NuclearUltrapower
/-- Exact main obligation, using an existential representative of the universal
C*-algebra. Proving this includes existence of C*(G), not just an implication
from an assumed universal model, and includes its separability.
The nonembedding assertion has no separability restriction on B. -/
def MainStatement : Prop :=
  ∃ (A : UnitalCStar.{u}) (ι : G →* unitary A),
    IsFullGroupAlgebra A ι ∧ TopologicalSpace.SeparableSpace A ∧
    ∀ (B : UnitalCStar.{u}), IsNuclear.{u, u} B →
      ∀ (ω : Ultrafilter ℕ), IsFree ω →
        ¬ ∃ φ : A →⋆ₐ[ℂ] NormUltrapower B ω, Function.Injective φ

end NuclearUltrapower
end
end

section

noncomputable section
namespace NuclearUltrapower

instance instCountableDyadic : Countable Dyadic :=
  (IsLocalization.mk'_surjective (Submonoid.powers (2 : ℤ)) (S := Dyadic)).countable

instance instCountableVector3 : Countable Vector3 := by
  unfold Vector3
  infer_instance

instance instCountableG : Countable G := by
  have : Countable (Multiplicative Vector3) := inferInstanceAs (Countable Vector3)
  have : Countable (Multiplicative ℤ) := inferInstanceAs (Countable ℤ)
  exact SemidirectProduct.equivProd.injective.countable

end NuclearUltrapower
end
end

end OAI
end


