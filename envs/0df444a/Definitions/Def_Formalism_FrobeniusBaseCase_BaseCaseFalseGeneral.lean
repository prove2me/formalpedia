-- Prove2me | Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
-- name    : Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T02:55:13.64125+00:00
-- url     : https://prove2.me/theorems/dfdffe6a-9742-59a8-8ddc-d3bba040aa53
-- title:
--   Base Case False General
-- statement:
--   Definitions and structural lemmas for Base Case False General, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/BaseCaseFalseGeneral.lean

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseFalseGeneralHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_FixAll
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_LogIffFix_statement
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_QSigmaSmall_statement
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_base_case_false_general_holds
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_base_case_k_one_holds
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_chainII_holds
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_chainI_holds
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_chain_ii_of_log
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_coeff_minus_one_holds
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_contracts
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_hasUniqueFixedPoint
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_log_unique_bis
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_opIsLimit
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_psi_in_W_holds
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_second_way_holds
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_start_eq_z
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_start_in_W_holds
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_unit_entry_all
import Theorems.Thm_Formalism_BaseCaseIdentities_frobeniusSubstSpec
import Theorems.Thm_Formalism_BaseCaseIdentities_mul_rule_two_holds
import Theorems.Thm_Formalism_BaseCaseIdentities_pow_rule_two_holds
import Theorems.Thm_Formalism_BaseCaseIdentities_weighted_mul_rule
import Theorems.Thm_Formalism_BaseCaseIdentities_weighted_pow_rule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.BaseCaseIdentities.Final
open Formalism.BaseCaseIdentities
alias frobenius_spectrum := frobeniusSubstSpec
alias psi_is_limit := Data.opIsLimit
alias chainI := Data.chainI_holds
alias contractionAlt := Data.contracts
alias fixed_point_alt := Data.hasUniqueFixedPoint
alias start_in_W := Data.start_in_W_holds
alias psi_in_W := Data.psi_in_W_holds
alias chainII := Data.chainII_holds
alias second_way := Data.second_way_holds
alias base_case_k_one := Data.base_case_k_one_holds
alias mul_rule := weighted_mul_rule
alias pow_rule := weighted_pow_rule
alias mul_rule_two := mul_rule_two_holds
alias pow_rule_two := pow_rule_two_holds
alias coeff_minus_one := Data.coeff_minus_one_holds
alias base_case_false_general := Data.base_case_false_general_holds
alias q_sigma_small := Data.QSigmaSmall_statement
alias unit_entries_alt := Data.unit_entry_all
alias start_eq_zero := Data.start_eq_z
alias log_iff_fixed_point := Data.LogIffFix_statement
alias log_unique_alt := Data.log_unique_bis
alias chainII_log := Data.chain_ii_of_log
end Formalism.BaseCaseIdentities.Final


