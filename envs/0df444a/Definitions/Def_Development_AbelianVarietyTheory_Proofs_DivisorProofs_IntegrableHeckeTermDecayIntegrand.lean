-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableHeckeTermDecayIntegrand
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableHeckeTermDecayIntegrand
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:43.39588+00:00
-- url     : https://prove2.me/theorems/30e972c4-b0f8-4cbd-a0e9-07d7df844e63
-- title:
--   Integrable Hecke Term Decay Integrand
-- statement:
--   Definitions and structural lemmas for Integrable Hecke Term Decay Integrand, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableHeckeTermDecayIntegrand.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntZEqFourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay
noncomputable section
namespace GlobalTheory.HeckeTwo.TermDecay
end GlobalTheory.HeckeTwo.TermDecay


