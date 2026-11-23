-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntZEqFourier
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntZEqFourier
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:52:02.968849+00:00
-- url     : https://prove2.me/theorems/a9aa4bb6-34c3-4553-8f02-c8b66fe25cc8
-- title:
--   Int ZEq Fourier
-- statement:
--   Definitions and structural lemmas for Int ZEq Fourier, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntZEqFourier.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
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
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
namespace GlobalTheory.HeckeTwo.TermDecay
def qZ (σ : ℂ) (a : ℤ) (b m : ℕ) (y t : ℝ) : ℂ :=
  ((t : ℂ) + (y : ℂ) * I) ^ (-a) * (((t ^ 2 + y ^ 2 : ℝ) : ℂ)) ^ (-σ - (b : ℂ)) * (y : ℂ) ^ m
def intZ (σ : ℂ) (ν : ℝ) (a : ℤ) (b m : ℕ) (y : ℝ) : ℂ :=
  ∫ t : ℝ, qZ σ a b m y t * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))
end GlobalTheory.HeckeTwo.TermDecay


