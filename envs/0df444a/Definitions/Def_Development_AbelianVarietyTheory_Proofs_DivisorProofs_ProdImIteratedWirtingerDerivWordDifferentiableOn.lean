-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdImIteratedWirtingerDerivWordDifferentiableOn
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdImIteratedWirtingerDerivWordDifferentiableOn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:52:21.547585+00:00
-- url     : https://prove2.me/theorems/53f0ea68-6193-4bcc-910f-8b28da07ed25
-- title:
--   Prod Im Iterated Wirtinger Deriv Word Differentiable On
-- statement:
--   Definitions and structural lemmas for Prod Im Iterated Wirtinger Deriv Word Differentiable On, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdImIteratedWirtingerDerivWordDifferentiableOn.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
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
namespace GlobalTheory.HeckeTwo.ProdImWirt
variable {Φ : Type} [Fintype Φ]
noncomputable def mono (c : ℂ → ℂ) (a : ℂ → Φ → ℂ) (σ : ℂ) (z : Φ → ℂ) : ℂ :=
  c σ * Complex.exp (∑ τ, a σ τ * ((Real.log (z τ).im : ℝ) : ℂ))
end GlobalTheory.HeckeTwo.ProdImWirt


