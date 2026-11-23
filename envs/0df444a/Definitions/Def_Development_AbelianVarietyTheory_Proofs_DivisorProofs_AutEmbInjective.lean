-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AutEmbInjective
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_AutEmbInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:19.694963+00:00
-- url     : https://prove2.me/theorems/fb21e731-1d42-4d5f-b203-37413439808c
-- title:
--   Aut Emb Injective
-- statement:
--   Definitions and structural lemmas for Aut Emb Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AutEmbInjective.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
namespace GlobalTheory.HilbFam
noncomputable def autEmb {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (g : ℂ ≃+* ℂ) (i : Emb F) : Emb F :=
  (IsTotallyReal.complexEmbedding_isReal (g.toRingHom.comp ((algebraMap ℝ ℂ).comp i))).embedding
end GlobalTheory.HilbFam


