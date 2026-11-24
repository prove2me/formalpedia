-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SwapCApply
-- name    : Development_AutomorphicSpectrum_Proofs_MembershipProofs_SwapCApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:45.919209+00:00
-- url     : https://prove2.me/theorems/da9ae0c9-00cb-4e39-911c-b79d3050ba30
-- title:
--   Swap CApply
-- statement:
--   Definitions and structural lemmas for Swap CApply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/SwapCApply.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_OrderOKOneInert
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IsLatticeOfCompactOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.CompanionTheory.IdxAd
section Single
variable {F : Type} [Field F] [NumberField F]
open Classical in

def sgl (v : HeightOneSpectrum (𝓞 F)) : v.adicCompletion F →+ FiniteAdeleRing (𝓞 F) F where
  toFun x := RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v x
  map_zero' := RestrictedProduct.single_zero _ v
  map_add' := RestrictedProduct.single_add _ v
end Single
def swapC (k : Type) [CommRing k] : (k × k) →ₐ[k] k × k := (GlobalTheory.CompanionTheory.SplitIdx.swapAlg k).toAlgHom
end GlobalTheory.CompanionTheory.IdxAd


