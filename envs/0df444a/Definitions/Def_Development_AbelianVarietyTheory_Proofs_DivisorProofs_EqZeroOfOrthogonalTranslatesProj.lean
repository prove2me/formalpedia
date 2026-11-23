-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfOrthogonalTranslatesProj
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfOrthogonalTranslatesProj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:03:13.557552+00:00
-- url     : https://prove2.me/theorems/7d36b6a7-66c2-4316-9d73-d3bb95825af3
-- title:
--   Eq Zero Of Orthogonal Translates Proj
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Orthogonal Translates Proj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqZeroOfOrthogonalTranslatesProj.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableMonomialMulConjComplexGaussian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
open scoped InnerProductSpace Real
namespace GlobalTheory.RealWeil
section Abstract
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → H →L[ℂ] H}
end Abstract
noncomputable def signUnit (p q : ℕ) : Fin p ⊕ Fin q → Circle :=
  Sum.elim (fun _ => ⟨I, by simp [Submonoid.unitSphere]⟩) (fun _ => ⟨-I, by simp [Submonoid.unitSphere]⟩)
noncomputable def signJ (p q : ℕ) : EuclideanSpace ℂ (Fin p ⊕ Fin q) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin p ⊕ Fin q) :=
  LinearIsometryEquiv.piLpCongrRight 2 fun a => rotation (signUnit p q a)
end GlobalTheory.RealWeil


