-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseObjects
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseObjects
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:58.63351+00:00
-- url     : https://prove2.me/theorems/eab5c332-85e2-489d-ad66-1bb7066a4d40
-- title:
--   St Transverse Objects
-- statement:
--   Definitions and structural lemmas for St Transverse Objects, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StTransverseObjects.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial Matrix ComplexSets IsLocalRing
noncomputable section
class IsCohenMacaulayLocalRing (B : Type*) [CommRing B] : Prop extends IsLocalRing B, IsNoetherianRing B where
  exists_isWeaklyRegular : ∃ rs : List B, (∀ r ∈ rs, r ∈ maximalIdeal B) ∧
    RingTheory.Sequence.IsWeaklyRegular B rs ∧ ringKrullDim B = (rs.length : WithBot ℕ∞)
variable {n d : ℕ}
instance isMaximal_ker_eval_point (q : Fin n → ℂ) :
    (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun z => ⟨C z, eval_C z⟩
abbrev localRingAt (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : Type :=
  Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) ⧸
    I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))
def IsCohenMacaulayAt (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : Prop :=
  IsCohenMacaulayLocalRing (localRingAt I q)
def IsTransverseSliceAt (W : Ideal (MvPolynomial (Fin n) ℂ)) (L : Matrix (Fin d) (Fin n) ℂ) (q : Fin n → ℂ) :
    Prop :=
  ∀ g : MvPolynomial (Fin n) ℂ, eval q g = 0 → ∃ s : MvPolynomial (Fin n) ℂ, eval q s ≠ 0 ∧ s * g ∈ sliceIdeal W L q
end
end GroundTheory.Heights₂.Heights


