-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecDomain
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecDomain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:17.462131+00:00
-- url     : https://prove2.me/theorems/f663aa45-b30e-4e45-a9bc-c8e5f91ac35b
-- title:
--   PGen Sec Domain
-- statement:
--   Definitions and structural lemmas for PGen Sec Domain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecDomain.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
namespace GenSecDomain
variable {k : Type} [Field k] {n : ℕ}
abbrev SecR (Q : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) : Type :=
  SecAlg (Q.map (MvPolynomial.map (C : k →+* MvPolynomial (Par e n) k)))
    (X : Par e n → MvPolynomial (Par e n) k)
abbrev xc (Q : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) (j : Fin n) : SecR Q e :=
  secCoord (Q.map (MvPolynomial.map (C : k →+* MvPolynomial (Par e n) k)))
    (X : Par e n → MvPolynomial (Par e n) k) j
section Point
variable (Q : Ideal (MvPolynomial (Fin n) k)) [Q.IsPrime] (e : ℕ)
abbrev Fn : Type := FractionRing (MvPolynomial (Fin n) k ⧸ Q)
abbrev Tgt : Type := MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) (Fn Q))
abbrev Om : Type := FractionRing (Tgt Q e)
def gsub (c : Fin n → Fn Q) : MvPolynomial (Fin e × Fin n) k →ₐ[k] MvPolynomial (Fin e × Fin n) (Fn Q) :=
  aeval (genSubst (genPt Q) c)
def ρ (c : Fin n → Fn Q) : MvPolynomial (Par e n) k →+* Tgt Q e :=
  (MvPolynomial.map (gsub Q e c).toRingHom).comp
    ((sumAlgEquiv k (Fin n) (Fin e × Fin n)).toRingHom.comp
      (renameEquiv k (Equiv.sumComm (Fin e × Fin n) (Fin n))).toRingHom)
def sT : Tgt Q e := ∑ l, X l * C (C (genPt Q l))
def ι : Fn Q →+* Om Q e := (algebraMap (Tgt Q e) (Om Q e)).comp ((C : _ →+* Tgt Q e).comp C)
def xs (l : Fin n) : Om Q e := ι Q e (genPt Q l) * (algebraMap (Tgt Q e) (Om Q e) (sT Q e))⁻¹
def Ψt (c : Fin n → Fn Q) : MvPolynomial (Fin n) (MvPolynomial (Par e n) k) →+* Om Q e :=
  eval₂Hom ((algebraMap (Tgt Q e) (Om Q e)).comp (ρ Q e c)) (xs Q e)
end Point
end GenSecDomain
end
end GroundTheory.Heights₂.Heights.Vertical


