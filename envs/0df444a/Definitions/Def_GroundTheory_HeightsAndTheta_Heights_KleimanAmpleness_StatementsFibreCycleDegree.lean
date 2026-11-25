-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreCycleDegree
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreCycleDegree
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:37:26.737703+00:00
-- url     : https://prove2.me/theorems/78cf8b95-63bd-56b3-9551-de97c56e4c5b
-- title:
--   Statements Fibre Cycle Degree
-- statement:
--   Definitions and structural lemmas for Statements Fibre Cycle Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StatementsFibreCycleDegree.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsNefGeneric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open Classical in

def FibreCycleDegree.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsDedekindDomain S] (F : Type u) [Field F] [Algebra S F]
    [IsFractionRing S F] (Ω : Type w) [Field Ω] [Algebra S Ω] [Algebra F Ω] [IsScalarTower S F Ω]
    (N : ℕ) (x : Fin (N + 1) → Ω) (M : LineBundle S x) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ qq : Ideal (Poly S N), qq.IsPrime → (∀ s : S, (C s : Poly S N) ∈ qq → s = 0) →
    IsSubvar x (qq.map (MvPolynomial.map (algebraMap S F))) 1 →
    ∀ᶠ c : ℕ in atTop,
      interSum (qq ⊔ 𝔪.map (C : S →+* Poly S N)) ![M.toSubSystem] c =
        ∑ᶠ G : Ideal (Poly S N),
          if h : G ∈ (qq ⊔ 𝔪.map (C : S →+* Poly S N)).minimalPrimes ∧ IsSubvar x G 1 then
            haveI : G.IsPrime := h.1.1.1
            ((cutMult (qq ⊔ 𝔪.map (C : S →+* Poly S N)) G).toNat : ℤ) * interNum G ![M.toSubSystem]
          else 0
end
end GroundTheory.Heights₂.Heights.Kleiman


