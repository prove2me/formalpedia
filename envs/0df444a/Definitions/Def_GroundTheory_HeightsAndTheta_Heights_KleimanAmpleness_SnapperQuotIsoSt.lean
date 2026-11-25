-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotIsoSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotIsoSt
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T06:27:35.598331+00:00
-- url     : https://prove2.me/theorems/7bc59d5f-fbc2-477f-b817-558507fc0c9f
-- title:
--   Snapper Quot Iso St
-- statement:
--   Definitions and structural lemmas for Snapper Quot Iso St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/SnapperQuotIsoSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperCutObj
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
open MvPolynomial
noncomputable section
universe u v w v'
section Defs
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
structure QuotIso {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    {E' : Type v'} [AddCommGroup E'] [Module Ω E'] [Module S E'] [IsScalarTower S Ω E']
    (F₁ F₂ : SubSystem S x E) (G₁ G₂ : SubSystem S x E') where

  equiv : ∀ I : Chart x,
    (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) ≃ₗ[S] (G₁.sub I ⧸ SubSystem.quotSub G₁ G₂ I)

  comm : ∀ (I J : Chart x) (h : I.1 ⊆ J.1) (y : F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I),
    equiv J (SubSystem.quotRes F₁ F₂ I J h y) = SubSystem.quotRes G₁ G₂ I J h (equiv I y)
def QuotIso.refl {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F₁ F₂ : SubSystem S x E) : QuotIso F₁ F₂ F₁ F₂ where
  equiv _ := LinearEquiv.refl S _
  comm _ _ _ _ := rfl
end Defs
def SnapperQuotIso.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (E' : Type v') [AddCommGroup E'] [Module Ω E'] [Module k E'] [IsScalarTower k Ω E']
    (F₁ F₂ : SubSystem k x E) (G₁ G₂ : SubSystem k x E'), QuotIso F₁ F₂ G₁ G₂ →
    eulerCharQuot k F₁ F₂ = eulerCharQuot k G₁ G₂
def snapperQuotIso_hyps (k : Type u) [Field k] :
    QuotIso (twistSys k (genericPt k 1) 0)
      ((twistSys k (genericPt k 1) 0).twist (idealSys (genericPt k 1) (primeOf (S := k) (genericPt k 1))))
      (twistSys k (genericPt k 1) 0)
      ((twistSys k (genericPt k 1) 0).twist (idealSys (genericPt k 1) (primeOf (S := k) (genericPt k 1)))) :=
  QuotIso.refl _ _
end
end GroundTheory.Heights₂.Heights.Kleiman


