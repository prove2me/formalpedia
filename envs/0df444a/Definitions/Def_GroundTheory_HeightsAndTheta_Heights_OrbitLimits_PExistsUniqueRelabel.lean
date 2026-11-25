-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T03:48:04.914572+00:00
-- url     : https://prove2.me/theorems/adb08382-251f-4439-9498-8c65f5077f41
-- title:
--   PExists Unique Relabel
-- statement:
--   Definitions and structural lemmas for PExists Unique Relabel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ExistsUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
namespace ExistsUniqueRelabel
section RingEquiv
variable {R R' : Type*} [CommRing R] [CommRing R'] (φ : R ≃+* R')
end RingEquiv
section MRing
variable {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
variable (e : K ≃ K') (σ : (Σ k, ι k) ≃ (Σ k', ι' k')) (hσ : ∀ p, (σ p).1 = e p.1)
abbrev ren : MRingOver F ι ≃+* MRingOver F ι' := (renameEquiv F σ).toRingEquiv
include hσ
omit hσ in

def idealEquiv : Ideal (MRingOver F ι) ≃ Ideal (MRingOver F ι') where
  toFun W := W.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')
  invFun W := W.map ((ren (F := F) σ).symm : MRingOver F ι' →+* MRingOver F ι)
  left_inv W := Ideal.map_of_equiv (I := W) (ren (F := F) σ)
  right_inv W := by
    have := Ideal.map_of_equiv (I := W) (ren (F := F) σ).symm
    rwa [RingEquiv.symm_symm] at this
omit hσ in

def fiberElt (q : Σ k', ι' k') (k' : K') (h : q.1 = k') : ι' k' := h ▸ q.2
def chartMap (i : ∀ k, ι k) (k' : K') : ι' k' :=
  fiberElt (σ ⟨e.symm k', i (e.symm k')⟩) k' (by rw [hσ, Equiv.apply_symm_apply])
omit hσ in

def pullFamily (I' : IFamily F ι') : IFamily F ι :=
  fun V n L => I' (V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')) n (fun j => L j ∘ e.symm)
end MRing
end ExistsUniqueRelabel
universe u v w v' w'
end GroundTheory.Heights₂.Heights.Targets


