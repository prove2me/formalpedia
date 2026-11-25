-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableLatticePairOrbitsFiniteAndCardProd
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableLatticePairOrbitsFiniteAndCardProd
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T05:58:19.23102+00:00
-- url     : https://prove2.me/theorems/20cc2db9-1164-4bf8-ac67-653e6b1d103e
-- title:
--   Stable Lattice Pair Orbits Finite And Card Prod
-- statement:
--   Definitions and structural lemmas for Stable Lattice Pair Orbits Finite And Card Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/StableLatticePairOrbitsFiniteAndCardProd.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
import Theorems.Thm_GlobalTheory_UnitLemma_latPair_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnitLemma
open Polynomial
section PairOrbits
variable (O E A₁ A₂ : Type) [CommRing O] [Field E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂]
  [Algebra E A₁] [Algebra E A₂] (g₁ : A₁) (g₂ : A₂)
theorem latPair_orbitRel_iff (p q : LatPair O E g₁ g₂) :
    (MulAction.orbitRel (A₁ × A₂)ˣ (LatPair O E g₁ g₂)) p q ↔
      (MulAction.orbitRel A₁ˣ (stLat O E g₁)) p.1 q.1 ∧ (MulAction.orbitRel A₂ˣ (stLat O E g₂)) p.2 q.2 := by
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · rintro ⟨⟨t₁, h₁⟩, ⟨t₂, h₂⟩⟩
    refine ⟨MulEquiv.prodUnits.symm (t₁, t₂), ?_⟩
    rw [latPair_smul]
    have e₁ : Units.map (MonoidHom.fst A₁ A₂) (MulEquiv.prodUnits.symm (t₁, t₂)) = t₁ :=
      congrArg Prod.fst (MulEquiv.prodUnits.apply_symm_apply (t₁, t₂))
    have e₂ : Units.map (MonoidHom.snd A₁ A₂) (MulEquiv.prodUnits.symm (t₁, t₂)) = t₂ :=
      congrArg Prod.snd (MulEquiv.prodUnits.apply_symm_apply (t₁, t₂))
    rw [e₁, e₂, h₁, h₂]
    rfl
def latPairOrbitEquiv :
    MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂) ≃
      MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁) × MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂) where
  toFun := Quotient.lift (fun p : LatPair O E g₁ g₂ => ((Quotient.mk _ p.1 : MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁)),
      (Quotient.mk _ p.2 : MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂))))
    (fun p q h => by
      obtain ⟨h₁, h₂⟩ := (latPair_orbitRel_iff O E A₁ A₂ g₁ g₂ p q).1 h
      exact Prod.ext (Quotient.sound h₁) (Quotient.sound h₂))
  invFun x := Quotient.lift₂ (fun (a : stLat O E g₁) (b : stLat O E g₂) =>
      (Quotient.mk _ ((a, b) : LatPair O E g₁ g₂) : MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂)))
    (fun a₁ b₁ a₂ b₂ h₁ h₂ => Quotient.sound
      ((latPair_orbitRel_iff O E A₁ A₂ g₁ g₂ (a₁, b₁) (a₂, b₂)).2 ⟨h₁, h₂⟩)) x.1 x.2
  left_inv o := by
    induction o using Quotient.inductionOn with
    | h p => rfl
  right_inv x := by
    obtain ⟨x₁, x₂⟩ := x
    induction x₁ using Quotient.inductionOn with
    | h a => induction x₂ using Quotient.inductionOn with
      | h b => rfl
end PairOrbits
end GlobalTheory.UnitLemma


