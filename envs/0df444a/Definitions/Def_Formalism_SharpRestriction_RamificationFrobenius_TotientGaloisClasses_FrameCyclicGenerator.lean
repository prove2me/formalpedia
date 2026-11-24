-- Prove2me | Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator
-- name    : Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T15:33:01.755284+00:00
-- url     : https://prove2.me/theorems/bf3090fe-813c-4df9-b4a6-8a5980e374a5
-- title:
--   Frame Cyclic Generator
-- statement:
--   Definitions and structural lemmas for Frame Cyclic Generator, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameCyclicGenerator.lean

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HC
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
namespace Frame
section Of
variable {A' : Type} [AddCommGroup A'] (e : ℕ) {n : ℕ} (ε : Idx n ≃ A') (h' : A' →+ Additive (HGrp e))
  (hs : Function.Surjective h') (a' : A') (hk : ∀ k : ℤ, h' (k • a') = 0 → k • a' = 0)
def ofEquiv : Frame :=
  letI : AddCommGroup (Idx n) := ε.addCommGroup
  { e := e
    ord := n
    grp := ε.addCommGroup
    h0 := h'.comp ε.addEquiv.toAddMonoidHom
    projection_surjective_field := hs.comp ε.surjective
    gen0 := ε.symm a'
    zsmul_generator_eq_zero_of_projection := fun k hk0 => by
      have h1 : ε.addEquiv (k • ε.symm a') = k • a' := by
        rw [map_zsmul]
        exact congrArg (fun x => k • x) (ε.apply_symm_apply a')
      apply ε.addEquiv.injective
      rw [h1, map_zero]
      apply hk
      rw [← h1]
      exact hk0 }
def ofEquivIso : (ofEquiv e ε h' hs a' hk).A ≃+ A' :=
  letI : AddCommGroup (Idx n) := ε.addCommGroup
  ε.addEquiv
variable [Fintype A']
def ofGroup : Frame := ofEquiv e (n := Fintype.card A') (Fintype.equivFin A').symm h' hs a' hk
def ofGroupIso : (ofGroup e h' hs a' hk).A ≃+ A' :=
  ofEquivIso e (n := Fintype.card A') (Fintype.equivFin A').symm h' hs a' hk
end Of
end Frame
def cycIso (e : ℕ) : Multiplicative (ZMod (2 ^ e)) ≃* HGrp e :=
  Classical.choose (hostGroup e).2.2.2.2.2.2.2.2
def cycHom (e : ℕ) : ZMod (2 ^ e) →+ Additive (HGrp e) :=
  AddMonoidHom.mk' (fun i => Additive.ofMul (cycIso e (Multiplicative.ofAdd i))) (fun i j => by
    rw [ofAdd_add, map_mul, ofMul_mul])
theorem cycHom_bijective (e : ℕ) : Function.Bijective (cycHom e) := by
  show Function.Bijective (fun i => Additive.ofMul (cycIso e (Multiplicative.ofAdd i)))
  exact Additive.ofMul.bijective.comp ((cycIso e).bijective.comp Multiplicative.ofAdd.bijective)
def idxZMod (n : ℕ) [NeZero n] : Idx n ≃ ZMod n := (ZMod.finEquiv n).toEquiv
theorem cycHom_ker (e : ℕ) (a' : ZMod (2 ^ e)) (k : ℤ) (hk : cycHom e (k • a') = 0) : k • a' = 0 :=
  (cycHom_bijective e).1 (by rw [hk, map_zero])
def frameCyc (e : ℕ) (a' : ZMod (2 ^ e)) : Frame :=
  Frame.ofEquiv e (idxZMod (2 ^ e)) (cycHom e) (cycHom_bijective e).2 a' (cycHom_ker e a')
def frameCycIso (e : ℕ) (a' : ZMod (2 ^ e)) : (frameCyc e a').A ≃+ ZMod (2 ^ e) :=
  Frame.ofEquivIso e (idxZMod (2 ^ e)) (cycHom e) (cycHom_bijective e).2 a' (cycHom_ker e a')
section Cyc
variable (e : ℕ) (a' : ZMod (2 ^ e))
end Cyc
def cyclicFrame (e : ℕ) : Frame := frameCyc e 1
def cyclicFramePow (e j : ℕ) : Frame := frameCyc e (2 ^ j)
end Formalism.HC
end


