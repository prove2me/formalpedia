-- Prove2me | Definitions.Def_GroundTheory_LocalFields_BrauerInductionClifford
-- name    : GroundTheory_LocalFields_BrauerInductionClifford
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:37:48.726259+00:00
-- url     : https://prove2.me/theorems/6d66ca42-efb6-4041-8fbb-912ad4296a8f
-- title:
--   Brauer Induction Clifford
-- statement:
--   Definitions and structural lemmas for Brauer Induction Clifford, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionClifford.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open Module Representation
section Basics
variable {G : Type*} [Group G]
def linRep (l : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun g := (l g : ℂ) • LinearMap.id
  map_one' := by
    ext
    simp
  map_mul' g h := by
    ext
    simp [mul_comm]
instance linRep_isIrreducible (l : G →* ℂˣ) : (linRep l).IsIrreducible where
  exists_pair_ne := ⟨⊥, ⊤, fun h ↦
    (bot_ne_top : (⊥ : Submodule ℂ ℂ) ≠ ⊤) (congrArg Subrepresentation.toSubmodule h)⟩
  eq_bot_or_eq_top U := by
    rcases Ideal.eq_bot_or_top U.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)
variable [Fintype G]
end Basics
section IndFunMore
variable {G H H' : Type*} [Group G] [Group H] [Group H'] [Fintype G] [Fintype H] [Fintype H']
end IndFunMore
section Conj
variable {G : Type*} [Group G] (A : Subgroup G) [hA : A.Normal]
def conjNormal (g : G) : A ≃* A where
  toFun a := ⟨g⁻¹ * a * g, by simpa using hA.conj_mem a a.2 g⁻¹⟩
  invFun a := ⟨g * a * g⁻¹, hA.conj_mem a a.2 g⟩
  left_inv a := by
    ext
    simp [mul_assoc]
  right_inv a := by
    ext
    simp [mul_assoc]
  map_mul' a b := by
    ext
    simp [mul_assoc]
@[simp]
theorem coe_conjNormal (g : G) (a : A) : (conjNormal A g a : G) = g⁻¹ * a * g := rfl
theorem conjNormal_mul (g h : G) (a : A) :
    conjNormal A (g * h) a = conjNormal A h (conjNormal A g a) := by
  ext
  simp [mul_assoc]
theorem conjNormal_one (a : A) : conjNormal A 1 a = a := by
  ext
  simp
def inertia (θ : A → ℂ) : Subgroup G where
  carrier := {g | ∀ a, θ (conjNormal A g a) = θ a}
  one_mem' := by
    intro a
    rw [conjNormal_one]
  mul_mem' {g h} hg hh := by
    intro a
    rw [conjNormal_mul, hh, hg]
  inv_mem' {g} hg := by
    intro a
    calc θ (conjNormal A g⁻¹ a) = θ (conjNormal A g (conjNormal A g⁻¹ a)) := (hg _).symm
      _ = θ a := by rw [← conjNormal_mul, inv_mul_cancel, conjNormal_one]
end Conj
section Clifford
variable {G : Type*} [Group G] [Fintype G] {A : Subgroup G} [A.Normal]
end Clifford
end GroundTheory.LocalField


