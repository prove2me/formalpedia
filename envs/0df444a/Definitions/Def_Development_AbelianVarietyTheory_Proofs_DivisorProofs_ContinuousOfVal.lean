-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:32.638527+00:00
-- url     : https://prove2.me/theorems/f27f865e-3dff-4d49-8c7d-0b9356f547eb
-- title:
--   Continuous Of Val
-- statement:
--   Definitions and structural lemmas for Continuous Of Val, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped WithZero
namespace GlobalTheory.CMVal.ValEx
section Local
variable {K : Type} [Field K] (v : Valuation K ℤᵐ⁰)
def cong (n : ℕ) : Subgroup Kˣ where
  carrier := {x | v (x : K) = 1 ∧ v ((x : K) - 1) ≤ WithZero.exp (-(n : ℤ))}
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨by rw [Units.val_mul, map_mul, ha.1, hb.1, one_mul], by
    have : ((a * b : Kˣ) : K) - 1 = a * ((b : K) - 1) + ((a : K) - 1) := by rw [Units.val_mul]; ring
    rw [this]
    exact v.map_add_le (by rw [map_mul, ha.1, one_mul]; exact hb.2) ha.2⟩
  inv_mem' := fun {a} ha => ⟨by rw [Units.val_inv_eq_inv_val, map_inv₀, ha.1, inv_one], by
    have : ((a⁻¹ : Kˣ) : K) - 1 = -((a : K)⁻¹ * ((a : K) - 1)) := by
      rw [Units.val_inv_eq_inv_val]; field_simp; ring
    rw [this, v.map_neg, map_mul, map_inv₀, ha.1, inv_one, one_mul]; exact ha.2⟩
end Local
variable {E : Type} [Field E] [NumberField E]
def toLoc (w : HeightOneSpectrum (𝓞 E)) : Eˣ →* (w.adicCompletion E)ˣ :=
  Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom
section CM
variable [IsCMField E]
local notation "cc" => IsCMField.complexConj E
def bar (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) :=
  w.comap (RingOfIntegers.mapRingEquiv (cc).toRingEquiv : 𝓞 E →+* 𝓞 E) (RingOfIntegers.mapRingEquiv (cc).toRingEquiv).surjective
end CM
def locU (P : HeightOneSpectrum (𝓞 E)) : (Af E)ˣ →* (P.adicCompletion E)ˣ :=
  Units.map { toFun := fun x : Af E => x P, map_one' := rfl, map_mul' := fun _ _ => rfl }
def finOf : Ideles E →* (Af E)ˣ := Units.map (MonoidHom.snd (InfiniteAdeleRing E) (Af E))
def infOf : Ideles E →* (InfiniteAdeleRing E)ˣ := Units.map (MonoidHom.fst (InfiniteAdeleRing E) (Af E))
def unitI : Subgroup (Ideles E) :=
  ⨅ P : HeightOneSpectrum (𝓞 E), (cong (Valued.v : Valuation (P.adicCompletion E) ℤᵐ⁰) 0).comap ((locU P).comp finOf)
end GlobalTheory.CMVal.ValEx


