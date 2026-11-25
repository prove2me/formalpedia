-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
-- name    : GroundTheory_GlobalFields_CyclotomicCharacters_Degree
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:28:28.014454+00:00
-- url     : https://prove2.me/theorems/855eda09-1308-4ed1-b2dd-9990afa22fd9
-- title:
--   Degree
-- statement:
--   Definitions and structural lemmas for Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Degree.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_PadicUnitsLog
import Theorems.Thm_GroundTheory_Global_Cyclotomic_eq_character
import Theorems.Thm_GroundTheory_Global_Cyclotomic_ext_toPadicInt
import Theorems.Thm_GroundTheory_Global_Cyclotomic_padicEquiv_apply
import Theorems.Thm_GroundTheory_Global_Cyclotomic_padicEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_Cyclotomic_val_unitsPadicEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Cyclotomic.padicEquiv_apply
attribute [local simp] GroundTheory.Global.Cyclotomic.padicEquiv_symm_apply
attribute [local simp] GroundTheory.Global.Cyclotomic.val_unitsPadicEquiv_apply


set_option autoImplicit false
open NumberField IntermediateField
open scoped GroundTheory.LocalField.Abstract ComplexConjugate
namespace GroundTheory.Global
namespace Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ
section UnitsDegree
noncomputable def unitsDegree : ℤ̂ˣ →* Multiplicative ℤ̂ where
  toFun u := Multiplicative.ofAdd
    (ofPadics fun q => Multiplicative.toAdd (padicUnitsLog q (unitsPadicEquiv u q)))
  map_one' := by
    rw [show (fun q : Nat.Primes => Multiplicative.toAdd (padicUnitsLog q (unitsPadicEquiv 1 q))) =
      0 from funext fun q => by simp, map_zero, ofAdd_zero]
  map_mul' u v := by
    rw [← ofAdd_add, ← map_add]
    congr 2
    funext q
    simp
theorem toPadicInt_unitsDegree (u : ℤ̂ˣ) (q : Nat.Primes) :
    toPadicInt q (Multiplicative.toAdd (unitsDegree u)) =
      Multiplicative.toAdd (padicUnitsLog q (unitsPadicEquiv u q)) :=
  congrFun (toPadics_ofPadics _) q
theorem unitsDegree_eq_one_iff (u : ℤ̂ˣ) :
    unitsDegree u = 1 ↔ ∀ q : Nat.Primes, unitsPadicEquiv u q ∈ CommGroup.torsion ℤ_[q]ˣ := by
  simp_rw [← ker_padicUnitsLog, MonoidHom.mem_ker]
  constructor
  · intro h q
    have := toPadicInt_unitsDegree u q
    rw [h, toAdd_one, map_zero] at this
    exact congrArg Multiplicative.ofAdd this.symm
  · intro h
    refine Multiplicative.toAdd.injective (ext_toPadicInt fun q => ?_)
    rw [toPadicInt_unitsDegree, h q, toAdd_one, toAdd_one, map_zero]
theorem unitsDegree_eq_one_of_pow_eq_one {u : ℤ̂ˣ} {k : ℕ} (hk : 0 < k) (h : u ^ k = 1) :
    unitsDegree u = 1 := by
  rw [unitsDegree_eq_one_iff]
  intro q
  rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  refine ⟨k, hk, ?_⟩
  rw [← Pi.pow_apply, ← map_pow, h, map_one, Pi.one_apply]
theorem unitsDegree_neg_one : unitsDegree (-1) = 1 :=
  unitsDegree_eq_one_of_pow_eq_one two_pos (by rw [neg_one_sq])
end UnitsDegree
section Degree
noncomputable def degree : Gal(ℚ̄/ℚ) →* Multiplicative ℤ̂ :=
  unitsDegree.comp character
theorem degree_apply (σ : Gal(ℚ̄/ℚ)) : degree σ = unitsDegree (character σ) :=
  rfl
noncomputable def degreeComponent (q : Nat.Primes) : Gal(ℚ̄/ℚ) →* Multiplicative ℤ_[q] :=
  (padicUnitsLog q).comp ((Units.map (toPadicInt q).toMonoidHom).comp character)
end Degree
section ComplexConjugation
def IsComplexConjugation (σ : Gal(ℚ̄/ℚ)) : Prop :=
  ∃ ι : ℚ̄ →+* ℂ, ∀ x, ι (σ x) = conj (ι x)
theorem exists_algEquiv_conj (ι : ℚ̄ →+* ℂ) :
    ∃ σ : Gal(ℚ̄/ℚ), ∀ x, ι (σ x) = conj (ι x) := by
  let _ : Algebra ℚ̄ ℂ := ι.toAlgebra
  have : IsScalarTower ℚ ℚ̄ ℂ := IsScalarTower.of_algebraMap_eq fun x =>
    (eq_ratCast _ x).trans (eq_ratCast (ι.comp (algebraMap ℚ ℚ̄)) x).symm
  let c : ℂ →ₐ[ℚ] ℂ := (starRingEnd ℂ).toRatAlgHom
  exact ⟨c.restrictNormal' ℚ̄, fun x => c.restrictNormal_commutes ℚ̄ x⟩
theorem character_of_isComplexConjugation {σ : Gal(ℚ̄/ℚ)} (h : IsComplexConjugation σ) :
    character σ = -1 := by
  obtain ⟨ι, hι⟩ := h
  refine Units.ext ?_
  rw [Units.val_neg, Units.val_one]
  refine (eq_character σ (-1) fun n t ht => ?_).symm
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_pow n.ne_zero] at ht
    exact zero_ne_one ht
  have hσ : σ t = t⁻¹ := by
    apply ι.injective
    rw [hι, map_inv₀]
    have hn : ‖ι t‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, ht, map_one]) n.ne_zero
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
    simp
  have hcast : (-1 : ZMod n) = (((n : ℕ) - 1 : ℕ) : ZMod n) := by
    rw [Nat.cast_sub (n.pos : 1 ≤ (n : ℕ)), ZMod.natCast_self, Nat.cast_one, zero_sub]
  rw [hσ, map_neg, map_one, hcast, pow_val_natCast ht]
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [← pow_succ, Nat.sub_add_cancel (n.pos : 1 ≤ (n : ℕ)), ht]
theorem degree_of_isComplexConjugation {σ : Gal(ℚ̄/ℚ)} (h : IsComplexConjugation σ) :
    degree σ = 1 := by
  rw [degree_apply, character_of_isComplexConjugation h, unitsDegree_neg_one]
end ComplexConjugation
section FixedField
noncomputable def zhatField : IntermediateField ℚ ℚ̄ :=
  fixedField degree.ker
theorem isReal_zhatField (φ : zhatField →+* ℂ) : ComplexEmbedding.IsReal φ := by
  let _ : Algebra zhatField ℂ := φ.toAlgebra
  have : Algebra.IsAlgebraic zhatField ℚ̄ := Algebra.IsAlgebraic.tower_top (K := ℚ) zhatField
  let ι : ℚ̄ →ₐ[zhatField] ℂ := IsAlgClosed.lift
  obtain ⟨σ, hσ⟩ := exists_algEquiv_conj ι.toRingHom
  have hdeg : σ ∈ degree.ker := degree_of_isComplexConjugation ⟨_, hσ⟩
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  have hx : σ (x : ℚ̄) = x := (mem_fixedField_iff _ _).1 x.2 σ hdeg
  have h1 : ι (x : ℚ̄) = φ x := ι.commutes x
  have h2 := hσ (x : ℚ̄)
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hx, h1] at h2
  exact h2.symm
instance isTotallyReal_zhatField : IsTotallyReal zhatField :=
  ⟨fun _ => InfinitePlace.isReal_iff.2 (isReal_zhatField _)⟩
end FixedField
end Cyclotomic
end GroundTheory.Global


