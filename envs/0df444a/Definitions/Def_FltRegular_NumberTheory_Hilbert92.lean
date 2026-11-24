-- Prove2me | Definitions.Def_FltRegular_NumberTheory_Hilbert92
-- name    : FltRegular_NumberTheory_Hilbert92
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:33:26.77618+00:00
-- url     : https://prove2.me/theorems/7226a21c-f7f9-4d10-8a91-3f98a48b1f65
-- title:
--   Hilbert92
-- statement:
--   Definitions and structural lemmas for Hilbert92, from leanprover-community/flt-regular contributors (see pinned LICENSE and source headers)'s pinned Fermat's Last Theorem for regular primes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean

module
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.Henselian
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
set_option autoImplicit false
@[expose] public section
@[expose] public section
open scoped NumberField nonZeroDivisors
open FiniteDimensional NumberField
variable {s r : ℕ} (p : ℕ) {K : Type*} [Field K]
variable {k : Type*} [Field k] (hp : Nat.Prime p)
open Module Finset
open CyclotomicIntegers (zeta)
section thm91
variable (G : Type*) [AddCommGroup G]
local notation3 "A" => CyclotomicIntegers p
abbrev systemOfUnits.IsMaximal {p : ℕ} {G : Type*} [AddCommGroup G]
    [Module (CyclotomicIntegers p) G] (sys : systemOfUnits (G := G) p s) :=
  (Submodule.span (CyclotomicIntegers p) (Set.range sys.units)).toAddSubgroup.FiniteIndex
@[nolint unusedArguments]
noncomputable def systemOfUnits.index [Module A G] (sys : systemOfUnits p G s) [sys.IsMaximal] :=
  (Submodule.span A (Set.range sys.units)).toAddSubgroup.index
def systemOfUnits.IsFundamental [Module A G] (h : systemOfUnits p G s) :=
  ∃ _ : h.IsMaximal, ∀ (S : systemOfUnits p G s) (_ : S.IsMaximal), h.index ≤ S.index
namespace systemOfUnits.IsFundamental
variable {H : Type*} [CommGroup H] [Fintype H] (hCard : Fintype.card H = p)
  (σ : H) (hσ : Subgroup.zpowers σ = ⊤) (s : ℕ) [DistribMulAction H G]
  (hf : finrank ℤ G = s * (p - 1))
include hp hf
variable [Module.Finite ℤ G]
end systemOfUnits.IsFundamental
section application
variable
    [Algebra k K] (hKL : finrank k K = p) (σ : K ≃ₐ[k] K)
    (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
def RelativeUnits (k K : Type*) [Field k] [Field K] [Algebra k K] :=
  (𝓞 K)ˣ ⧸ MonoidHom.range
    (Units.map (algebraMap (𝓞 k) (𝓞 K) : (𝓞 k) →* (𝓞 K)))
instance : CommGroup (RelativeUnits k K) := by
  delta RelativeUnits
  infer_instance
section
variable [NumberField K] [NumberField k]
noncomputable def relativeUnitsMap (σ : K →ₐ[k] K) : RelativeUnits k K →* RelativeUnits k K := by
  apply QuotientGroup.lift _
    ((QuotientGroup.mk' _).comp (Units.map (galRestrictHom (𝓞 k) k K (𝓞 K) σ)))
  rintro _ ⟨i, rfl⟩
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, QuotientGroup.coe_mk', Function.comp_apply,
    QuotientGroup.eq_one_iff, MonoidHom.mem_range, Units.ext_iff, Units.coe_map]
  exact ⟨i, by change algebraMap (𝓞 k) (𝓞 K) i = (galRestrictHom (𝓞 k) k K (𝓞 K) σ) (algebraMap (𝓞 k) (𝓞 K) i); exact (AlgHom.commutes _ _).symm⟩
lemma relativeUnitsMap_mk (σ : K →ₐ[k] K) (x : (𝓞 K)ˣ) :
    relativeUnitsMap σ (QuotientGroup.mk x) =
      QuotientGroup.mk (Units.map (galRestrictHom (𝓞 k) k K (𝓞 K) σ) x) := rfl
@[simp]
theorem relativeUnitsMap_one (x : RelativeUnits k K) :
    relativeUnitsMap (1 : K →ₐ[k] K) x = x := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  simp only [relativeUnitsMap_mk, map_one]
  rfl
theorem relativeUnitsMap_mul_apply {f g} (x : RelativeUnits k K) :
    (relativeUnitsMap (f * g)) x = (relativeUnitsMap f (relativeUnitsMap g x)) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  simp_rw [relativeUnitsMap_mk, map_mul]
  rfl
noncomputable def relativeUnitsMapHom : (K →ₐ[k] K) →* (Monoid.End (RelativeUnits k K)) where
  toFun := relativeUnitsMap
  map_one' := by
    ext x
    exact relativeUnitsMap_one x
  map_mul' f g := by
    ext x
    exact relativeUnitsMap_mul_apply x
@[simp]
theorem relativeUnitsMapHom_apply (σ : K →ₐ[k] K) :
    relativeUnitsMapHom σ = relativeUnitsMap σ := rfl
set_option backward.isDefEq.respectTransparency false in
include σ hp hKL hσ in
open Polynomial in
lemma isTors' [IsGalois k K] : Module.IsTorsionBySet ℤ[X]
    (Module.AEval' (addMonoidEndRingEquivInt _
      (monoidEndToAdditive _ <| relativeUnitsMapHom <|
        ((AlgEquiv.algHomUnitsEquiv _ _).symm σ).val)))
    (Ideal.span {cyclotomic p ℤ}) := by
  classical
  have := Fact.mk hp
  rw [← Module.isTorsionBySet_iff_is_torsion_by_span, Module.isTorsionBySet_singleton_iff]
  intro x
  obtain ⟨x, rfl⟩ := (Module.AEval.of _ _ _).surjective x
  obtain ⟨x, rfl⟩ := Additive.ofMul.surjective x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  rw [← Module.AEval.of_aeval_smul]
  simp_rw [Module.End.smul_def, Polynomial.cyclotomic_prime ℤ p, EmbeddingLike.map_eq_zero_iff,
    map_sum, map_pow, aeval_X, LinearMap.coe_sum, Finset.sum_apply]
  conv =>
    enter [1, 2, c]
    rw [← map_pow, ← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow,
      AlgEquiv.val_algHomUnitsEquiv_symm_apply, relativeUnitsMapHom_apply,
      addMonoidEndRingEquivInt_apply, AddHom.toFun_eq_coe,
      LinearMap.coe_toAddHom, LinearEquiv.coe_coe, addMonoidHomLequivInt_apply,
      AddMonoidHom.coe_toIntLinearMap, monoidEndToAdditive_apply_apply, toMul_ofMul,
      relativeUnitsMap_mk]
  rw [← ofMul_prod, ← QuotientGroup.mk_prod, ofMul_eq_zero, QuotientGroup.eq_one_iff]
  use Units.map (RingOfIntegers.norm k) x
  ext
  change ((algebraMap (𝓞 k) (𝓞 K) (RingOfIntegers.norm k (x : 𝓞 K)) : 𝓞 K) : K) = _
  simp only [RingOfIntegers.coe_algebraMap_norm, Units.coe_prod, Algebra.norm_eq_prod_automorphisms]
  rw [← hKL, ← IsGalois.card_aut_eq_finrank,
    ← orderOf_eq_card_of_forall_mem_zpowers hσ, ← Fin.prod_univ_eq_prod_range,
    ← (finEquivZPowers <| isOfFinOrder_of_finite _).symm.prod_comp]
  simp only [RingOfIntegers.coe_eq_algebraMap, pow_finEquivZPowers_symm_apply, map_prod,
    algebraMap_galRestrictHom_apply, AlgEquiv.coe_toAlgHom]
  refine (Finset.prod_subtype Finset.univ (p := fun a : Gal(K/k) => a ∈ Subgroup.zpowers σ)
    (fun a => by simp [hσ]) (fun a => a ((algebraMap (𝓞 K) K) (x : 𝓞 K)))).trans
    (Finset.prod_congr rfl fun a _ => ?_)
  change _ = (algebraMap (𝓞 K) K) ((galRestrictHom (𝓞 k) k K (𝓞 K) a.1) (x : 𝓞 K))
  exact (algebraMap_galRestrictHom_apply (𝓞 k) k K (𝓞 K) a.1 (x : 𝓞 K)).symm
@[nolint unusedArguments]
def relativeUnitsWithGenerator (_hp : Nat.Prime p)
  (_hKL : finrank k K = p) (σ : K ≃ₐ[k] K) (_hσ : ∀ x, x ∈ Subgroup.zpowers σ) :=
  RelativeUnits k K
instance : CommGroup (relativeUnitsWithGenerator p hp hKL σ hσ) := by
  delta relativeUnitsWithGenerator
  infer_instance
end
local notation "G" =>
  Additive (relativeUnitsWithGenerator p hp hKL σ hσ) ⧸
    AddCommGroup.torsion (Additive (relativeUnitsWithGenerator p hp hKL σ hσ))
def unitToU (u : (𝓞 K)ˣ) : G := QuotientAddGroup.mk (Additive.ofMul <| QuotientGroup.mk u)
local notation "mkG" => unitToU p hp hKL σ hσ
variable [NumberField k]
variable [NumberField K]
variable [IsGalois k K]
include hKL in
noncomputable instance relativeUnitsModule : Module A G := by
  letI : Module A (Additive (relativeUnitsWithGenerator p hp hKL σ hσ)) :=
    (isTors' p hp hKL σ hσ).module
  infer_instance
local instance _p2m_local_instance_fee6646a52_507 : Module.Finite ℤ (Additive <| RelativeUnits k K) :=
  inferInstanceAs
    (Module.Finite ℤ (Additive (𝓞 K)ˣ ⧸ AddSubgroup.toIntSubmodule (Subgroup.toAddSubgroup
    (MonoidHom.range <| Units.map (algebraMap (𝓞 k) (𝓞 K) : (𝓞 k) →* (𝓞 K))))))
local instance _p2m_local_instance_fee6646a52_512 : Module.Finite ℤ (Additive <| relativeUnitsWithGenerator p hp hKL σ hσ) :=
  inferInstanceAs (Module.Finite ℤ (Additive (RelativeUnits k K)))
local instance _p2m_local_instance_fee6646a52_515 : Module.Finite ℤ G := Module.Finite.of_surjective
  (M := Additive (relativeUnitsWithGenerator p hp hKL σ hσ))
  (QuotientAddGroup.mk' _).toIntLinearMap (QuotientAddGroup.mk'_surjective _)
noncomputable def unitlifts (S : systemOfUnits p G (NumberField.Units.rank k + 1)) :
    Fin (NumberField.Units.rank k + 1) → Additive (𝓞 K)ˣ :=
  fun i ↦ Additive.ofMul (Additive.toMul (S.units i).out).out
variable [IsUnramifiedAtInfinitePlaces k K]
local notation "r" => NumberField.Units.rank k
end application
end thm91


