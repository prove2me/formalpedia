-- Prove2me | solution 1 for AddMonoidAlgebra.natCard_withConv_algHom_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/7694bbe4-d5c2-5af0-a4e4-edaa76a5bd76

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddMonoidAlgebra_natCard_withConv_algHom_pow_eq_one

set_option autoImplicit false

open AddMonoidAlgebra WithConv

namespace SplitTorusTorsionCount

universe u v w

section Char

variable (k : Type u) [CommRing k] (M : Type v) [AddCommGroup M]
  (A : Type w) [CommRing A] [Algebra k A]

noncomputable def convEquivChar :
    WithConv (AddMonoidAlgebra k M →ₐ[k] A) ≃* (Multiplicative M →* A) where
  toEquiv := (WithConv.equiv _).trans (AddMonoidAlgebra.lift k A M).symm
  map_mul' φ ψ := by
    refine MonoidHom.ext fun x => ?_
    rw [MonoidHom.mul_apply]
    change (AddMonoidAlgebra.lift k A M).symm (φ * ψ).ofConv x =
      (AddMonoidAlgebra.lift k A M).symm φ.ofConv x * (AddMonoidAlgebra.lift k A M).symm ψ.ofConv x
    rw [AddMonoidAlgebra.lift_symm_apply, AddMonoidAlgebra.lift_symm_apply,
      AddMonoidAlgebra.lift_symm_apply, AlgHom.convMul_apply]
    erw [AddMonoidAlgebra.comul_single]
    simp

theorem convEquivChar_apply (φ : WithConv (AddMonoidAlgebra k M →ₐ[k] A)) (x : Multiplicative M) :
    convEquivChar k M A φ x = φ.ofConv (single (Multiplicative.toAdd x) 1) := rfl

end Char

section Count

variable {M : Type v} [AddCommGroup M] {A : Type w} [CommRing A]

theorem char_ext {ι : Type*} (b : Module.Basis ι ℤ M) (ψ ψ' : Multiplicative M →* A)
    (h : ∀ i, ψ (Multiplicative.ofAdd (b i)) = ψ' (Multiplicative.ofAdd (b i))) : ψ = ψ' := by

  have key : (MonoidHom.toAdditiveRight ψ.toHomUnits).toIntLinearMap =
      (MonoidHom.toAdditiveRight ψ'.toHomUnits).toIntLinearMap := by
    refine b.ext fun i => ?_
    simp only [AddMonoidHom.coe_toIntLinearMap]
    change Additive.ofMul (ψ.toHomUnits (Multiplicative.ofAdd (b i))) =
      Additive.ofMul (ψ'.toHomUnits (Multiplicative.ofAdd (b i)))
    congr 1
    exact Units.ext (h i)
  refine MonoidHom.ext fun x => ?_
  have hx := LinearMap.congr_fun key (Multiplicative.toAdd x)
  simp only [AddMonoidHom.coe_toIntLinearMap] at hx
  have hx' : ψ.toHomUnits x = ψ'.toHomUnits x := Additive.ofMul.injective hx
  have := congrArg (fun u : Aˣ => (u : A)) hx'
  simpa using this

variable (M A)

theorem natCard_char_pow_eq_one [Module.Free ℤ M] [Module.Finite ℤ M]
    (m : ℕ) [NeZero m] [HasEnoughRootsOfUnity A m] :
    Nat.card {ψ : Multiplicative M →* A // ψ ^ m = 1} = m ^ Module.finrank ℤ M := by
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ M
  let b : Module.Basis ι ℤ M := Module.Free.chooseBasis ℤ M
  haveI : Fintype ι := inferInstance

  have hpow : ∀ (ψ : Multiplicative M →* A) (x : Multiplicative M) (n : ℕ),
      (ψ ^ n) x = ψ x ^ n := fun ψ x n => MonoidHom.pow_apply ψ n x
  let F : {ψ : Multiplicative M →* A // ψ ^ m = 1} → (ι → rootsOfUnity m A) := fun ψ i =>
    ⟨ψ.1.toHomUnits (Multiplicative.ofAdd (b i)), by
      rw [mem_rootsOfUnity]
      ext
      rw [Units.val_pow_eq_pow_val, MonoidHom.coe_toHomUnits, ← hpow, ψ.2, Units.val_one,
        MonoidHom.one_apply]⟩
  have hF : ∀ ψ i, ((F ψ i : Aˣ) : A) = ψ.1 (Multiplicative.ofAdd (b i)) := fun ψ i => rfl

  have hinj : Function.Injective F := by
    intro ψ ψ' hψ
    apply Subtype.ext
    refine char_ext b _ _ fun i => ?_
    rw [← hF ψ i, ← hF ψ' i, hψ]

  have hsurj : Function.Surjective F := by
    intro ζ

    let θ : M →ₗ[ℤ] Additive Aˣ := b.constr ℤ fun i => Additive.ofMul (ζ i : Aˣ)
    have hθb : ∀ i, θ (b i) = Additive.ofMul (ζ i : Aˣ) := fun i => by
      simp [θ]
    let χ : Multiplicative M →* Aˣ := AddMonoidHom.toMultiplicativeLeft θ.toAddMonoidHom
    let ψ : Multiplicative M →* A := (Units.coeHom A).comp χ
    have hψ : ∀ x : M, ψ (Multiplicative.ofAdd x) = ((Additive.toMul (θ x) : Aˣ) : A) :=
      fun x => rfl

    have hmθ : (m : ℤ) • θ = 0 := by
      refine b.ext fun i => ?_
      rw [LinearMap.smul_apply, hθb, LinearMap.zero_apply]
      have hζ : ((ζ i : Aˣ)) ^ m = 1 := (mem_rootsOfUnity _ _).1 (ζ i).2
      change Additive.ofMul ((ζ i : Aˣ) ^ (m : ℤ)) = Additive.ofMul 1
      rw [zpow_natCast, hζ]
    have hψm : ψ ^ m = 1 := by
      refine MonoidHom.ext fun x => ?_
      rw [hpow, MonoidHom.one_apply]
      have hx := LinearMap.congr_fun hmθ (Multiplicative.toAdd x)
      rw [LinearMap.smul_apply, LinearMap.zero_apply] at hx
      have hx' : (Additive.toMul (θ (Multiplicative.toAdd x)) : Aˣ) ^ (m : ℤ) = 1 :=
        congrArg Additive.toMul hx
      rw [zpow_natCast] at hx'
      have := congrArg (fun u : Aˣ => (u : A)) hx'
      simp [Units.val_pow_eq_pow_val] at this
      exact this
    refine ⟨⟨ψ, hψm⟩, funext fun i => ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [hF]
    change ψ (Multiplicative.ofAdd (b i)) = _
    rw [hψ, hθb]
    rfl

  rw [Nat.card_eq_of_bijective F ⟨hinj, hsurj⟩, Nat.card_pi, Finset.prod_const, Finset.card_univ,
    HasEnoughRootsOfUnity.natCard_rootsOfUnity A m, Module.finrank_eq_card_basis b]

end Count

theorem main
    (k : Type u) [CommRing k] (M : Type v) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (A : Type w) [CommRing A] [Algebra k A]
    (m : ℕ) [NeZero m] [HasEnoughRootsOfUnity A m] :
    Nat.card {φ : WithConv (AddMonoidAlgebra k M →ₐ[k] A) // φ ^ m = 1} =
      m ^ Module.finrank ℤ M := by
  let e := convEquivChar k M A
  have he : {φ : WithConv (AddMonoidAlgebra k M →ₐ[k] A) // φ ^ m = 1} ≃
      {ψ : Multiplicative M →* A // ψ ^ m = 1} :=
    e.toEquiv.subtypeEquiv fun φ => by
      change φ ^ m = 1 ↔ e φ ^ m = 1
      rw [← map_pow, e.map_eq_one_iff]
  rw [Nat.card_congr he, natCard_char_pow_eq_one M A m]

end SplitTorusTorsionCount

universe u v w

theorem solution
    (k : Type u) [CommRing k] (M : Type v) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (A : Type w) [CommRing A] [Algebra k A]
    (m : ℕ) [NeZero m] [HasEnoughRootsOfUnity A m] :
    Nat.card {φ : WithConv (AddMonoidAlgebra k M →ₐ[k] A) // φ ^ m = 1} =
      m ^ Module.finrank ℤ M :=
  SplitTorusTorsionCount.main k M A m

end S_AddMonoidAlgebra_natCard_withConv_algHom_pow_eq_one
end P2MW
export P2MW.S_AddMonoidAlgebra_natCard_withConv_algHom_pow_eq_one (solution)
