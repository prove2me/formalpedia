-- Prove2me | solution 1 for Algebra.IsInvariant.exists_ringHom_eq_comp_toRingHom_of_comp_algebraMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/19235d59-db2b-574b-93e1-24ec65572225

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_IsInvariant_exists_ringHom_eq_comp_toRingHom_of_comp_algebraMap_eq

open scoped Pointwise
open Polynomial

namespace P2mKcAffineQuotientGeomPoints

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  {Ω : Type*} [Field Ω]

omit [SMulCommClass G A B] in

theorem exists_apply_eq_apply_smul [Algebra.IsInvariant A B G] (φ₁ φ₂ : B →+* Ω)
    (h : φ₁.comp (algebraMap A B) = φ₂.comp (algebraMap A B)) (b : B) :
    ∃ g : G, φ₂ b = φ₁ (g • b) := by
  classical
  cases nonempty_fintype G
  obtain ⟨p, hp⟩ := (Polynomial.mem_lifts _).mp
    (Algebra.IsInvariant.charpoly_mem_lifts A B G b)

  have h2 : ((MulSemiringAction.charpoly G b).map φ₂).eval (φ₂ b) = 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, MulSemiringAction.eval_charpoly, map_zero]

  have h12 : (MulSemiringAction.charpoly G b).map φ₂ = (MulSemiringAction.charpoly G b).map φ₁ := by
    rw [← hp, Polynomial.map_map, Polynomial.map_map, ← h]
  rw [h12, MulSemiringAction.charpoly_eq, Polynomial.map_prod, Polynomial.eval_prod,
    Finset.prod_eq_zero_iff] at h2
  obtain ⟨g, -, hg⟩ := h2
  refine ⟨g, ?_⟩
  rwa [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, eval_sub, eval_X, eval_C,
    sub_eq_zero] at hg

omit [Finite G] in

theorem ker_comp_toRingHom (φ : B →+* Ω) (g : G) :
    RingHom.ker (φ.comp (MulSemiringAction.toRingHom G B g⁻¹)) = g • RingHom.ker φ := by
  ext b
  rw [RingHom.mem_ker, RingHom.comp_apply, MulSemiringAction.toRingHom_apply,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem, RingHom.mem_ker]

omit [Finite G] in
theorem comp_toRingHom_comp_algebraMap (φ : B →+* Ω) (g : G) :
    (φ.comp (MulSemiringAction.toRingHom G B g)).comp (algebraMap A B) =
      φ.comp (algebraMap A B) := by
  ext a
  simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply, smul_algebraMap]

theorem exists_eq_comp_toRingHom_of_ker_eq [Algebra.IsInvariant A B G] (φ₁ φ₂ : B →+* Ω)
    (h : φ₁.comp (algebraMap A B) = φ₂.comp (algebraMap A B))
    (hker : RingHom.ker φ₁ = RingHom.ker φ₂) :
    ∃ g : G, φ₂ = φ₁.comp (MulSemiringAction.toRingHom G B g) := by
  classical
  cases nonempty_fintype G
  set Q : Ideal B := RingHom.ker φ₁ with hQdef
  haveI hQ : Q.IsPrime := RingHom.ker_isPrime φ₁
  set P : Ideal A := Q.under A with hPdef
  haveI : Q.LiesOver P := ⟨rfl⟩
  haveI hP : P.IsPrime := Ideal.IsPrime.under A Q

  have hle₁ : Q ≤ RingHom.ker φ₁ := le_rfl
  have hle₂ : Q ≤ RingHom.ker φ₂ := hker.le
  set ψ₁ : B ⧸ Q →+* Ω := Ideal.Quotient.lift Q φ₁ fun b hb => hle₁ hb with hψ₁
  set ψ₂ : B ⧸ Q →+* Ω := Ideal.Quotient.lift Q φ₂ fun b hb => hle₂ hb with hψ₂
  have hψ₁inj : Function.Injective ψ₁ := by
    rw [hψ₁, Ideal.injective_lift_iff]
  have hψ₂inj : Function.Injective ψ₂ := by
    rw [hψ₂, Ideal.injective_lift_iff]; exact hker.symm

  let K := FractionRing (A ⧸ P)
  let L := FractionRing (B ⧸ Q)
  letI : Algebra K L := FractionRing.liftAlgebra (A ⧸ P) L

  set θ₁ : L →+* Ω := IsFractionRing.lift hψ₁inj with hθ₁
  set θ₂ : L →+* Ω := IsFractionRing.lift hψ₂inj with hθ₂
  have hθ₁B : ∀ b : B, θ₁ (algebraMap (B ⧸ Q) L (Ideal.Quotient.mk Q b)) = φ₁ b := fun b => by
    rw [hθ₁, IsFractionRing.lift_algebraMap, hψ₁, Ideal.Quotient.lift_mk]
  have hθ₂B : ∀ b : B, θ₂ (algebraMap (B ⧸ Q) L (Ideal.Quotient.mk Q b)) = φ₂ b := fun b => by
    rw [hθ₂, IsFractionRing.lift_algebraMap, hψ₂, Ideal.Quotient.lift_mk]

  have hθK : ∀ k : K, θ₂ (algebraMap K L k) = θ₁ (algebraMap K L k) := by
    suffices hc : θ₂.comp (algebraMap K L) = θ₁.comp (algebraMap K L) from
      fun k => congrArg (fun f : K →+* Ω => f k) hc
    apply IsFractionRing.ringHom_ext (A := A ⧸ P)
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply (A ⧸ P) K L,
      IsScalarTower.algebraMap_apply (A ⧸ P) (B ⧸ Q) L,
      Ideal.Quotient.algebraMap_mk_of_liesOver, hθ₁B, hθ₂B]
    exact (congrArg (fun f : A →+* Ω => f a) h).symm

  letI : Algebra K Ω := (θ₁.comp (algebraMap K L)).toAlgebra
  let η₁ : L →ₐ[K] Ω := ⟨θ₁, fun k => rfl⟩
  let η₂ : L →ₐ[K] Ω := ⟨θ₂, fun k => hθK k⟩
  have hη₁ : ∀ x, η₁ x = θ₁ x := fun x => rfl
  have hη₂ : ∀ x, η₂ x = θ₂ x := fun x => rfl

  haveI : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  have hgen : ∀ x : L, ∃ (k : K) (b : B), x = k • algebraMap (B ⧸ Q) L (Ideal.Quotient.mk Q b) := by
    intro x
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := B ⧸ Q) x
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    obtain ⟨c, d, hd, hcd⟩ :=
      Algebra.IsAlgebraic.exists_smul_eq_mul (A ⧸ P) x hy0
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨(algebraMap (A ⧸ P) K d)⁻¹, c, ?_⟩
    have hd' : algebraMap (A ⧸ P) L d ≠ 0 := by
      rwa [Ne, IsScalarTower.algebraMap_apply (A ⧸ P) K L, map_eq_zero_iff _
        (algebraMap K L).injective, map_eq_zero_iff _
        (FaithfulSMul.algebraMap_injective (A ⧸ P) K)]
    have hyL : algebraMap (B ⧸ Q) L y ≠ 0 :=
      mt (map_eq_zero_iff _ (IsFractionRing.injective (B ⧸ Q) L)).mp hy0
    rw [div_eq_iff hyL, Algebra.smul_def, map_inv₀, ← IsScalarTower.algebraMap_apply,
      mul_assoc, eq_inv_mul_iff_mul_eq₀ hd', IsScalarTower.algebraMap_apply (A ⧸ P) (B ⧸ Q) L,
      ← map_mul, ← map_mul, ← Algebra.smul_def, hcd, mul_comm]

  have hrange : ∀ (χ₁ χ₂ : B →+* Ω) (μ₁ μ₂ : L →ₐ[K] Ω),
      χ₁.comp (algebraMap A B) = χ₂.comp (algebraMap A B) →
      (∀ b : B, μ₁ (algebraMap (B ⧸ Q) L (Ideal.Quotient.mk Q b)) = χ₁ b) →
      (∀ b : B, μ₂ (algebraMap (B ⧸ Q) L (Ideal.Quotient.mk Q b)) = χ₂ b) →
      μ₂.range ≤ μ₁.range := by
    intro χ₁ χ₂ μ₁ μ₂ hχ h₁ h₂ y hy
    rw [AlgHom.mem_range] at hy
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨k, b, rfl⟩ := hgen x
    rw [map_smul]
    refine Subalgebra.smul_mem _ ?_ k
    obtain ⟨g, hg⟩ := exists_apply_eq_apply_smul G χ₁ χ₂ hχ b
    rw [h₂, hg, ← h₁]
    exact AlgHom.mem_range_self μ₁ _
  have hR : η₂.range = η₁.range :=
    le_antisymm (hrange φ₁ φ₂ η₁ η₂ h hθ₁B hθ₂B) (hrange φ₂ φ₁ η₂ η₁ h.symm hθ₂B hθ₁B)

  let e₁ : L ≃ₐ[K] η₁.range := AlgEquiv.ofInjectiveField η₁
  let e₂ : L ≃ₐ[K] η₂.range := AlgEquiv.ofInjectiveField η₂
  let σ : L ≃ₐ[K] L := (e₂.trans (Subalgebra.equivOfEq _ _ hR)).trans e₁.symm
  have hσ : ∀ x : L, θ₁ (σ x) = θ₂ x := by
    intro x
    have h1 : (e₁ (σ x) : Ω) = θ₁ (σ x) := AlgEquiv.ofInjective_apply _ _ _
    rw [← h1]
    change ((e₁ (e₁.symm ((Subalgebra.equivOfEq _ _ hR) (e₂ x)))) : Ω) = θ₂ x
    rw [AlgEquiv.apply_symm_apply]
    change ((e₂ x : η₂.range) : Ω) = θ₂ x
    exact AlgEquiv.ofInjective_apply _ _ _

  obtain ⟨g, hg⟩ := IsFractionRing.stabilizerHom_surjective G P Q K L σ
  refine ⟨(g : G), RingHom.ext fun b => ?_⟩
  rw [RingHom.comp_apply, MulSemiringAction.toRingHom_apply, ← hθ₂B, ← hσ, ← hg,
    ← MulAction.subgroup_smul_def, IsFractionRing.stabilizerHom_apply_apply_mk, hθ₁B]
  rfl

theorem exists_eq_comp_toRingHom [Algebra.IsInvariant A B G] (φ₁ φ₂ : B →+* Ω)
    (h : φ₁.comp (algebraMap A B) = φ₂.comp (algebraMap A B)) :
    ∃ g : G, φ₂ = φ₁.comp (MulSemiringAction.toRingHom G B g) := by
  haveI h1 : (RingHom.ker φ₁).IsPrime := RingHom.ker_isPrime φ₁
  haveI h2 : (RingHom.ker φ₂).IsPrime := RingHom.ker_isPrime φ₂
  have hunder : (RingHom.ker φ₁).under A = (RingHom.ker φ₂).under A := by
    rw [Ideal.under_def, Ideal.under_def, RingHom.comap_ker, RingHom.comap_ker, h]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G _ _ hunder

  set φ₁' := φ₁.comp (MulSemiringAction.toRingHom G B g⁻¹) with hφ₁'
  have hker : RingHom.ker φ₁' = RingHom.ker φ₂ := by rw [hφ₁', ker_comp_toRingHom, hg]
  have h' : φ₁'.comp (algebraMap A B) = φ₂.comp (algebraMap A B) := by
    rw [hφ₁', comp_toRingHom_comp_algebraMap, h]
  obtain ⟨g', hg'⟩ := exists_eq_comp_toRingHom_of_ker_eq G φ₁' φ₂ h' hker
  refine ⟨g⁻¹ * g', ?_⟩
  rw [hg', hφ₁']
  ext b
  simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply, mul_smul]

end P2mKcAffineQuotientGeomPoints

theorem solution
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G]
    {Ω : Type*} [Field Ω] (φ₁ φ₂ : B →+* Ω)
    (h : φ₁.comp (algebraMap A B) = φ₂.comp (algebraMap A B)) :
    ∃ g : G, φ₂ = φ₁.comp (MulSemiringAction.toRingHom G B g) :=
  P2mKcAffineQuotientGeomPoints.exists_eq_comp_toRingHom G φ₁ φ₂ h

end S_Algebra_IsInvariant_exists_ringHom_eq_comp_toRingHom_of_comp_algebraMap_eq
end P2MW
export P2MW.S_Algebra_IsInvariant_exists_ringHom_eq_comp_toRingHom_of_comp_algebraMap_eq (solution)
