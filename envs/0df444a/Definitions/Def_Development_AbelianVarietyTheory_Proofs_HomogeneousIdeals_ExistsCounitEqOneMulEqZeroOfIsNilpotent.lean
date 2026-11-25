-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:18:11.999586+00:00
-- url     : https://prove2.me/theorems/149b8339-d245-4482-9159-0bfce2a4d9e4
-- title:
--   Exists Counit Eq One Mul Eq Zero Of Is Nilpotent
-- statement:
--   Definitions and structural lemmas for Exists Counit Eq One Mul Eq Zero Of Is Nilpotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsCounitEqOneMulEqZeroOfIsNilpotent.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsCounitDerivationCounitComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Coalgebra Bialgebra HopfAlgebra WithConv
open scoped TensorProduct
namespace GlobalTheory
section Derivations
variable {k H : Type*} [CommRing k] [CommRing H]
theorem isNilpotent_derivation_apply [Algebra k H] [Algebra ℚ H] (D : Derivation k H H) {x : H}
    (hx : IsNilpotent x) : IsNilpotent (D x) := by
  have key : ∀ m j : ℕ, x ^ m * D x ^ j = 0 → IsNilpotent (D x) := by
    intro m
    induction m with
    | zero => intro j h; exact ⟨j, by simpa using h⟩
    | succ m ih =>
      intro j h
      have h1 := congr(D $h)
      rw [Derivation.leibniz, Derivation.leibniz_pow D x (m + 1), map_zero] at h1
      simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel] at h1
      have h2 : ((m + 1 : ℕ) : H) * (x ^ m * D x ^ (2 * j + 1)) = 0 := by
        linear_combination (D x ^ j) * h1 - D (D x ^ j) * h
      have hu : IsUnit ((m + 1 : ℕ) : H) := by
        have : IsUnit ((m + 1 : ℕ) : ℚ) := by
          rw [isUnit_iff_ne_zero]; exact_mod_cast Nat.succ_ne_zero m
        simpa using this.map (algebraMap ℚ H)
      exact ih _ (hu.mul_right_eq_zero.1 h2)
  obtain ⟨n, hn⟩ := hx
  exact key n 0 (by simp [hn])
theorem derivation_sub_nsmul_mem_pow [Algebra k H] (I : Ideal H) (E : Derivation k H H)
    (h0 : ∀ y, E y ∈ I) (h1 : ∀ y ∈ I, E y - y ∈ I ^ 2) (n : ℕ) :
    ∀ y ∈ I ^ n, E y - (n : H) * y ∈ I ^ (n + 1) := by
  induction n with
  | zero => intro y _; simpa using h0 y
  | succ n ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy (fun b hb a ha ↦ ?_) (fun a b ha hb ↦ ?_)
    · have e : E (b * a) - ((n + 1 : ℕ) : H) * (b * a) =
          b * (E a - a) + (E b - n * b) * a := by
        rw [Derivation.leibniz]; simp only [smul_eq_mul]; push_cast; ring
      rw [e]
      refine add_mem ?_ ?_
      · rw [show n + 1 + 1 = n + 2 from rfl, pow_add]
        exact Ideal.mul_mem_mul hb (h1 a ha)
      · rw [pow_succ I (n + 1)]
        exact Ideal.mul_mem_mul (ih b hb) ha
    · have e : E (a + b) - ((n + 1 : ℕ) : H) * (a + b) =
          (E a - ((n + 1 : ℕ) : H) * a) + (E b - ((n + 1 : ℕ) : H) * b) := by
        rw [map_add]; ring
      rw [e]; exact add_mem ha hb
variable [Bialgebra k H]
noncomputable def invariantDerivation (φ : H →ₗ[k] k)
    (hφ : ∀ a b, φ (a * b) = counit (R := k) a * φ b + counit (R := k) b * φ a) :
    Derivation k H H := GlobalTheory.LeftRightDerivations.derivRight φ hφ
theorem invariantDerivation_apply (φ : H →ₗ[k] k)
    (hφ : ∀ a b, φ (a * b) = counit (R := k) a * φ b + counit (R := k) b * φ a) (y : H) :
    invariantDerivation φ hφ y = TensorProduct.rid k H (φ.lTensor H (comul y)) := rfl
theorem counit_invariantDerivation (φ : H →ₗ[k] k)
    (hφ : ∀ a b, φ (a * b) = counit (R := k) a * φ b + counit (R := k) b * φ a) (y : H) :
    counit (R := k) (invariantDerivation φ hφ y) = φ y := by
  have key : ∀ s : H ⊗[k] H, counit (R := k) (TensorProduct.rid k H (φ.lTensor H s)) =
      φ (TensorProduct.lid k H ((counit (R := k)).rTensor H s)) := by
    intro s
    induction s with
    | zero => simp
    | add s s' h h' => simp only [map_add, h, h']
    | tmul a b => simp [mul_comm]
  rw [invariantDerivation_apply, key]
  simp
end Derivations
section Cartier
variable {k H : Type*} [Field k] [CommRing H]
theorem exists_derivations_sum_sub_mem_sq [Bialgebra k H] [Algebra.FiniteType k H] :
    ∃ (n : ℕ) (x : Fin n → H) (D : Fin n → Derivation k H H),
      (∀ i, x i ∈ RingHom.ker (counitAlgHom k H)) ∧
      ∀ y ∈ RingHom.ker (counitAlgHom k H),
        ∑ i, x i * D i y - y ∈ RingHom.ker (counitAlgHom k H) ^ 2 := by
  set I := RingHom.ker (counitAlgHom k H) with hI
  have hmem : ∀ y, y ∈ I ↔ counit (R := k) y = 0 := fun y ↦ by simp [hI, RingHom.mem_ker]
  have : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  let p : H →ₗ[k] H := LinearMap.id - Algebra.linearMap k H ∘ₗ counit
  have hp : ∀ y, p y = y - algebraMap k H (counit y) := fun y ↦ rfl
  have hpI : ∀ y, p y ∈ I := fun y ↦ by simp [hmem, hp]
  let q : H →ₗ[k] H ⧸ I ^ 2 := (Ideal.Quotient.mkₐ k (I ^ 2)).toLinearMap ∘ₗ p
  have hq : ∀ y, q y = Ideal.Quotient.mk (I ^ 2) (p y) := fun y ↦ rfl
  have hqmul : ∀ a b, q (a * b) = counit (R := k) a • q b + counit (R := k) b • q a := by
    intro a b
    rw [← map_smul, ← map_smul, ← map_add, hq, hq, Ideal.Quotient.eq]
    have : p (a * b) - p (counit (R := k) a • b + counit (R := k) b • a) = p a * p b := by
      simp only [hp, map_add, map_smul, counit_mul, smul_eq_mul, map_mul, Algebra.smul_def,
        counit_algebraMap, Algebra.algebraMap_self, RingHom.id_apply]
      ring
    rw [this, sq]
    exact Ideal.mul_mem_mul (hpI a) (hpI b)
  have hfin : Module.Finite k (LinearMap.range q) := by
    obtain ⟨s, hs⟩ : I.FG := IsNoetherian.noetherian I
    have hle : LinearMap.range q ≤ Submodule.span k (q '' s) := by
      rintro _ ⟨y, rfl⟩
      have h1 : q y = q (p y) := by
        rw [hq, hq, hp (p y), (hmem _).1 (hpI y)]; simp
      have h2 : ∀ z ∈ I, q z ∈ Submodule.span k (q '' s) := by
        intro z hz
        rw [← hs] at hz
        induction hz using Submodule.span_induction with
        | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
        | zero => simp
        | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
        | smul a x hx' hx =>
          have : x ∈ I := hs ▸ hx'
          rw [smul_eq_mul, hqmul, (hmem x).1 this, zero_smul, add_zero]
          exact Submodule.smul_mem _ _ hx
      rw [h1]; exact h2 _ (hpI y)
    have : Module.Finite k (Submodule.span k (q '' s)) :=
      Module.Finite.span_of_finite k (s.finite_toSet.image _)
    exact Submodule.finiteDimensional_of_le hle
  let b := Module.finBasis k (LinearMap.range q)
  choose z hz using fun i ↦ (b i).2
  let φ : _ → H →ₗ[k] k := fun i ↦ b.coord i ∘ₗ q.rangeRestrict
  have hφ : ∀ i a c, φ i (a * c) = counit (R := k) a * φ i c + counit (R := k) c * φ i a := by
    intro i a c
    have : q.rangeRestrict (a * c) =
        counit (R := k) a • q.rangeRestrict c + counit (R := k) c • q.rangeRestrict a :=
      Subtype.ext (hqmul a c)
    simp only [φ, LinearMap.comp_apply, this, map_add, map_smul, smul_eq_mul]
  refine ⟨_, fun i ↦ p (z i), fun i ↦ invariantDerivation (φ i) (hφ i), fun i ↦ hpI _,
    fun y hy ↦ ?_⟩
  have h1 : ∑ i, φ i y • p (z i) - y ∈ I ^ 2 := by
    rw [← Ideal.Quotient.eq]
    have h2 := congr(($(b.sum_repr (q.rangeRestrict y)) : H ⧸ I ^ 2))
    simp only [Submodule.coe_sum, Submodule.coe_smul, ← hz] at h2
    have h3 : Ideal.Quotient.mk (I ^ 2) y = q y := by
      rw [hq, hp, (hmem y).1 hy]; simp
    rw [h3, map_sum]
    exact h2
  have h2 : ∑ i, p (z i) * p (invariantDerivation (φ i) (hφ i) y) ∈ I ^ 2 :=
    Ideal.sum_mem _ fun i _ ↦ by rw [sq]; exact Ideal.mul_mem_mul (hpI _) (hpI _)
  convert add_mem h2 h1 using 1
  rw [← add_sub_assoc, ← Finset.sum_add_distrib]
  congr 2 with i
  rw [hp (invariantDerivation _ _ _), counit_invariantDerivation, Algebra.smul_def]
  ring
theorem mem_ker_counit_pow_of_isNilpotent [CharZero k] [Bialgebra k H] [Algebra.FiniteType k H]
    (n : ℕ) {y : H} (hy : IsNilpotent y) : y ∈ RingHom.ker (counitAlgHom k H) ^ n := by
  obtain ⟨m, x, D, hx, hD⟩ := exists_derivations_sum_sub_mem_sq (k := k) (H := H)
  set I := RingHom.ker (counitAlgHom k H) with hI
  letI : Algebra ℚ H := ((algebraMap k H).comp (algebraMap ℚ k)).toAlgebra
  let E : Derivation k H H := ∑ i, x i • D i
  have hE : ∀ y, E y = ∑ i, x i * D i y := fun y ↦ by
    have := congr($(map_sum (Derivation.coeFnAddMonoidHom (R := k) (A := H) (M := H))
      (fun i ↦ x i • D i) Finset.univ) y)
    rw [Finset.sum_apply] at this
    exact this
  have hn := derivation_sub_nsmul_mem_pow I E
    (fun y ↦ by rw [hE]; exact Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_right _ _ (hx i))
    (fun y hy ↦ by rw [hE]; exact hD y hy)
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simpa [hI, RingHom.mem_ker] using (hy.map (counitAlgHom k H)).eq_zero
    have h1 : E y ∈ I ^ (n + 1) := by
      rw [hE, pow_succ']
      exact Ideal.sum_mem _ fun i _ ↦
        Ideal.mul_mem_mul (hx i) (ih (isNilpotent_derivation_apply _ hy))
    have h2 : (n : H) * y ∈ I ^ (n + 1) := by simpa using sub_mem h1 (hn n y (ih hy))
    have hu : IsUnit (n : H) := by
      have : IsUnit (n : k) := by
        rw [isUnit_iff_ne_zero]; exact_mod_cast hpos.ne'
      simpa using this.map (algebraMap k H)
    exact (Ideal.unit_mul_mem_iff_mem _ hu).1 h2
theorem exists_counit_eq_one_mul_eq_zero_of_isNilpotent [CharZero k] [Bialgebra k H]
    [Algebra.FiniteType k H] {y : H} (hy : IsNilpotent y) :
    ∃ s : H, counit (R := k) s = 1 ∧ s * y = 0 := by
  have : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  obtain ⟨r, hr⟩ := ((RingHom.ker (counitAlgHom k H)).mem_iInf_smul_pow_eq_bot_iff y).1 <| by
    rw [Submodule.mem_iInf]
    intro n
    simpa using mem_ker_counit_pow_of_isNilpotent n hy
  refine ⟨1 - r, ?_, ?_⟩
  · have : counit (R := k) (r : H) = 0 := r.2
    simp [this]
  · rw [smul_eq_mul] at hr
    rw [sub_mul, hr, one_mul, sub_self]
end Cartier
section Translation
variable {k H : Type*} [CommRing k] [CommRing H] [HopfAlgebra k H]
theorem exists_algEquiv_counit_comp_eq (χ : H →ₐ[k] k) :
    ∃ τ : H ≃ₐ[k] H, ∀ y, counit (R := k) (τ y) = χ y := by
  let u : WithConv (H →ₐ[k] H) := toConv ((Algebra.ofId k H).comp χ)
  let v : WithConv (H →ₐ[k] H) := u⁻¹
  let e : WithConv (H →ₐ[k] H) := toConv (AlgHom.id k H)
  have hu' : ∀ f : H →ₐ[k] H, f.comp u.ofConv = u.ofConv := fun f ↦ by
    ext y; simp [u]
  have hv' : ∀ f : H →ₐ[k] H, f.comp v.ofConv = v.ofConv := fun f ↦ by
    change f.comp (u.ofConv.comp _) = u.ofConv.comp _
    rw [← AlgHom.comp_assoc, hu']
  have he : ∀ f : H →ₐ[k] H, f.comp e.ofConv = f := fun f ↦ rfl
  refine ⟨AlgEquiv.ofAlgHom (e * u).ofConv (e * v).ofConv ?_ ?_, fun y ↦ ?_⟩
  · rw [AlgHom.comp_convMul_distrib, he, hv', toConv_ofConv, toConv_ofConv, mul_inv_cancel_right]
  · rw [AlgHom.comp_convMul_distrib, he, hu', toConv_ofConv, toConv_ofConv, inv_mul_cancel_right]
  · have h := AlgHom.comp_convMul_distrib (counitAlgHom k H) e u
    have h1 : toConv ((counitAlgHom k H).comp e.ofConv) = 1 := by
      rw [AlgHom.convOne_def]; rfl
    rw [h1, one_mul] at h
    refine congr($h y).trans ?_
    simp [u]
end Translation
section Reduced
variable (k H : Type*) [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
theorem isReduced_of_hopfAlgebra_of_isAlgClosed [IsAlgClosed k] [Algebra.FiniteType k H] :
    IsReduced H := by
  refine ⟨fun y hy ↦ ?_⟩
  by_contra hne
  have hA : (Ideal.span {y}).annihilator ≠ ⊤ := by
    intro h
    have : (1 : H) ∈ (Ideal.span {y}).annihilator := h ▸ Submodule.mem_top
    exact hne (by simpa using Submodule.mem_annihilator.1 this y (Ideal.mem_span_singleton_self y))
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hA
  letI := Ideal.Quotient.field m
  have : Module.Finite k (H ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (H ⧸ m)
  let e : k ≃ₐ[k] H ⧸ m :=
    .ofBijective (Algebra.ofId k _) IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨τ, hτ⟩ := exists_algEquiv_counit_comp_eq (e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m))
  obtain ⟨s, hs, hsy⟩ := exists_counit_eq_one_mul_eq_zero_of_isNilpotent (k := k) (hy.map τ)
  have h1 : τ.symm s * y = 0 := τ.injective (by simpa using hsy)
  have h2 : τ.symm s ∈ m := hle (by
    rw [Ideal.span, Submodule.mem_annihilator_span_singleton]; exact h1)
  have h3 := hτ (τ.symm s)
  rw [τ.apply_symm_apply, hs] at h3
  simp [Ideal.Quotient.eq_zero_iff_mem.2 h2] at h3
theorem isReduced_of_hopfAlgebra [Algebra.FiniteType k H] : IsReduced H := by
  have := isReduced_of_hopfAlgebra_of_isAlgClosed (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] H)
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : H →ₐ[k] AlgebraicClosure k ⊗[k] H)
    (Algebra.TensorProduct.includeRight_injective (algebraMap k _).injective)
theorem etale_of_hopfAlgebra [Module.Finite k H] : Algebra.Etale k H :=
  have := isReduced_of_hopfAlgebra k H
  etale_of_isReduced_of_perfectField k H
end Reduced
section Schemes
open CategoryTheory AlgebraicGeometry
universe u
theorem exists_hopfAlgebra_sections (R : CommRingCat.{u}) (G : Scheme.{u}) [G.Over (Spec R)]
    [GrpObj (G.asOver (Spec R))] [IsAffine G] :
    ∃ h : HopfAlgebra R Γ(G, ⊤),
      Spec.map (CommRingCat.ofHom (@algebraMap R Γ(G, ⊤) _ _ h.toAlgebra)) =
        G.isoSpec.inv ≫ G ↘ Spec R :=
  ⟨inferInstance,
    Spec.fullyFaithful.map_preimage (X := .op Γ(G, ⊤)) (Y := .op R) (G.isoSpec.inv ≫ G ↘ Spec R)⟩
variable {k : Type u} [Field k] [CharZero k] {G : Scheme.{u}} (f : G ⟶ Spec (.of k))
  [GrpObj (Over.mk f)]
theorem isReduced_of_grpObj_of_isAffine [IsAffine G] [LocallyOfFiniteType f] : IsReduced G := by
  letI : G.Over (Spec (.of k)) := ⟨f⟩
  letI : GrpObj (G.asOver (Spec (.of k))) := ‹GrpObj (Over.mk f)›
  obtain ⟨_, h⟩ := exists_hopfAlgebra_sections (.of k) G
  replace h : Spec.map (CommRingCat.ofHom (algebraMap k Γ(G, ⊤))) = G.isoSpec.inv ≫ f := h
  have : Algebra.FiniteType k Γ(G, ⊤) := by
    have h1 : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k Γ(G, ⊤)))) := by
      rw [h]; infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h1
    exact RingHom.finiteType_algebraMap.1 h1
  have := isReduced_of_hopfAlgebra k Γ(G, ⊤)
  exact isReduced_of_isAffine_isReduced G
theorem smooth_of_grpObj_of_isAffine [IsAffine G] [LocallyOfFiniteType f] : Smooth f := by
  have : GeometricallyReduced f := by
    refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.2 fun K _ _ ↦ ?_⟩
    have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
    let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom <| algebraMap k K)
    let : GrpObj (Over.mk (Limits.pullback.snd f g)) := Over.grpObjMkPullbackSnd
    exact isReduced_of_grpObj_of_isAffine (Limits.pullback.snd f g)
  exact smooth_of_grpObj f
theorem smooth_of_hopfAlgebra (k H : Type u) [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
    [Algebra.FiniteType k H] : Algebra.Smooth k H := by
  let f : Spec (.of H) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k H))
  letI : GrpObj (Over.mk f) :=
    instGrpObjSpecAsOverSpec (R := CommRingCat.of k) (A := CommRingCat.of H)
  have : LocallyOfFiniteType f :=
    locallyOfFiniteType_specOverSpec (R := CommRingCat.of k) (A := CommRingCat.of H)
  have h := smooth_of_grpObj_of_isAffine f
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at h
  exact RingHom.smooth_algebraMap.1 h
end Schemes
section Closure
variable {V : Type*} (K : Type*) {H : Type*} [CommRing V] [CommRing K] [Algebra V K] [CommRing H]
noncomputable def closureIdeal [Algebra V H] (J : Ideal (K ⊗[V] H)) : Ideal H :=
  J.comap (Algebra.TensorProduct.includeRight : H →ₐ[V] K ⊗[V] H)
variable {K}
@[simp]
theorem mem_closureIdeal [Algebra V H] {J : Ideal (K ⊗[V] H)} {x : H} :
    x ∈ closureIdeal K J ↔ (1 : K) ⊗ₜ[V] x ∈ J := Iff.rfl
section Algebra
variable [Algebra V H] [IsFractionRing V K] (J : Ideal (K ⊗[V] H))
theorem torsion_quotient_closureIdeal : Submodule.torsion V (H ⧸ closureIdeal K J) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨a, ha⟩, hx⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h1 : a • x ∈ closureIdeal K J := Ideal.Quotient.eq_zero_iff_mem.1 hx
  rw [mem_closureIdeal] at h1
  have hu : IsUnit (algebraMap V (K ⊗[V] H) a) := by
    rw [IsScalarTower.algebraMap_apply V K (K ⊗[V] H)]
    exact (IsLocalization.map_units K ⟨a, ha⟩).map _
  rw [TensorProduct.tmul_smul, Algebra.smul_def, Ideal.unit_mul_mem_iff_mem _ hu] at h1
  exact Ideal.Quotient.eq_zero_iff_mem.2 h1
instance isTorsionFree_quotient_closureIdeal [IsDomain V] :
    Module.IsTorsionFree V (H ⧸ closureIdeal K J) :=
  Submodule.isTorsionFree_iff_torsion_eq_bot.2 (torsion_quotient_closureIdeal J)
theorem map_closureIdeal :
    (closureIdeal K J).map (Algebra.TensorProduct.includeRight : H →ₐ[V] K ⊗[V] H) = J := by
  letI : Algebra H (K ⊗[V] H) := Algebra.TensorProduct.rightAlgebra
  have := IsLocalization.tensorRight (R := V) (S := H) K (nonZeroDivisors V)
  exact IsLocalization.map_under (Algebra.algebraMapSubmonoid H (nonZeroDivisors V)) (K ⊗[V] H) J
noncomputable def baseChangeQuotientClosureIdealEquiv :
    K ⊗[V] (H ⧸ closureIdeal K J) ≃ₐ[K] (K ⊗[V] H) ⧸ J :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := V) K H K (closureIdeal K J)).trans
    (Ideal.quotientEquivAlgOfEq K (map_closureIdeal J))
@[simp]
theorem baseChangeQuotientClosureIdealEquiv_tmul (a : K) (x : H) :
    baseChangeQuotientClosureIdealEquiv J (a ⊗ₜ Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk J (a ⊗ₜ x) := rfl
theorem flat_quotient_closureIdeal_of_isDedekindDomain [IsDedekindDomain V] :
    Module.Flat V (H ⧸ closureIdeal K J) :=
  IsDedekindDomain.flat_iff_torsion_eq_bot.2 (torsion_quotient_closureIdeal J)
end Algebra
end Closure
section HopfClosure
variable {V K H : Type*} [CommRing V] [Field K] [Algebra V K] [CommRing H]
variable [HopfAlgebra V H] [IsFractionRing V K] (J : Ideal (K ⊗[V] H)) [J.IsHopfIdeal K]
theorem isHopfIdeal_closureIdeal_of_flat [Module.Flat V (H ⧸ closureIdeal K J)] :
    (closureIdeal K J).IsHopfIdeal V where
  counit_eq_zero x hx := by
    have h := Submodule.IsCoideal.counit_eq_zero (I := J.restrictScalars K) hx
    apply IsFractionRing.injective V K
    simpa [Algebra.smul_def] using h
  antipode_mem x hx := by
    have h := Ideal.IsHopfIdeal.antipode_mem (R := K) (I := J) hx
    simpa using h
  map_mkQ_comul_eq_zero x hx := by
    have h := Submodule.IsCoideal.map_mkQ_comul_eq_zero (I := J.restrictScalars K) hx
    let Q := (K ⊗[V] H) ⧸ J.restrictScalars K
    let P := H ⧸ closureIdeal K J
    let π : H →ₗ[V] P := (Ideal.Quotient.mkₐ V (closureIdeal K J)).toLinearMap
    let ι : P →ₗ[V] Q := ((closureIdeal K J).restrictScalars V).liftQ
      ((J.restrictScalars K).mkQ.restrictScalars V ∘ₗ TensorProduct.mk V K H 1)
      (fun y hy ↦ (Submodule.Quotient.mk_eq_zero _).2 hy)
    have hι : Function.Injective ι := by
      rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact Ideal.Quotient.eq_zero_iff_mem.2
        ((Submodule.Quotient.mk_eq_zero (J.restrictScalars K)).1 hy)
    have hinj : Function.Injective (TensorProduct.map ι ι) := by
      have : Module.Flat V K := IsLocalization.flat K (nonZeroDivisors V)
      have : Module.Flat V Q := Module.Flat.trans V K Q
      rw [← LinearMap.rTensor_comp_lTensor, LinearMap.coe_comp]
      exact (Module.Flat.rTensor_preserves_injective_linearMap ι hι).comp
        (Module.Flat.lTensor_preserves_injective_linearMap ι hι)
    change TensorProduct.map π π (comul x) = 0
    apply hinj
    apply (IsLocalization.moduleTensorEquiv (nonZeroDivisors V) K Q Q).symm.injective
    rw [map_zero, map_zero, ← h, Algebra.TensorProduct.includeRight_apply,
      TensorProduct.comul_tmul]
    generalize comul (R := V) x = t
    induction t with
    | zero => simp only [map_zero, TensorProduct.tmul_zero]
    | add a b ha hb => simp only [map_add, TensorProduct.tmul_add, ha, hb]
    | tmul a b =>
      simp only [CommSemiring.comul_apply, TensorProduct.map_tmul, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
      rfl
theorem isHopfIdeal_closureIdeal_of_isDedekindDomain [IsDedekindDomain V] :
    (closureIdeal K J).IsHopfIdeal V :=
  have := flat_quotient_closureIdeal_of_isDedekindDomain J
  isHopfIdeal_closureIdeal_of_flat J
end HopfClosure
section Surjections
end Surjections
section Examples
theorem isHopfIdeal_ker_counit (R H : Type*) [CommRing R] [CommRing H] [HopfAlgebra R H] :
    (RingHom.ker (counitAlgHom R H)).IsHopfIdeal R where
  counit_eq_zero _ hx := hx
  antipode_mem x hx := by
    have hx' : counit (R := R) x = 0 := hx
    change counit (R := R) (antipode R x) = 0
    simpa using hx'
  map_mkQ_comul_eq_zero x hx := by
    have hx' : counit (R := R) x = 0 := hx
    set π := ((RingHom.ker (counitAlgHom R H)).restrictScalars R).mkQ with hπ
    have h1 : ∀ y, π y = counit (R := R) y • π 1 := fun y ↦ by
      rw [← map_smul, hπ, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      change counit (R := R) (y - counit (R := R) y • (1 : H)) = 0
      simp
    have h2 : ∀ t : H ⊗[R] H, TensorProduct.map π π t =
        π 1 ⊗ₜ π (TensorProduct.lid R H ((counit (R := R)).rTensor H t)) := by
      intro t
      induction t with
      | zero => simp
      | add a b ha hb => simp only [map_add, TensorProduct.tmul_add, ha, hb]
      | tmul a b =>
        rw [TensorProduct.map_tmul, h1 a, TensorProduct.smul_tmul, LinearMap.rTensor_tmul,
          TensorProduct.lid_tmul, map_smul]
    rw [h2, rTensor_counit_comul, TensorProduct.lid_tmul, one_smul, h1 x, hx', zero_smul,
      TensorProduct.tmul_zero]
example : Algebra.Etale ℚ (AddMonoidAlgebra ℚ (ZMod 3)) := etale_of_hopfAlgebra _ _
example : Algebra.Smooth ℚ (AddMonoidAlgebra ℚ ℤ) := smooth_of_hopfAlgebra _ _
example : (closureIdeal (V := ℤ) ℚ
    (RingHom.ker (counitAlgHom ℚ (ℚ ⊗[ℤ] AddMonoidAlgebra ℤ (ZMod 3))))).IsHopfIdeal ℤ :=
  have := isHopfIdeal_ker_counit ℚ (ℚ ⊗[ℤ] AddMonoidAlgebra ℤ (ZMod 3))
  isHopfIdeal_closureIdeal_of_isDedekindDomain _
end Examples
end GlobalTheory


