-- Prove2me | Definitions.Def_DedekindDomain_IntegralClosure
-- name    : DedekindDomain_IntegralClosure
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/d956b31c-1152-5b1b-823d-29c7b7b3a667
-- title:
--   Primes over a prime in an AKLB extension; base change
-- statement:
--   The first part of the module works in the AKLB setting: $A$ a Dedekind domain with fraction field $K$, $L$ a field extension of $K$, and $B$ a Dedekind domain which is the integral closure of $A$ in $L$, integral over $A$ and with fraction field $L$. For $v$ in the height-one spectrum of $A$, `Extension B v` is defined as the subtype of height-one primes $w$ of $B$ whose contraction `w.under A` equals $v$. The accompanying results are: for injective $A \to B$, the multiplicity of $w$ in the factorisation of the extended ideal $I B$ equals $e(w \mid w\cap A)$ times the multiplicity of $w\cap A$ in $I$ (written with `Associates` factor counts), and the ramification index $e =$ `Ideal.ramificationIdx'` of $w$ over $w \cap A$ is nonzero; the compatibility of valuations, namely that the $e$-th power of the $(w\cap A)$-adic valuation of $x$ is the $w$-adic valuation of the image of $x$, both for $x \in A$ with the integral valuations and for $x \in K$ with the valuations on $K$ and $L$; torsion-freeness of $B$ as an $A$-module; finiteness of `Extension B v`, with a derived `Fintype` instance, finiteness of the preimage under contraction of a finite set of height-one primes of $A$, the corresponding `Finset`, and, for $B$ finite over $A$, the fundamental identity $\sum_{w \mid v} e(w\mid v) f(w\mid v) = [L:K]$ with the sum taken over `Extension B v`.
--
--   The second part, with $L/K$ algebraic and $B$ the integral closure of $A$ in $L$, provides base-change equivalences: a $K$-linear isomorphism $L \cong K \otimes_A B$, together with the computation of its inverse on $k \otimes b$ as $k \cdot b$; for a $K$-module $M$ which is also an $A$-module compatibly, $A$-linear and $B$-linear isomorphisms $L \otimes_K M \cong B \otimes_A M$ sending $b \otimes m$ to $b \otimes m$, the $B$-linear one restricting to the $A$-linear one. Finally, $L$ is exhibited as the localisation of the $A$-module $B$ at the non-zero-divisors of $A$.
--
--   **Relation to Mathlib.** Built on Mathlib's `IsDedekindDomain.HeightOneSpectrum`, `Ideal.under`, `Ideal.primesOver`, the primed ramification index and inertia degree, and Mathlib's `Ideal.sum_ramification_inertia`, which is here transported to a sum indexed by the subtype `Extension B v`.
--
--   **Where it is used.** This is groundwork for the valuation-theoretic and adelic parts of the formalisation: it supplies the set of places of $B$ above a place of $A$, their finiteness, the relation between the associated valuations, and the identification of $L$-linear data with $B$-linear data by base change along $A \to B$.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/DedekindDomain/IntegralClosure.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Andrew Yang, Matthew Jasper). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_DedekindDomain_IntegralClosure.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Localization_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

namespace IsDedekindDomain.HeightOneSpectrum

section BaseChange

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [Algebra.IsIntegral A B] [IsDedekindDomain B]
    [IsFractionRing B L]

variable (v : HeightOneSpectrum A)

variable {A} in

def Extension (v : HeightOneSpectrum A) := {w : HeightOneSpectrum B // w.under A = v}

lemma mk_count_factors_map
    (hAB : Function.Injective (algebraMap A B))
    (w : HeightOneSpectrum B) (I : Ideal A) :
    (Associates.mk w.asIdeal).count (Associates.mk (Ideal.map (algebraMap A B) I)).factors =
    Ideal.ramificationIdx' (under A w).asIdeal w.asIdeal *
      (Associates.mk (under A w).asIdeal).count (Associates.mk I).factors := by
  classical
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    rw [Associates.mk_zero, Ideal.zero_eq_bot, Ideal.map_bot, ← Ideal.zero_eq_bot,
      Associates.mk_zero]
    simp [-under_asIdeal, Associates.count, Associates.factors_zero, w.associates_irreducible,
      associates_irreducible (under A w), Associates.bcount]
  | h₂ I hI =>
    obtain rfl : I = ⊤ := by simpa using hI
    simp only [Ideal.map_top]
    simp only [← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one]
    rw [Associates.count_zero (associates_irreducible _),
      Associates.count_zero (associates_irreducible _), mul_zero]
  | h₃ I p hI hp IH =>
    simp only [Ideal.map_mul, ← Associates.mk_mul_mk]
    have hp_bot : p ≠ ⊥ := hp.ne_zero
    have hp_bot' := (Ideal.map_eq_bot_iff_of_injective hAB).not.mpr hp_bot
    have hI_bot := (Ideal.map_eq_bot_iff_of_injective hAB).not.mpr hI
    rw [Associates.count_mul (Associates.mk_ne_zero.mpr hp_bot) (Associates.mk_ne_zero.mpr hI)
      (associates_irreducible _), Associates.count_mul (Associates.mk_ne_zero.mpr hp_bot')
      (Associates.mk_ne_zero.mpr hI_bot) (associates_irreducible _)]
    simp only [IH, mul_add]
    congr 1
    by_cases hw : (w.under A).asIdeal = p
    · have : Irreducible (Associates.mk p) := Associates.irreducible_mk.mpr hp.irreducible
      rw [hw, Associates.factors_self this, Associates.count_some this]
      simp only [Multiset.nodup_singleton, Multiset.mem_singleton, Multiset.count_eq_one_of_mem,
        mul_one]
      rw [count_associates_factors_eq hp_bot' w.2 w.3,
        Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hp_bot' w.2 w.3]
    · have : (Associates.mk (under A w).asIdeal).count (Associates.mk p).factors = 0 :=
        Associates.count_eq_zero_of_ne (associates_irreducible _)
          (Associates.irreducible_mk.mpr hp.irreducible)
          (by rwa [ne_eq, Associates.mk_eq_mk_iff_associated, associated_iff_eq])
      rw [this, mul_zero, eq_comm]
      by_contra H
      rw [eq_comm, ← ne_eq, Associates.count_ne_zero_iff_dvd hp_bot' (irreducible w),
        Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap] at H
      apply hw (((Ideal.isPrime_of_prime hp).isMaximal hp_bot).eq_of_le
        (under A w).2.ne_top H).symm

lemma ramificationIdx_ne_zero (hAB : Function.Injective (algebraMap A B))
    (w : HeightOneSpectrum B) :
    Ideal.ramificationIdx' (under A w).asIdeal w.asIdeal ≠ 0 :=
  Ideal.IsDedekindDomain.ramificationIdx'_ne_zero
    ((Ideal.map_eq_bot_iff_of_injective hAB).not.mpr (under A w).3) w.2 Ideal.map_comap_le

lemma intValuation_comap (hAB : Function.Injective (algebraMap A B))
    (w : HeightOneSpectrum B) (x : A) :
    (under A w).intValuation x ^
    (Ideal.ramificationIdx' (under A w).asIdeal w.asIdeal) =
    w.intValuation (algebraMap A B x) := by
  classical
  have h_ne_zero := ramificationIdx_ne_zero A B hAB w
  by_cases hx : x = 0
  · simpa [hx]
  simp only [intValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  change (ite _ _ _) ^ _ = ite _ _ _
  rw [map_eq_zero_iff _ hAB, if_neg hx, if_neg hx, ← Set.image_singleton, ← Ideal.map_span,
    mk_count_factors_map _ _ hAB, mul_comm, WithZero.exp, WithZero.exp]
  simp

omit [IsIntegralClosure B A L] in

lemma valuation_comap (w : HeightOneSpectrum B) (x : K) :
    (under A w).valuation K x ^
      (Ideal.ramificationIdx' (under A w).asIdeal w.asIdeal) =
    w.valuation L (algebraMap K L x) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  simp [valuation, ← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L,
    ← intValuation_comap A B (algebraMap_injective_of_field_isFractionRing A B K L), div_pow]

include K L in
omit [IsDedekindDomain A] [IsIntegralClosure B A L]
    [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L] in
lemma isTorsionFree [IsDomain B] : Module.IsTorsionFree A B := by
  have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  have : Nontrivial A := (IsFractionRing.nontrivial_iff_nontrivial A K).mpr inferInstance
  infer_instance

include K L in
omit [IsIntegralClosure B A L] [IsFractionRing B L] in

theorem Extension.finite (v : HeightOneSpectrum A) : Finite (v.Extension B) := by
  have := isTorsionFree A K L B
  rw [Extension, ← Set.coe_setOf]
  rw [@Set.finite_coe_iff]
  have := primesOver_finite v.asIdeal B
  refine Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal) ?_ ?_
  · refine Set.Finite.subset this ?_
    simp only [Set.subset_def, Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    rintro w rfl
    simp only [Ideal.primesOver, Set.mem_setOf_eq, isPrime, true_and]
    constructor
    simp [Ideal.under_def, under]
  · intro x hx y hy hxy
    rwa [← @HeightOneSpectrum.ext_iff] at hxy

@[reducible]
noncomputable def Extension.fintype : Fintype (Extension B v) :=
  have := Extension.finite A K L B v
  Fintype.ofFinite <| Extension B v

include K L in
omit [IsIntegralClosure B A L] [IsFractionRing B L] in
theorem preimage_comap_finite (S : Set (HeightOneSpectrum A)) (hS : S.Finite) :
    ((under A : HeightOneSpectrum B → HeightOneSpectrum A) ⁻¹' S).Finite := by
  rw [← Set.biUnion_preimage_singleton (under A) S]
  exact Set.Finite.biUnion' hS <| fun v _ ↦ Extension.finite A K L B v

noncomputable def preimageComapFinset (S : Finset (HeightOneSpectrum A)) :
    Finset (HeightOneSpectrum B) :=
  Set.Finite.toFinset <| preimage_comap_finite A K L B S S.finite_toSet

omit [IsIntegralClosure B A L] in

lemma _root_.Ideal.sum_ramification_inertia_extensions [Module.Finite A B] :
    letI := Extension.fintype A K L B v
    ∑ (w : Extension B v), Ideal.ramificationIdx' v.asIdeal w.val.asIdeal
      * (v.asIdeal).inertiaDeg' (w.val.asIdeal) = Module.finrank K L := by
  have := v.isMaximal
  have := isTorsionFree A K L B

  rw [← Ideal.sum_ramification_inertia B K L v.ne_bot]

  apply Finset.sum_nbij (fun w ↦ w.val.asIdeal)
  · rintro ⟨a, rfl⟩ -
    rw [← Finset.mem_coe, coe_primesOverFinset (under A a).ne_bot]
    exact ⟨a.isPrime, ⟨rfl⟩⟩
  · apply Function.Injective.injOn
    exact fun _ _ hw ↦ Subtype.ext <| HeightOneSpectrum.ext hw
  · intro y hy
    rw [coe_primesOverFinset v.ne_bot B] at hy
    obtain ⟨hprime, ⟨hyover⟩⟩ := hy
    have hybot : y ≠ ⊥ := by
      rw [Ideal.under_def] at hyover
      intro hbot
      apply v.ne_bot
      rw [hyover, hbot]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
    let w' : HeightOneSpectrum B := ⟨y, hprime, hybot⟩
    have wcomap : under A w' = v := HeightOneSpectrum.ext hyover.symm
    let w : Extension B v := ⟨w', wcomap⟩
    exact ⟨w, by simp, rfl⟩
  · exact fun _ _ ↦ rfl

end BaseChange

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain

open scoped TensorProduct

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [Algebra.IsAlgebraic K L]

noncomputable def LinearEquivTensorProduct :
    L ≃ₗ[K] K ⊗[A] B :=
  let f := LocalizedModule.equivTensorProduct (nonZeroDivisors A) B
  have := IsIntegralClosure.isLocalization A K L B
  have : IsLocalizedModule (nonZeroDivisors A) (IsScalarTower.toAlgHom A B L).toLinearMap :=
    inferInstance
  let g : LocalizedModule (nonZeroDivisors A) B ≃ₗ[A] L := @IsLocalizedModule.iso
      _ _ (nonZeroDivisors A) _ _ _ _ _ _ (IsScalarTower.toAlgHom A B L) this
  let h := TensorProduct.congr (Localization.algEquiv (nonZeroDivisors A) K) (LinearEquiv.refl A B)
  LinearEquiv.extendScalarsOfIsLocalization (nonZeroDivisors A) K
    <| g.symm.trans (f.restrictScalars A) |>.trans h

lemma LinearEquivTensorProduct_symm_one_tmul (b : B) :
    (LinearEquivTensorProduct A K L B).symm (1 ⊗ₜ b) =
    (algebraMap _ _ b) := by
  have : (SemilinearEquivClass.semilinearEquiv (Localization.algEquiv (nonZeroDivisors A) K)).symm
      1 = 1 :=
    map_one (Localization.algEquiv (nonZeroDivisors A) K).symm
  simp [LinearEquivTensorProduct, this]

lemma LinearEquivTensorProduct_symm_tmul (k : K) (b : B) :
    (LinearEquivTensorProduct A K L B).symm (k ⊗ₜ b) =
    k • (algebraMap _ _ b) := by
  have : k ⊗ₜ b = k • (1 ⊗ₜ b : K ⊗[A] B) := by
    simp [TensorProduct.smul_tmul']
  rw [this, LinearEquiv.map_smul, LinearEquivTensorProduct_symm_one_tmul]

variable (M : Type*) [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower A K M]

noncomputable def linearEquivTensorProductModule : L ⊗[K] M ≃ₗ[A] B ⊗[A] M :=
  let f₁ : L ⊗[K] M ≃ₗ[A] L ⊗[A] M := IsLocalization.moduleTensorEquiv (nonZeroDivisors A) K L M
    |>.restrictScalars A
  let f₂ : L ≃ₗ[A] B ⊗[A] K := LinearEquivTensorProduct A K L B
    |>.restrictScalars A
    |>.trans (TensorProduct.comm A K B)
  let f₃ : L ⊗[A] M ≃ₗ[A] (B ⊗[A] K) ⊗[A] M := TensorProduct.congr f₂ (LinearEquiv.refl A M)
  let f₄ : (B ⊗[A] K) ⊗[A] M ≃ₗ[A] B ⊗[A] (K ⊗[A] M) :=
    TensorProduct.assoc A B K M
  let f₅ : B ⊗[A] (K ⊗[A] M) ≃ₗ[A] B ⊗[A] M := TensorProduct.congr (LinearEquiv.refl A B)
    (IsLocalization.moduleLid (nonZeroDivisors A) K M |>.restrictScalars A)
  f₁.trans f₃ |>.trans f₄ |>.trans f₅

noncomputable def linearEquivTensorProductModuleLeft : L ⊗[K] M ≃ₗ[B] B ⊗[A] M :=
  let f₁ : L ⊗[K] M ≃ₗ[B] L ⊗[A] M :=
    IsLocalization.leftModuleTensorEquiv B (nonZeroDivisors A) K L M
  let f₂ : B ⊗[A] K ≃ₗ[B] L := {
    __ := LinearEquivTensorProduct A K L B
        |>.restrictScalars A
        |>.trans (TensorProduct.comm A K B) |>.symm
    map_smul' b x := by
      induction x with
      | zero => simp
      | tmul l m => simp [LinearEquivTensorProduct_symm_tmul, Algebra.smul_def]; ring
      | add => simp_all
    }
  let f₃ : (B ⊗[A] K) ⊗[A] M ≃ₗ[B] L ⊗[A] M :=
    TensorProduct.AlgebraTensorModule.congr f₂ (LinearEquiv.refl A M)
  let f₄ : (B ⊗[A] K) ⊗[A] M ≃ₗ[B] B ⊗[A] (K ⊗[A] M) :=
    TensorProduct.AlgebraTensorModule.assoc _ A B _ K M
  let f₅ : B ⊗[A] (K ⊗[A] M) ≃ₗ[B] B ⊗[A] M :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (IsLocalization.moduleLid (nonZeroDivisors A) K M |>.restrictScalars A)
  f₁.trans f₃.symm |>.trans f₄ |>.trans f₅

lemma linearEquivTensorProductModuleLeft_restrictScalars :
    (linearEquivTensorProductModuleLeft A K L B M).restrictScalars A =
      linearEquivTensorProductModule A K L B M := by
  rfl

lemma linearEquivTensorProductModule_symm_tmul (b : B) (m : M) :
    (linearEquivTensorProductModule A K L B M).symm (b ⊗ₜ m) = (algebraMap B L b) ⊗ₜ m := by
  simp [linearEquivTensorProductModule, LinearEquivTensorProduct_symm_one_tmul]

lemma linearEquivTensorProductModule_tmul (b : B) (m : M) :
    (linearEquivTensorProductModule A K L B M) ((algebraMap B L b) ⊗ₜ m) = b ⊗ₜ m := by
  rw [← LinearEquiv.eq_symm_apply, linearEquivTensorProductModule_symm_tmul]

lemma linearEquivTensorProductModuleLeft_symm_tmul (b : B) (m : M) :
    (linearEquivTensorProductModuleLeft A K L B M).symm (b ⊗ₜ m) = (algebraMap B L b) ⊗ₜ m := by
  simp [linearEquivTensorProductModuleLeft, LinearEquivTensorProduct_symm_one_tmul]

lemma linearEquivTensorProductModuleLeft_tmul (b : B) (m : M) :
    (linearEquivTensorProductModuleLeft A K L B M) ((algebraMap B L b) ⊗ₜ m) = b ⊗ₜ m := by
  rw [← LinearEquiv.eq_symm_apply, linearEquivTensorProductModuleLeft_symm_tmul]

end IsDedekindDomain

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [Algebra.IsAlgebraic K L]

include K in
lemma _root_.IsIntegralClosure.isLocalizedModule : IsLocalizedModule (nonZeroDivisors A)
    ((Algebra.linearMap B L).restrictScalars A) := by
  have hlocal := IsIntegralClosure.isLocalization A K L B
  rw [← isLocalizedModule_iff_isLocalization'] at hlocal
  exact {
    map_units x := by
      obtain ⟨x, hx⟩ := x
      have h := hlocal.map_units ⟨_, x, hx, rfl⟩
      rw [Module.End.isUnit_iff] at h ⊢
      convert h using 1
      ext l
      simp [Module.algebraMap_end_apply, algebraMap_smul]
    surj y := by
      obtain ⟨⟨b, _, s, hs, rfl⟩, hx⟩ := (hlocal.surj) y
      exact ⟨(b, ⟨s, hs⟩), by simpa [Submonoid.smul_def] using hx⟩
    exists_of_eq {x₁ x₂} e := by
      obtain ⟨⟨_, c, hc, rfl⟩, he⟩ := hlocal.exists_of_eq e
      use ⟨c, hc⟩
      simpa only [Submonoid.smul_def, smul_eq_mul, Algebra.smul_def] using he
  }


