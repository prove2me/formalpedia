-- Prove2me | solution 1 for AlgebraicGeometry.isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/050c1c93-6b4a-594a-a231-919d4e36b6e2

import Mathlib
import Theorems.Thm_Module_flat_of_maximalIdeal_rTensor_injective_of_isLocalHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocalRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TensorProduct

universe u

namespace E3bGlue

theorem epi_stalkMap_of_mono {M S : Scheme.{u}} (ϖ : M ⟶ S) [Mono ϖ] (x : M) : Epi (ϖ.stalkMap x) := by
  constructor
  intro T g₁ g₂ h
  have h1 : (Spec.map g₁ ≫ M.fromSpecStalk x) ≫ ϖ = (Spec.map g₂ ≫ M.fromSpecStalk x) ≫ ϖ := by
    simp only [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc, h]
  have h2 : Spec.map g₁ ≫ M.fromSpecStalk x = Spec.map g₂ ≫ M.fromSpecStalk x := (cancel_mono ϖ).mp h1
  exact Spec.map_injective ((cancel_mono (M.fromSpecStalk x)).mp h2)

theorem exists_stalkHom_of_apply_closedPoint_eq {M : Scheme.{u}} {T : CommRingCat.{u}} [IsLocalRing T]
    (g : Spec T ⟶ M) (x : M) (hx : g.base (closedPoint T) = x) :
    ∃ ψ : M.presheaf.stalk x ⟶ T, IsLocalHom ψ.hom ∧ Spec.map ψ ≫ M.fromSpecStalk x = g := by
  subst hx
  exact ⟨Scheme.stalkClosedPointTo g, inferInstance, Scheme.Spec_stalkClosedPointTo_fromSpecStalk g⟩

theorem specMap_comp_fromSpecStalk_closedPoint {M : Scheme.{u}} {T : CommRingCat.{u}} [IsLocalRing T] {x : M}
    (ψ : M.presheaf.stalk x ⟶ T) [IsLocalHom ψ.hom] :
    (Spec.map ψ ≫ M.fromSpecStalk x).base (closedPoint T) = x := by
  rw [Scheme.Hom.comp_base, TopCat.comp_app]
  have : (Spec.map ψ).base (closedPoint T) = closedPoint (M.presheaf.stalk x) := IsLocalRing.comap_closedPoint ψ.hom
  rw [this]
  exact Scheme.fromSpecStalk_closedPoint

section Quotients

variable (A : Type u) [CommRing A] [IsLocalRing A]

theorem maximalIdeal_pow_ne_top (n : ℕ) : maximalIdeal A ^ (n + 1) ≠ ⊤ := fun htop =>
  Ideal.IsPrime.ne_top' (I := maximalIdeal A) (top_le_iff.mp (htop ▸ Ideal.pow_le_self (Nat.succ_ne_zero n)))

scoped instance nontrivial_quot (n : ℕ) : Nontrivial (A ⧸ maximalIdeal A ^ (n + 1)) :=
  Ideal.Quotient.nontrivial_iff.mpr (maximalIdeal_pow_ne_top A n)

scoped instance isLocalRing_quot (n : ℕ) : IsLocalRing (A ⧸ maximalIdeal A ^ (n + 1)) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem eq_maximalIdeal_of_pow_le {n : ℕ} (hn : n ≠ 0) (P : Ideal A) [P.IsPrime] (h : maximalIdeal A ^ n ≤ P) :
    P = maximalIdeal A :=
  ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le Ideal.IsPrime.ne_top'
    ((Ideal.IsPrime.pow_le_iff hn).mp h)).symm

theorem isMaximal_map_maximalIdeal (n : ℕ) :
    ((maximalIdeal A).map (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)))).IsMaximal := by
  refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    (IsLocalRing.maximalIdeal.isMaximal A)).resolve_left fun htop => ?_
  have := congrArg (Ideal.comap (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)))) htop
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, Ideal.comap_top, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker, sup_of_le_left (Ideal.pow_le_self (Nat.succ_ne_zero n))] at this
  exact Ideal.IsPrime.ne_top' this

theorem isMaximal_of_isPrime_quot (n : ℕ) (P : Ideal (A ⧸ maximalIdeal A ^ (n + 1))) (hP : P.IsPrime) : P.IsMaximal := by
  have hc : P.comap (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))) = maximalIdeal A := by
    apply eq_maximalIdeal_of_pow_le A (Nat.succ_ne_zero n)
    intro a ha
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact Ideal.zero_mem _
  have hP' : P = (P.comap (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)))).map (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))) :=
    (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P).symm
  rw [hc] at hP'
  rw [hP']
  exact isMaximal_map_maximalIdeal A n

scoped instance isArtinianRing_quot [IsNoetherianRing A] (n : ℕ) : IsArtinianRing (A ⧸ maximalIdeal A ^ (n + 1)) := by
  rw [isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_zero_iff]
  exact fun P hP => isMaximal_of_isPrime_quot A n P hP

theorem maximalIdeal_quot (n : ℕ) :
    maximalIdeal (A ⧸ maximalIdeal A ^ (n + 1)) = (maximalIdeal A).map (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))) :=
  (IsLocalRing.eq_maximalIdeal (isMaximal_map_maximalIdeal A n)).symm

private theorem _root_.E3bGlue.factor_surjective (n : ℕ) :
    Function.Surjective (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : maximalIdeal A ^ (n + 1 + 1) ≤ maximalIdeal A ^ (n + 1))) :=
  Ideal.Quotient.factor_surjective _

p2m_export "E3bGlue" "factor_surjective"
theorem ker_factor (n : ℕ) :
    RingHom.ker (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : maximalIdeal A ^ (n + 1 + 1) ≤ maximalIdeal A ^ (n + 1))) =
      (maximalIdeal A ^ (n + 1)).map (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1 + 1))) := by
  ext y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
  constructor
  · exact fun h => ⟨a, h, rfl⟩
  · rintro ⟨b, hb, hab⟩
    rw [Ideal.Quotient.eq] at hab
    have : a = b - (b - a) := by ring
    rw [this]
    exact Ideal.sub_mem _ hb (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) hab)

theorem ker_factor_mul_maximalIdeal (n : ℕ) :
    RingHom.ker (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : maximalIdeal A ^ (n + 1 + 1) ≤ maximalIdeal A ^ (n + 1))) *
      maximalIdeal (A ⧸ maximalIdeal A ^ (n + 1 + 1)) = ⊥ := by
  rw [ker_factor, maximalIdeal_quot A (n + 1), ← Ideal.map_mul, ← pow_succ, Ideal.map_quotient_self]

end Quotients

end E3bGlue
p2m_reactivate "P2MW.S_AlgebraicGeometry_isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocalRing.E3bGlue"

namespace E3bGlue

theorem exists_retraction_succ {R : Type u} [CommRing R] {M : Scheme.{u}} (ϖ : M ⟶ Spec (CommRingCat.of R)) [Mono ϖ]
    (h : ∀ (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
      [CommRing T] [Nontrivial T] (p : T' →+* T), Function.Surjective p → RingHom.ker p * maximalIdeal T' = ⊥ →
      ∀ (s : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of R)) (m : Spec (CommRingCat.of T) ⟶ M),
        m ≫ ϖ = Spec.map (CommRingCat.ofHom p) ≫ s →
        ∃ m' : Spec (CommRingCat.of T') ⟶ M, m' ≫ ϖ = s ∧ Spec.map (CommRingCat.ofHom p) ≫ m' = m)
    (x : M) (n : ℕ) [IsNoetherianRing ((Spec (CommRingCat.of R)).presheaf.stalk (ϖ.base x))]
    (ψ : M.presheaf.stalk x ⟶ CommRingCat.of (↑((Spec (CommRingCat.of R)).presheaf.stalk (ϖ.base x)) ⧸ maximalIdeal ↑((Spec (CommRingCat.of R)).presheaf.stalk (ϖ.base x)) ^ (n + 1))) [IsLocalHom ψ.hom]
    (hψ : ϖ.stalkMap x ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal ↑((Spec (CommRingCat.of R)).presheaf.stalk (ϖ.base x)) ^ (n + 1)))) :
    ∃ ψ' : M.presheaf.stalk x ⟶ CommRingCat.of (↑((Spec (CommRingCat.of R)).presheaf.stalk (ϖ.base x)) ⧸ maximalIdeal ↑((Spec (CommRingCat.of R)).presheaf.stalk (ϖ.base x)) ^ (n + 1 + 1)),
      IsLocalHom ψ'.hom ∧ ϖ.stalkMap x ≫ ψ' = CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal ↑((Spec (CommRingCat.of R)).presheaf.stalk (ϖ.base x)) ^ (n + 1 + 1))) := by

  set A : CommRingCat.{u} := ((Spec (CommRingCat.of R)).presheaf.stalk (ϖ.base x)) with hA
  let q : ∀ k : ℕ, ↑A →+* ↑A ⧸ maximalIdeal ↑A ^ k := fun k => Ideal.Quotient.mk _
  let p : ↑A ⧸ maximalIdeal ↑A ^ (n + 1 + 1) →+* ↑A ⧸ maximalIdeal ↑A ^ (n + 1) :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : maximalIdeal ↑A ^ (n + 1 + 1) ≤ maximalIdeal ↑A ^ (n + 1))
  have hpq : p.comp (q (n + 1 + 1)) = q (n + 1) := Ideal.Quotient.factor_comp_mk _
  haveI : IsLocalHom p := IsLocalHom.of_surjective p (factor_surjective (↑A) n)

  let ι : CommRingCat.of R ⟶ A := StructureSheaf.toStalk R (ϖ.base x)
  have hfrom : (Spec (CommRingCat.of R)).fromSpecStalk (ϖ.base x) = Spec.map ι := Spec.fromSpecStalk_eq' _ _

  let s : Spec (CommRingCat.of (↑A ⧸ maximalIdeal ↑A ^ (n + 1 + 1))) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (ι ≫ CommRingCat.ofHom (q (n + 1 + 1)))
  let m : Spec (CommRingCat.of (↑A ⧸ maximalIdeal ↑A ^ (n + 1))) ⟶ M := Spec.map ψ ≫ M.fromSpecStalk x
  have hsq : m ≫ ϖ = Spec.map (CommRingCat.ofHom p) ≫ s := by
    simp only [m, s, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, hfrom, ← Spec.map_comp, hψ]
    congr 1
  obtain ⟨m', hm'1, hm'2⟩ := h _ _ p (factor_surjective (↑A) n) (ker_factor_mul_maximalIdeal (↑A) n) s m hsq

  have hcl : m'.base (closedPoint (↑A ⧸ maximalIdeal ↑A ^ (n + 1 + 1))) = x := by
    have h1 : (Spec.map (CommRingCat.ofHom p)).base (closedPoint (↑A ⧸ maximalIdeal ↑A ^ (n + 1))) =
        closedPoint (↑A ⧸ maximalIdeal ↑A ^ (n + 1 + 1)) := IsLocalRing.comap_closedPoint p
    rw [← h1, ← TopCat.comp_app, ← Scheme.Hom.comp_base, hm'2]
    exact specMap_comp_fromSpecStalk_closedPoint ψ
  obtain ⟨ψ', hloc, hψ'⟩ := exists_stalkHom_of_apply_closedPoint_eq m' x hcl
  refine ⟨ψ', hloc, ?_⟩

  have key : ι ≫ (ϖ.stalkMap x ≫ ψ') = ι ≫ CommRingCat.ofHom (q (n + 1 + 1)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, ← hfrom, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, hψ',
      hm'1]

  letI : Algebra R ↑A := (ι.hom).toAlgebra
  haveI : IsLocalization.AtPrime (↑A) (ϖ.base x).asIdeal := StructureSheaf.IsLocalization.to_stalk R (ϖ.base x)
  have := IsLocalization.ringHom_ext (S := ↑A) ((ϖ.base x).asIdeal.primeCompl)
    (j := (ϖ.stalkMap x ≫ ψ').hom) (k := (CommRingCat.ofHom (q (n + 1 + 1))).hom)
    (congrArg CommRingCat.Hom.hom key)
  exact CommRingCat.hom_ext this

end E3bGlue
p2m_reactivate "P2MW.S_AlgebraicGeometry_isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocalRing.E3bGlue"

namespace E3bGlue

theorem isNoetherianRing_stalk {R : Type u} [CommRing R] [IsNoetherianRing R] (p : ↥(Spec (CommRingCat.of R))) :
    IsNoetherianRing ((Spec (CommRingCat.of R)).presheaf.stalk p) := by
  letI : Algebra R ↑((Spec (CommRingCat.of R)).presheaf.stalk p) := (StructureSheaf.toStalk R p).hom.toAlgebra
  haveI : IsLocalization.AtPrime (↑((Spec (CommRingCat.of R)).presheaf.stalk p)) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R p
  exact IsLocalization.isNoetherianRing p.asIdeal.primeCompl _ inferInstance

end E3bGlue
p2m_reactivate "P2MW.S_AlgebraicGeometry_isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocalRing.E3bGlue"

namespace E3bMono

section separated

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B]
  [IsLocalHom (algebraMap A B)]

theorem maximalIdeal_pow_smul_top_le_restrictScalars (P : Type*) [AddCommGroup P] [Module A P]
    [Module B P] [IsScalarTower A B P] (k : ℕ) :
    ((maximalIdeal A) ^ k • ⊤ : Submodule A P) ≤
      ((maximalIdeal B) ^ k • ⊤ : Submodule B P).restrictScalars A := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Submodule.mul_smul]
    refine Submodule.smul_le.mpr fun a ha x hx => ?_
    have hx' := ih hx
    rw [Submodule.restrictScalars_mem] at hx' ⊢
    rw [← algebraMap_smul B a x, pow_succ', Submodule.mul_smul]
    exact Submodule.smul_mem_smul (map_nonunit (algebraMap A B) a ha) hx'

variable [IsNoetherianRing B]

theorem iInf_maximalIdeal_pow_smul_eq_bot_of_isLocalHom (P : Type*) [AddCommGroup P]
    [Module A P] [Module B P] [IsScalarTower A B P] [Module.Finite B P] :
    (⨅ k : ℕ, (maximalIdeal A) ^ k • ⊤ : Submodule A P) = ⊥ := by
  have hB := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := P) (maximalIdeal B)
    (maximalIdeal.isMaximal B).ne_top
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ (⨅ k : ℕ, (maximalIdeal B) ^ k • ⊤ : Submodule B P) := by
    rw [Submodule.mem_iInf] at hx ⊢
    intro k
    exact (Submodule.restrictScalars_mem A ((maximalIdeal B) ^ k • ⊤ : Submodule B P) x).mp
      (maximalIdeal_pow_smul_top_le_restrictScalars P k (hx k))
  rw [hB] at hx'
  simpa using hx'

end separated
p2m_reactivate "P2MW.S_AlgebraicGeometry_isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocalRing.E3bGlue"

theorem finite_lTensor {A : Type u} (B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (M : Type u) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M] (P : Type u) [AddCommGroup P] [Module A P] [Module.Finite A P] :
    Module.Finite B (M ⊗[A] P) :=
  Module.Finite.equiv (AlgebraTensorModule.cancelBaseChange A B B M P)

theorem iInf_maximalIdeal_pow_smul_tensor_eq_bot {A : Type u} (B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
    (M : Type u) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M] (P : Type u) [AddCommGroup P] [Module A P] [Module.Finite A P] :
    (⨅ k : ℕ, (maximalIdeal A) ^ k • ⊤ : Submodule A (M ⊗[A] P)) = ⊥ :=
  haveI := finite_lTensor (A := A) B M P
  iInf_maximalIdeal_pow_smul_eq_bot_of_isLocalHom (B := B) (M ⊗[A] P)

section core

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

lemma map_mem_smul_top {P Q : Type*} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (g : P →ₗ[A] Q) {I : Ideal A} {p : P} (hp : p ∈ (I • ⊤ : Submodule A P)) :
    g p ∈ (I • ⊤ : Submodule A Q) := by
  have := Submodule.mem_map_of_mem (f := g) hp
  rw [Submodule.map_smul''] at this
  exact Submodule.smul_mono le_rfl le_top this

lemma mem_pow_smul_top_of_coe_mem (I : Ideal A) (k : ℕ) (m : I) (hm : (m : A) ∈ I ^ k * I) :
    m ∈ (I ^ k • ⊤ : Submodule A I) := by
  have h' : (m : A) ∈ Submodule.map I.subtype (I ^ k • ⊤ : Submodule A I) := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top, Ideal.smul_eq_mul]
    exact hm
  obtain ⟨m', hm', heq⟩ := h'
  have : m' = m := Subtype.ext heq
  exact this ▸ hm'

variable [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
  [IsLocalHom (algebraMap A B)]

theorem lTensor_maximalIdeal_subtype_injective
    (hI : ∀ k : ℕ, ∀ b : B, ∃ a : A,
      b - algebraMap A B a ∈ (maximalIdeal A ^ k • ⊤ : Submodule A B))
    (hII : ∀ k : ℕ, ∀ a : A,
      algebraMap A B a ∈ (maximalIdeal A ^ k • ⊤ : Submodule A B) → a ∈ maximalIdeal A ^ k) :
    Function.Injective (LinearMap.lTensor B (maximalIdeal A).subtype) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  let μ : B ⊗[A] maximalIdeal A →ₗ[A] B :=
    (TensorProduct.rid A B).toLinearMap ∘ₗ LinearMap.lTensor B (maximalIdeal A).subtype
  have hμ : ∀ (b : B) (m : maximalIdeal A), μ (b ⊗ₜ m) = (m : A) • b := fun b m => by
    simp [μ]
  have hx0 : μ x = 0 := by
    simp only [μ, LinearMap.coe_comp, Function.comp_apply, LinearMap.mem_ker.mp hx, map_zero]
  suffices hall : ∀ k : ℕ, x ∈ (maximalIdeal A ^ k • ⊤ : Submodule A (B ⊗[A] maximalIdeal A)) by
    have hmem : x ∈ (⨅ k : ℕ, (maximalIdeal A) ^ k • ⊤ : Submodule A (B ⊗[A] maximalIdeal A)) :=
      (Submodule.mem_iInf _).mpr hall
    rwa [iInf_maximalIdeal_pow_smul_tensor_eq_bot B B (maximalIdeal A)] at hmem
  intro k

  have claim1 : ∀ y : B ⊗[A] maximalIdeal A, ∃ m : maximalIdeal A,
      y - (1 : B) ⊗ₜ m ∈ (maximalIdeal A ^ (k + 1) • ⊤ : Submodule A (B ⊗[A] maximalIdeal A)) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul b m =>
      obtain ⟨a, ha⟩ := hI (k + 1) b
      refine ⟨a • m, ?_⟩
      have : b ⊗ₜ[A] m - (1 : B) ⊗ₜ[A] (a • m) = (b - algebraMap A B a) ⊗ₜ[A] m := by
        rw [TensorProduct.sub_tmul, tmul_smul, smul_tmul', Algebra.smul_def, mul_one]
      rw [this]
      exact map_mem_smul_top ((TensorProduct.mk A B (maximalIdeal A)).flip m) ha
    | add y z hy hz =>
      obtain ⟨m₁, h₁⟩ := hy
      obtain ⟨m₂, h₂⟩ := hz
      refine ⟨m₁ + m₂, ?_⟩
      have : y + z - (1 : B) ⊗ₜ[A] (m₁ + m₂) = (y - (1 : B) ⊗ₜ m₁) + (z - (1 : B) ⊗ₜ m₂) := by
        rw [tmul_add]; abel
      rw [this]
      exact Submodule.add_mem _ h₁ h₂
  obtain ⟨m, hm⟩ := claim1 x

  have h1m : μ ((1 : B) ⊗ₜ m) ∈ (maximalIdeal A ^ (k + 1) • ⊤ : Submodule A B) := by
    have : μ ((1 : B) ⊗ₜ m) = μ x - μ (x - (1 : B) ⊗ₜ m) := by rw [map_sub]; abel
    rw [this, hx0, zero_sub]
    exact Submodule.neg_mem _ (map_mem_smul_top μ hm)
  rw [hμ, ← Algebra.algebraMap_eq_smul_one] at h1m
  have hmk : (m : A) ∈ maximalIdeal A ^ (k + 1) := hII (k + 1) m h1m
  have h1mem : (1 : B) ⊗ₜ[A] m ∈
      (maximalIdeal A ^ k • ⊤ : Submodule A (B ⊗[A] maximalIdeal A)) := by
    have hm' : m ∈ (maximalIdeal A ^ k • ⊤ : Submodule A (maximalIdeal A)) :=
      mem_pow_smul_top_of_coe_mem (maximalIdeal A) k m (by rw [← pow_succ]; exact hmk)
    exact map_mem_smul_top (TensorProduct.mk A B (maximalIdeal A) 1) hm'
  have hsplit : x = (x - (1 : B) ⊗ₜ m) + (1 : B) ⊗ₜ m := by abel
  rw [hsplit]
  refine Submodule.add_mem _ ?_ h1mem
  exact Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_succ k)) le_rfl hm

theorem flat_of_approx
    (hI : ∀ k : ℕ, ∀ b : B, ∃ a : A,
      b - algebraMap A B a ∈ (maximalIdeal A ^ k • ⊤ : Submodule A B))
    (hII : ∀ k : ℕ, ∀ a : A,
      algebraMap A B a ∈ (maximalIdeal A ^ k • ⊤ : Submodule A B) → a ∈ maximalIdeal A ^ k) :
    Module.Flat A B :=
  Module.flat_of_maximalIdeal_rTensor_injective_of_isLocalHom (A := A) (B := B) B
    ((LinearMap.lTensor_inj_iff_rTensor_inj B _).mp (lTensor_maximalIdeal_subtype_injective hI hII))

end core
p2m_reactivate "P2MW.S_AlgebraicGeometry_isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocalRing.E3bGlue"

section retraction

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

theorem approx_of_isEpi_of_retraction [Algebra.IsEpi A B] (I : Ideal A)
    (ψ : B →+* A ⧸ I) (hψ : ψ.comp (algebraMap A B) = Ideal.Quotient.mk I) :
    (∀ b : B, ∃ a : A, b - algebraMap A B a ∈ (I • ⊤ : Submodule A B)) ∧
    (∀ a : A, algebraMap A B a ∈ (I • ⊤ : Submodule A B) → a ∈ I) := by
  set J : Ideal B := I.map (algebraMap A B) with hJ
  have hIJ : ∀ b : B, b ∈ (I • ⊤ : Submodule A B) ↔ b ∈ J := fun b => by
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
  have hψa : ∀ a : A, ψ (algebraMap A B a) = Ideal.Quotient.mk I a := fun a =>
    RingHom.congr_fun hψ a
  have hJψ : ∀ b ∈ J, ψ b = 0 := by
    have : J ≤ RingHom.ker ψ := by
      rw [hJ, Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker, hψa, Ideal.Quotient.eq_zero_iff_mem]
      exact ha
    exact fun b hb => this hb
  constructor
  · intro b
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (ψ b)
    refine ⟨a, ?_⟩
    rw [hIJ]
    refine (Ideal.Quotient.eq (I := J)).mp ?_
    let ι : A ⧸ I →+* B ⧸ J := Ideal.quotientMap J (algebraMap A B) Ideal.le_comap_map
    let g₁ : B →ₐ[A] B ⧸ J := Ideal.Quotient.mkₐ A J
    let g₂ : B →ₐ[A] B ⧸ J :=
      { toRingHom := ι.comp ψ
        commutes' := fun r => by
          change ι (ψ (algebraMap A B r)) = algebraMap A (B ⧸ J) r
          rw [hψa]
          simp only [ι, Ideal.quotientMap_mk, Ideal.Quotient.mk_algebraMap] }
    have key : (1 : B) ⊗ₜ[A] b = b ⊗ₜ[A] 1 :=
      (Algebra.isEpi_iff_forall_one_tmul_eq A B).mp inferInstance b
    have hlift := congrArg (Algebra.TensorProduct.lift g₁ g₂ (fun _ _ => .all _ _)) key
    simp only [Algebra.TensorProduct.lift_tmul, map_one, one_mul, mul_one] at hlift

    have h2 : g₂ b = ι (ψ b) := rfl
    have h1 : g₁ b = Ideal.Quotient.mk J b := rfl
    rw [h1, h2, ← ha] at hlift
    rw [← hlift]
    exact (Ideal.quotientMap_mk (J := I) (I := J) (f := algebraMap A B)
      (H := Ideal.le_comap_map) (x := a)).symm
  · intro a ha
    rw [hIJ] at ha
    have := hJψ _ ha
    rwa [hψa, Ideal.Quotient.eq_zero_iff_mem] at this

end retraction
p2m_reactivate "P2MW.S_AlgebraicGeometry_isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocalRing.E3bGlue"

section fieldEpi

theorem surjective_algebraMap_of_isEpi_of_field (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.IsEpi K L] : Function.Surjective (algebraMap K L) := by
  intro a
  have key : (1 : L) ⊗ₜ[K] a = a ⊗ₜ[K] 1 :=
    (Algebra.isEpi_iff_forall_one_tmul_eq K L).mp inferInstance a
  let W : Submodule K L := Submodule.span K {(1 : L)}
  have h1 : W.mkQ 1 = 0 :=
    (Submodule.Quotient.mk_eq_zero W).mpr (Submodule.mem_span_singleton_self _)
  have h3 : (1 : L) ⊗ₜ[K] W.mkQ a = 0 := by
    have e1 : LinearMap.lTensor L W.mkQ ((1 : L) ⊗ₜ[K] a) = (1 : L) ⊗ₜ[K] W.mkQ a :=
      LinearMap.lTensor_tmul _ _ _ _
    have e2 : LinearMap.lTensor L W.mkQ (a ⊗ₜ[K] (1 : L)) = 0 := by
      rw [LinearMap.lTensor_tmul, h1, tmul_zero]
    rw [← e1, key, e2]
  have hinj : Function.Injective (LinearMap.rTensor (L ⧸ W) (Algebra.linearMap K L)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap K L).injective
  have h5 : (1 : K) ⊗ₜ[K] W.mkQ a = 0 := by
    apply hinj
    rw [LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one, map_zero]
    exact h3
  have h6 : W.mkQ a = 0 := by
    have := congrArg (TensorProduct.lid K (L ⧸ W)) h5
    rwa [TensorProduct.lid_tmul, one_smul, map_zero] at this
  have h7 : a ∈ W := (Submodule.Quotient.mk_eq_zero W).mp h6
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h7
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one, hc]⟩

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B]
  [IsLocalHom (algebraMap A B)]

theorem residueField_algebraMap_bijective_of_isEpi [Algebra.IsEpi A B] :
    Function.Bijective (algebraMap (ResidueField A) (ResidueField B)) := by
  refine ⟨(algebraMap (ResidueField A) (ResidueField B)).injective, ?_⟩

  have hAB : Epi (CommRingCat.ofHom (algebraMap A B)) := CommRingCat.epi_iff_epi.mpr inferInstance
  have hresB : Epi (CommRingCat.ofHom (residue B)) :=
    ConcreteCategory.epi_of_surjective _ residue_surjective
  have hcomp : CommRingCat.ofHom (algebraMap A B) ≫ CommRingCat.ofHom (residue B) =
      CommRingCat.ofHom (residue A) ≫
        CommRingCat.ofHom (algebraMap (ResidueField A) (ResidueField B)) := by
    ext a
    rfl
  have hepi : Epi (CommRingCat.ofHom (residue A) ≫
      CommRingCat.ofHom (algebraMap (ResidueField A) (ResidueField B))) := by
    rw [← hcomp]
    exact epi_comp _ _
  have : Epi (CommRingCat.ofHom (algebraMap (ResidueField A) (ResidueField B))) :=
    epi_of_epi (CommRingCat.ofHom (residue A)) _
  haveI : Algebra.IsEpi (ResidueField A) (ResidueField B) := CommRingCat.epi_iff_epi.mp this
  exact surjective_algebraMap_of_isEpi_of_field (ResidueField A) (ResidueField B)

theorem exists_retraction_one [Algebra.IsEpi A B] :
    ∃ ψ : B →+* A ⧸ maximalIdeal A ^ 1,
      IsLocalHom ψ ∧ ψ.comp (algebraMap A B) = Ideal.Quotient.mk _ := by
  let e : ResidueField A ≃+* ResidueField B :=
    RingEquiv.ofBijective _ residueField_algebraMap_bijective_of_isEpi
  let q : ResidueField A ≃+* A ⧸ maximalIdeal A ^ 1 :=
    Ideal.quotEquivOfEq (pow_one (maximalIdeal A)).symm
  let ψ : B →+* A ⧸ maximalIdeal A ^ 1 :=
    q.toRingHom.comp (e.symm.toRingHom.comp (residue B))
  have hψa : ∀ a : A, ψ (algebraMap A B a) = Ideal.Quotient.mk _ a := fun a => by
    simp only [ψ, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom]
    have : e.symm (residue B (algebraMap A B a)) = residue A a := by
      apply e.injective
      rw [RingEquiv.apply_symm_apply]
      rfl
    rw [this]
    rfl
  haveI : Nontrivial (A ⧸ maximalIdeal A ^ 1) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rw [pow_one]; exact (maximalIdeal.isMaximal A).ne_top)
  refine ⟨ψ, ⟨fun b hb => ?_⟩, RingHom.ext hψa⟩
  by_contra hnu
  have hb0 : residue B b = 0 := (residue_eq_zero_iff b).mpr ((mem_maximalIdeal b).mpr hnu)
  have : ψ b = 0 := by
    simp only [ψ, RingHom.coe_comp, Function.comp_apply, hb0, map_zero]
  rw [this] at hb
  exact not_isUnit_zero hb

end fieldEpi
p2m_reactivate "P2MW.S_AlgebraicGeometry_isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocalRing.E3bGlue"

section assembly

theorem flat_stalkMap {R : Type u} [CommRing R] [IsNoetherianRing R] {M : Scheme.{u}}
    (ϖ : M ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation ϖ] [Mono ϖ]
    (h : ∀ (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
      [CommRing T] [Nontrivial T] (p : T' →+* T), Function.Surjective p →
      RingHom.ker p * maximalIdeal T' = ⊥ →
      ∀ (s : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of R)) (m : Spec (CommRingCat.of T) ⟶ M),
        m ≫ ϖ = Spec.map (CommRingCat.ofHom p) ≫ s →
        ∃ m' : Spec (CommRingCat.of T') ⟶ M, m' ≫ ϖ = s ∧ Spec.map (CommRingCat.ofHom p) ≫ m' = m)
    (x : M) : (ϖ.stalkMap x).hom.Flat := by
  set A : CommRingCat.{u} := (Spec (CommRingCat.of R)).presheaf.stalk (ϖ.base x) with hA
  set B : CommRingCat.{u} := M.presheaf.stalk x with hB
  haveI : IsLocallyNoetherian M := LocallyOfFiniteType.isLocallyNoetherian ϖ
  haveI : IsNoetherianRing B := inferInstance
  haveI : IsNoetherianRing A := inferInstance
  letI : Algebra A B := (ϖ.stalkMap x).hom.toAlgebra
  haveI : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom (ϖ.stalkMap x).hom)
  haveI : Algebra.IsEpi A B :=
    CommRingCat.epi_iff_epi.mp (E3bGlue.epi_stalkMap_of_mono ϖ x)

  have tower : ∀ n : ℕ, ∃ ψ : (B : Type u) →+* (A ⧸ maximalIdeal A ^ (n + 1)),
      IsLocalHom ψ ∧ ψ.comp (algebraMap A B) = Ideal.Quotient.mk _ := by
    intro n
    induction n with
    | zero => exact exists_retraction_one
    | succ n ih =>
      obtain ⟨ψ, hψl, hψ⟩ := ih
      haveI : IsLocalHom (CommRingCat.ofHom ψ).hom := hψl
      obtain ⟨ψ', hψ'l, hψ'⟩ := E3bGlue.exists_retraction_succ ϖ h x n (CommRingCat.ofHom ψ)
        (by ext b; exact RingHom.congr_fun hψ b)
      exact ⟨ψ'.hom, hψ'l, by ext a; exact congrArg (fun φ => φ.hom a) hψ'⟩
  have happrox : ∀ k : ℕ,
      (∀ b : B, ∃ a : A, b - algebraMap A B a ∈ (maximalIdeal A ^ k • ⊤ : Submodule A B)) ∧
      (∀ a : A, algebraMap A B a ∈ (maximalIdeal A ^ k • ⊤ : Submodule A B) →
        a ∈ maximalIdeal A ^ k) := by
    intro k
    cases k with
    | zero =>
      refine ⟨fun b => ⟨0, ?_⟩, fun a _ => ?_⟩
      · rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
        exact Submodule.mem_top
      · rw [pow_zero, Ideal.one_eq_top]
        exact Submodule.mem_top
    | succ k =>
      obtain ⟨ψ, -, hψ⟩ := tower k
      exact approx_of_isEpi_of_retraction (maximalIdeal A ^ (k + 1)) ψ hψ
  exact flat_of_approx (fun k => (happrox k).1) (fun k => (happrox k).2)

end assembly
p2m_reactivate "P2MW.S_AlgebraicGeometry_isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocalRing.E3bGlue"

end E3bMono
p2m_reactivate "P2MW.S_AlgebraicGeometry_isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocalRing.E3bGlue"

open E3bMono in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] {M : Scheme.{u}} (ϖ : M ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation ϖ] [Mono ϖ]
    (h : ∀ (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
      [CommRing T] [Nontrivial T] (p : T' →+* T), Function.Surjective p → RingHom.ker p * maximalIdeal T' = ⊥ →
      ∀ (s : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of R)) (m : Spec (CommRingCat.of T) ⟶ M),
        m ≫ ϖ = Spec.map (CommRingCat.ofHom p) ≫ s →
        ∃ m' : Spec (CommRingCat.of T') ⟶ M, m' ≫ ϖ = s ∧ Spec.map (CommRingCat.ofHom p) ≫ m' = m) :
    IsOpenImmersion ϖ := by
  haveI : Flat ϖ := Flat.of_stalkMap ϖ fun x => flat_stalkMap ϖ h x
  exact IsOpenImmersion.of_flat_of_mono ϖ

end S_AlgebraicGeometry_isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocalRing
end P2MW
export P2MW.S_AlgebraicGeometry_isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocalRing (solution)
