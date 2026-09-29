-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_idealSheafData_tensor_linearEquiv_of_presentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/55a8a78c-42ae-506c-baee-dd7a0da0fb1b

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation

set_option autoImplicit false

open TensorProduct

universe u

noncomputable section

namespace P2mDenomAlg

section Denom

variable {A K : Type*} [CommRing A] [CommRing K] [Algebra A K]
variable {P : Type*} [AddCommGroup P] [Module A P] (φ : P →ₗ[A] K)

def intLocus (a : A) : Submodule A P where
  carrier := {p | IsLocalization.IsInteger A (algebraMap A K a * φ p)}
  zero_mem' := by
    show IsLocalization.IsInteger A (algebraMap A K a * φ 0)
    rw [map_zero, mul_zero]; exact IsLocalization.isInteger_zero
  add_mem' {p q} hp hq := by
    show IsLocalization.IsInteger A (algebraMap A K a * φ (p + q))
    rw [map_add, mul_add]; exact IsLocalization.isInteger_add hp hq
  smul_mem' c {p} hp := by
    show IsLocalization.IsInteger A (algebraMap A K a * φ (c • p))
    rw [LinearMap.map_smul, mul_smul_comm]; exact IsLocalization.isInteger_smul hp

def denom : Ideal A where
  carrier := {a | ∀ p, IsLocalization.IsInteger A (algebraMap A K a * φ p)}
  zero_mem' p := by
    rw [map_zero, zero_mul]; exact IsLocalization.isInteger_zero
  add_mem' {a b} ha hb p := by
    rw [map_add, add_mul]; exact IsLocalization.isInteger_add (ha p) (hb p)
  smul_mem' c {a} ha p := by
    rw [smul_eq_mul, map_mul, mul_assoc, ← Algebra.smul_def]
    exact IsLocalization.isInteger_smul (ha p)

theorem mem_denom {a : A} : a ∈ denom φ ↔ ∀ p, IsLocalization.IsInteger A (algebraMap A K a * φ p) :=
  Iff.rfl

theorem mem_denom_of_span {s : Set P} (hs : Submodule.span A s = ⊤) {a : A}
    (h : ∀ p ∈ s, IsLocalization.IsInteger A (algebraMap A K a * φ p)) : a ∈ denom φ := by
  intro p
  have hle : Submodule.span A s ≤ intLocus φ a := Submodule.span_le.mpr fun q hq => h q hq
  exact hle (hs ▸ Submodule.mem_top : p ∈ Submodule.span A s)

theorem exists_mem_denom (S : Submonoid A) [IsLocalization S K] [Module.Finite A P] :
    ∃ s ∈ S, s ∈ denom φ := by
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := A) (M := P)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples S t (fun p => φ p)
  refine ⟨b, b.2, mem_denom_of_span φ ht fun p hp => ?_⟩
  rw [← Algebra.smul_def]
  exact hb p hp

def mulMap : ↥(denom φ) ⊗[A] P →ₗ[A] K :=
  φ ∘ₗ (TensorProduct.lid A P).toLinearMap ∘ₗ ((denom φ).subtype.rTensor P)

theorem mulMap_tmul (a : denom φ) (p : P) : mulMap φ (a ⊗ₜ p) = algebraMap A K a * φ p := by
  simp [mulMap, Algebra.smul_def]

theorem mulMap_injective [Module.Flat A P] (hφ : Function.Injective φ) :
    Function.Injective (mulMap φ) :=
  hφ.comp ((TensorProduct.lid A P).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective))

theorem isInteger_mulMap (t : ↥(denom φ) ⊗[A] P) : IsLocalization.IsInteger A (mulMap φ t) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact IsLocalization.isInteger_zero
  | tmul a p => rw [mulMap_tmul]; exact a.2 p
  | add x y hx hy => rw [map_add]; exact IsLocalization.isInteger_add hx hy

theorem range_mulMap_le : LinearMap.range (mulMap φ) ≤ LinearMap.range (Algebra.linearMap A K) := by
  rintro _ ⟨t, rfl⟩
  obtain ⟨b, hb⟩ := isInteger_mulMap φ t
  exact ⟨b, hb⟩

def gens : Set K := {x | ∃ (a : A) (_ : a ∈ denom φ) (p : P), x = algebraMap A K a * φ p}

theorem range_mulMap_eq_span : LinearMap.range (mulMap φ) = Submodule.span A (gens φ) := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul a p => exact Submodule.subset_span ⟨a, a.2, p, mulMap_tmul φ a p⟩
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  · rw [Submodule.span_le]
    rintro _ ⟨a, ha, p, rfl⟩
    exact ⟨⟨a, ha⟩ ⊗ₜ p, mulMap_tmul φ ⟨a, ha⟩ p⟩

def numer : Ideal A := (LinearMap.range (mulMap φ)).comap (Algebra.linearMap A K)

theorem mem_numer {b : A} : b ∈ numer φ ↔ algebraMap A K b ∈ LinearMap.range (mulMap φ) := Iff.rfl

theorem map_numer_eq :
    Submodule.map (Algebra.linearMap A K) (numer φ) = LinearMap.range (mulMap φ) :=
  Submodule.map_comap_eq_self (range_mulMap_le φ)

def numerMap : ↥(numer φ) →ₗ[A] K := (Algebra.linearMap A K).domRestrict (numer φ)

theorem numerMap_injective (hinj : Function.Injective (algebraMap A K)) :
    Function.Injective (numerMap φ) := fun _ _ h => Subtype.ext (hinj h)

theorem range_mulMap_eq_range_numerMap :
    LinearMap.range (mulMap φ) = LinearMap.range (numerMap φ) := by
  rw [numerMap, LinearMap.range_domRestrict, map_numer_eq]

def equiv [Module.Flat A P] (hφ : Function.Injective φ)
    (hinj : Function.Injective (algebraMap A K)) : ↥(denom φ) ⊗[A] P ≃ₗ[A] ↥(numer φ) :=
  (LinearEquiv.ofInjective _ (mulMap_injective φ hφ)).trans
    ((LinearEquiv.ofEq _ _ (range_mulMap_eq_range_numerMap φ)).trans
      (LinearEquiv.ofInjective _ (numerMap_injective φ hinj)).symm)

theorem algebraMap_equiv [Module.Flat A P] (hφ : Function.Injective φ)
    (hinj : Function.Injective (algebraMap A K)) (t : ↥(denom φ) ⊗[A] P) :
    algebraMap A K (equiv φ hφ hinj t : A) = mulMap φ t :=
  LinearEquiv.ofInjective_symm_apply (numerMap φ) (h := numerMap_injective φ hinj)
    (LinearEquiv.ofEq _ _ (range_mulMap_eq_range_numerMap φ)
      (LinearEquiv.ofInjective _ (mulMap_injective φ hφ) t))

theorem numer_ne_bot [IsDomain K] (hinj : Function.Injective (algebraMap A K))
    {s : A} (hs : s ∈ denom φ) (hs0 : s ≠ 0) {p : P} (hp : φ p ≠ 0) : numer φ ≠ ⊥ := by
  obtain ⟨b, hb⟩ := hs p
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hb
    exact mul_ne_zero ((map_ne_zero_iff _ hinj).mpr hs0) hp hb.symm
  intro h
  have : b ∈ numer φ := ⟨⟨s, hs⟩ ⊗ₜ p, by rw [mulMap_tmul]; exact hb.symm⟩
  rw [h] at this
  exact hb0 ((Submodule.mem_bot A).mp this)

end Denom

section Loc

variable {A B K : Type*} [CommRing A] [CommRing B] [CommRing K]
variable [Algebra A B] [Algebra A K] [Algebra B K] [IsScalarTower A B K]
variable (f : A) [IsLocalization.Away f B]
variable {P Q : Type*} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module B Q]
variable (φP : P →ₗ[A] K) (φQ : Q →ₗ[B] K) (r : P →+ Q)
variable (hr : ∀ p, φQ (r p) = φP p)
variable (hsurj : ∀ q : Q, ∃ (n : ℕ) (p : P), r p = (algebraMap A B f ^ n) • q)

include hr hsurj in

theorem map_denom_le : (denom φP).map (algebraMap A B) ≤ denom φQ := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha q
  obtain ⟨n, p, hp⟩ := hsurj q
  obtain ⟨b, hb⟩ := ha p
  obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := B) f

  have h1 : φP p = algebraMap B K (algebraMap A B f ^ n) * φQ q := by
    rw [← hr, hp, LinearMap.map_smul, Algebra.smul_def]
  refine ⟨algebraMap A B b * ↑(u ^ n)⁻¹, ?_⟩
  show algebraMap B K (algebraMap A B b * ↑(u ^ n)⁻¹) = algebraMap B K (algebraMap A B a) * φQ q
  rw [map_mul, ← IsScalarTower.algebraMap_apply, hb, h1, IsScalarTower.algebraMap_apply A B K a,
    ← hu, ← Units.val_pow_eq_pow_val]

  have hu1 : algebraMap B K ↑(u ^ n) * algebraMap B K ↑(u ^ n)⁻¹ = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  calc algebraMap B K (algebraMap A B a) * (algebraMap B K ↑(u ^ n) * φQ q) * algebraMap B K ↑(u ^ n)⁻¹
      = algebraMap B K (algebraMap A B a) * φQ q *
          (algebraMap B K ↑(u ^ n) * algebraMap B K ↑(u ^ n)⁻¹) := by ring
    _ = algebraMap B K (algebraMap A B a) * φQ q := by rw [hu1, mul_one]

include f hr in

theorem denom_le_map [Module.Finite A P] : denom φQ ≤ (denom φP).map (algebraMap A B) := by
  intro b hb
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := A) (M := P)
  obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := B) f

  obtain ⟨m, a₀, ha₀⟩ := IsLocalization.Away.surj f b

  have hc : ∀ p : P, ∃ c : B, algebraMap B K c = algebraMap B K b * φQ (r p) := fun p => hb (r p)
  choose c hc using hc
  have hd : ∀ p : P, ∃ (n : ℕ) (d : A), c p * algebraMap A B f ^ n = algebraMap A B d := fun p =>
    IsLocalization.Away.surj f (c p)
  choose n d hd using hd
  classical
  set N : ℕ := t.sum n with hN
  have hnN : ∀ p ∈ t, n p ≤ N := fun p hp => Finset.single_le_sum (fun _ _ => Nat.zero_le _) hp

  have hmem : a₀ * f ^ N ∈ denom φP := by
    refine mem_denom_of_span φP ht fun p hp => ⟨f ^ m * f ^ (N - n p) * d p, ?_⟩
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hnN p hp)
    have hk' : N - n p = k := by omega
    rw [hk', IsScalarTower.algebraMap_apply A B K, IsScalarTower.algebraMap_apply A B K (a₀ * f ^ N),
      ← hr p]
    simp only [map_mul, map_pow, ← hd p, ← ha₀]
    rw [hk]
    simp only [hc p, pow_add]
    ring

  have hunit : (u ^ m * (u ^ N * (u ^ (m + N))⁻¹) : Bˣ) = 1 := by
    rw [← mul_assoc, ← pow_add, mul_inv_cancel]
  have hb' : b = algebraMap A B (a₀ * f ^ N) * ↑(u ^ (m + N))⁻¹ := by
    rw [map_mul, map_pow, ← ha₀, ← hu, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val]
    rw [mul_assoc, mul_assoc, ← Units.val_mul, ← Units.val_mul, hunit, Units.val_one, mul_one]
  rw [hb']
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hmem)

include hr hsurj in
theorem map_denom_eq [Module.Finite A P] : (denom φP).map (algebraMap A B) = denom φQ :=
  le_antisymm (map_denom_le f φP φQ r hr hsurj) (denom_le_map f φP φQ r hr)

theorem map_linearMap_map (I : Ideal A) :
    Submodule.map (Algebra.linearMap B K) (I.map (algebraMap A B)) =
      Submodule.span B (algebraMap A K '' I) := by
  change Submodule.map (Algebra.linearMap B K) (Submodule.span B (algebraMap A B '' I)) = _
  rw [Submodule.map_span, Set.image_image]
  congr 1
  refine Set.image_congr fun a _ => ?_
  simp [← IsScalarTower.algebraMap_apply]

include hr hsurj in

theorem range_mulMap_loc [Module.Finite A P] :
    LinearMap.range (mulMap φQ) = Submodule.span B (gens φP) := by
  obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := B) f
  apply le_antisymm
  · rw [range_mulMap_eq_span, Submodule.span_le]
    rintro _ ⟨b, hb, q, rfl⟩
    obtain ⟨k, p, hp⟩ := hsurj q

    have hq : φQ q = algebraMap B K ↑(u ^ k)⁻¹ * φP p := by
      rw [← hr, hp, LinearMap.map_smul, Algebra.smul_def, ← hu, ← Units.val_pow_eq_pow_val, ← mul_assoc,
        ← map_mul, Units.inv_mul, map_one, one_mul]

    rw [← map_denom_eq f φP φQ r hr hsurj] at hb
    change b ∈ Submodule.span B (algebraMap A B '' denom φP) at hb
    show algebraMap B K b * φQ q ∈ Submodule.span B (gens φP)
    induction hb using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      rw [hq, ← IsScalarTower.algebraMap_apply, mul_left_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, p, rfl⟩)
    | zero => rw [map_zero, zero_mul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add, add_mul]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      rw [smul_eq_mul, map_mul, mul_assoc, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hx
  · rw [Submodule.span_le]
    rintro _ ⟨a, ha, p, rfl⟩
    have ha' : algebraMap A B a ∈ denom φQ :=
      map_denom_le f φP φQ r hr hsurj (Ideal.mem_map_of_mem _ ha)
    refine ⟨⟨_, ha'⟩ ⊗ₜ r p, ?_⟩
    rw [mulMap_tmul, hr, Subtype.coe_mk, ← IsScalarTower.algebraMap_apply]

include hr hsurj in

theorem map_numer_eq_loc [Module.Finite A P] (hinjB : Function.Injective (algebraMap B K)) :
    (numer φP).map (algebraMap A B) = numer φQ := by
  apply Submodule.map_injective_of_injective (f := Algebra.linearMap B K) hinjB
  rw [map_linearMap_map, map_numer_eq, range_mulMap_loc f φP φQ r hr hsurj]

  have hset : algebraMap A K '' (numer φP : Set A) = (LinearMap.range (mulMap φP) : Set K) := by
    have := congrArg (fun S : Submodule A K => (S : Set K)) (map_numer_eq φP)
    simpa [Submodule.map_coe] using this
  rw [hset, range_mulMap_eq_span, Submodule.span_span_of_tower]

end Loc

section Geom

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

variable {X : Scheme.{u}}

def toSpecTop (X : Scheme.{u}) : X ⟶ Spec (.of Γ(X, ⊤)) := X.toSpecΓ

theorem finite_sections (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (U : X.affineOpens) :
    Module.Finite Γ(X, U) Γ(M, U) :=
  OModulePresheaf.isCoherent_ofModules_of_locallyTrivial (toSpecTop X) M hM.1 U

theorem flat_sections (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (U : X.affineOpens) :
    Module.Flat Γ(X, U) Γ(M, U) := by
  haveI := Scheme.Modules.projective_sections_of_locallyTrivial M hM.1 U
  exact Module.Flat.of_projective

theorem res_surj (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (U : X.affineOpens) (f : Γ(X, U))
    (x : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (y : Γ(M, U)), M.presheaf.map (homOfLE (X.basicOpen_le f)).op y =
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom (f ^ n) • x :=
  ((OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial (toSpecTop X) M hM.1) U f).1 x

theorem nonempty_of_le {U V : X.Opens} (h : V ≤ U) [hV : Nonempty V] : Nonempty U :=
  let ⟨⟨x, hx⟩⟩ := hV; ⟨⟨x, h hx⟩⟩

theorem eq_bot_of_not_nonempty {U : X.Opens} (h : ¬ Nonempty U) : U = ⊥ :=
  (Opens.not_nonempty_iff_eq_bot U).mp fun hne => h hne.to_subtype

theorem subsingleton_of_not_nonempty {U : X.Opens} (h : ¬ Nonempty U) : Subsingleton Γ(X, U) :=
  CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty (eq_bot_of_not_nonempty h))

section Integral

variable [IsIntegral X]

theorem genericPoint_mem (U : X.Opens) [h : Nonempty U] : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using h)

theorem algebraMap_res {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U) (a : Γ(X, U)) :
    algebraMap Γ(X, V) X.functionField ((X.presheaf.map (homOfLE h).op).hom a) =
      algebraMap Γ(X, U) X.functionField a :=
  TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE h) (genericPoint X) (genericPoint_mem V) a

theorem isScalarTower_basicOpen (U : X.Opens) (f : Γ(X, U)) [Nonempty U] [Nonempty (X.basicOpen f)] :
    IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) X.functionField :=
  IsScalarTower.of_algebraMap_eq fun a => (algebraMap_res (X.basicOpen_le f) a).symm

end Integral

section Families

variable [IsIntegral X] (M : X.Modules)
  (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
  (hφ₂ : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
    φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)

def φlin (U : X.Opens) [Nonempty U] : Γ(M, U) →ₗ[Γ(X, U)] (X.functionField : Type u) where
  toFun := φ U
  map_add' := map_add (φ U)
  map_smul' a m := by rw [RingHom.id_apply, Algebra.smul_def]; exact hφ₂ U a m

theorem φlin_apply (U : X.Opens) [Nonempty U] (m : Γ(M, U)) : φlin M φ hφ₂ U m = φ U m := rfl

open Classical in

def idealI (U : X.affineOpens) : Ideal Γ(X, U) :=
  if h : Nonempty (U : X.Opens) then (haveI := h; denom (φlin M φ hφ₂ U)) else ⊤

open Classical in

def idealJ (U : X.affineOpens) : Ideal Γ(X, U) :=
  if h : Nonempty (U : X.Opens) then (haveI := h; numer (φlin M φ hφ₂ U)) else ⊤

theorem idealI_eq (U : X.affineOpens) [h : Nonempty (U : X.Opens)] :
    idealI M φ hφ₂ U = denom (φlin M φ hφ₂ U) := dif_pos h

theorem idealJ_eq (U : X.affineOpens) [h : Nonempty (U : X.Opens)] :
    idealJ M φ hφ₂ U = numer (φlin M φ hφ₂ U) := dif_pos h

theorem idealI_eq_top (U : X.affineOpens) (h : ¬ Nonempty (U : X.Opens)) : idealI M φ hφ₂ U = ⊤ := dif_neg h

theorem idealJ_eq_top (U : X.affineOpens) (h : ¬ Nonempty (U : X.Opens)) : idealJ M φ hφ₂ U = ⊤ := dif_neg h

variable (hM : Scheme.Modules.IsInvertible M)
  (hφ₁ : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
    ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)

include hM hφ₁ in

theorem map_ideal_basicOpen (U : X.affineOpens) (f : Γ(X, U)) :
    (idealI M φ hφ₂ U).map (X.presheaf.map (homOfLE <| X.basicOpen_le f).op).hom =
        idealI M φ hφ₂ (X.affineBasicOpen f) ∧
      (idealJ M φ hφ₂ U).map (X.presheaf.map (homOfLE <| X.basicOpen_le f).op).hom =
        idealJ M φ hφ₂ (X.affineBasicOpen f) := by
  by_cases hD : Nonempty (X.basicOpen f)
  · haveI := hD
    haveI : Nonempty (U : X.Opens) := nonempty_of_le (X.basicOpen_le f)
    haveI := U.2.isLocalization_basicOpen f
    haveI hst : IsScalarTower Γ(X, (U : X.Opens)) Γ(X, X.basicOpen f) X.functionField :=
      isScalarTower_basicOpen (U : X.Opens) f
    haveI := finite_sections M hM U
    have hr : ∀ p : Γ(M, U), φlin M φ hφ₂ (X.basicOpen f)
        ((M.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom p) = φlin M φ hφ₂ U p := fun p =>
      hφ₁ U _ (X.basicOpen_le f) hD p
    have hsurj : ∀ q : Γ(M, X.basicOpen f), ∃ (n : ℕ) (p : Γ(M, U)),
        (M.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom p =
          (algebraMap Γ(X, U) Γ(X, X.basicOpen f) f ^ n) • q := fun q => by
      obtain ⟨n, p, hp⟩ := res_surj M hM U f q
      exact ⟨n, p, by rw [← map_pow]; exact hp⟩
    have halg : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom = algebraMap Γ(X, U) Γ(X, X.basicOpen f) :=
      rfl
    rw [idealI_eq, idealJ_eq, halg, idealI_eq M φ hφ₂ (X.affineBasicOpen f) (h := hD),
      idealJ_eq M φ hφ₂ (X.affineBasicOpen f) (h := hD)]
    have h1 := map_denom_eq f (φlin M φ hφ₂ U) (φlin M φ hφ₂ (X.basicOpen f))
      (M.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom hr hsurj
    have h2 := map_numer_eq_loc f (φlin M φ hφ₂ U) (φlin M φ hφ₂ (X.basicOpen f))
      (M.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom hr hsurj
      (X.germToFunctionField_injective (X.basicOpen f))
    exact ⟨h1, h2⟩
  · haveI : Subsingleton Γ(X, X.basicOpen f) := subsingleton_of_not_nonempty hD
    haveI : Subsingleton (Ideal Γ(X, X.basicOpen f)) := (Submodule.subsingleton_iff _).mpr inferInstance
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

def sheafI : X.IdealSheafData where
  ideal := idealI M φ hφ₂
  map_ideal_basicOpen U f := (map_ideal_basicOpen M φ hφ₂ hM hφ₁ U f).1

def sheafJ : X.IdealSheafData where
  ideal := idealJ M φ hφ₂
  map_ideal_basicOpen U f := (map_ideal_basicOpen M φ hφ₂ hM hφ₁ U f).2

theorem sheafI_ideal (U : X.affineOpens) : (sheafI M φ hφ₂ hM hφ₁).ideal U = idealI M φ hφ₂ U := rfl
theorem sheafJ_ideal (U : X.affineOpens) : (sheafJ M φ hφ₂ hM hφ₁).ideal U = idealJ M φ hφ₂ U := rfl

end Families

section Nonvanishing

variable [IsIntegral X] (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
  (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
  (hφ₁ : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
    ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
  (hφ₂ : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
    φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
  (hφ₃ : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))

include hM hφ₁ hφ₂ hφ₃ in

theorem exists_apply_ne_zero (U : X.affineOpens) [Nonempty (U : X.Opens)] :
    ∃ y : Γ(M, U), φ U y ≠ 0 := by
  obtain ⟨W₀, hξ, ⟨e₀⟩⟩ := hM.1 (genericPoint X)
  let E₀ : M.restrict W₀.ι ≅ (SheafOfModules.unit W₀.toScheme.ringCatSheaf : W₀.toScheme.Modules) :=
    (Scheme.Modules.restrictFunctorIsoPullback W₀.ι).app M ≪≫ e₀
  have hξU : genericPoint X ∈ (U : X.Opens) := genericPoint_mem (X := X) (U : X.Opens)
  obtain ⟨g, hgle, hξg⟩ := U.2.exists_basicOpen_le
    (⟨genericPoint X, (⟨hξ, hξU⟩ : genericPoint X ∈ W₀ ⊓ (U : X.Opens))⟩ : (W₀ ⊓ (U : X.Opens) : X.Opens)) hξU
  haveI hDne : Nonempty (X.basicOpen g) := ⟨⟨_, hξg⟩⟩

  let V : W₀.toScheme.Opens := W₀.ι ⁻¹ᵁ X.basicOpen g
  have hV : W₀.ι ''ᵁ V = X.basicOpen g := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr (hgle.trans inf_le_left)
  haveI : Nonempty V := ⟨⟨⟨genericPoint X, hξ⟩, show (W₀.ι ⟨genericPoint X, hξ⟩) ∈ X.basicOpen g from hξg⟩⟩

  let trivInv : Γ(W₀.toScheme, V) →+ Γ(M, W₀.ι ''ᵁ V) :=
    ((Scheme.Modules.Hom.app E₀.inv V).hom :
      Γ((SheafOfModules.unit W₀.toScheme.ringCatSheaf : W₀.toScheme.Modules), V) →+ Γ(M.restrict W₀.ι, V))
  have hinj : Function.Injective trivInv :=
    (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app E₀.inv V)).1
  have hm₁ : trivInv 1 ≠ 0 := (map_ne_zero_iff _ hinj).mpr one_ne_zero

  have hle : X.basicOpen g ≤ W₀.ι ''ᵁ V := hV.ge
  haveI : Nonempty (W₀.ι ''ᵁ V) := nonempty_of_le hle
  set m₂ : Γ(M, X.basicOpen g) := (M.presheaf.map (homOfLE hle).op).hom (trivInv 1) with hm₂
  have hm₂ne : φ (X.basicOpen g) m₂ ≠ 0 := by
    rw [hm₂, hφ₁ _ _ hle hDne]
    intro h
    exact hm₁ (hφ₃ _ inferInstance (by rw [h, map_zero]))

  obtain ⟨n, y, hy⟩ := res_surj M hM U g m₂
  refine ⟨y, fun h0 => ?_⟩
  have key := hφ₁ U (X.basicOpen g) (X.basicOpen_le g) hDne y
  rw [h0] at key
  change φ (X.basicOpen g) ((M.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom y) = 0 at key
  rw [hy, hφ₂] at key
  haveI := U.2.isLocalization_basicOpen g
  have hu : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom (g ^ n)) := by
    rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit (S := Γ(X, X.basicOpen g)) g).pow n
  exact (mul_ne_zero (hu.map (algebraMap Γ(X, X.basicOpen g) X.functionField)).ne_zero hm₂ne) key

end Nonvanishing

section Assembly

variable [IsIntegral X] (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
  (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
  (hφ₁ : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
    ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
  (hφ₂ : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
    φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
  (hφ₃ : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))

def ePos (U : X.affineOpens) [Nonempty (U : X.Opens)] :
    ↥(idealI M φ hφ₂ U) ⊗[Γ(X, U)] Γ(M, U) ≃ₗ[Γ(X, U)] ↥(idealJ M φ hφ₂ U) :=
  haveI := flat_sections M hM U
  (TensorProduct.congr (LinearEquiv.ofEq _ _ (idealI_eq M φ hφ₂ U)) (LinearEquiv.refl _ _)).trans
    ((equiv (φlin M φ hφ₂ U) (hφ₃ U inferInstance)
        (X.germToFunctionField_injective U)).trans
      (LinearEquiv.ofEq _ _ (idealJ_eq M φ hφ₂ U)).symm)

theorem algebraMap_ePos_tmul (U : X.affineOpens) [Nonempty (U : X.Opens)] (a : ↥(idealI M φ hφ₂ U))
    (m : Γ(M, U)) :
    algebraMap Γ(X, U) X.functionField (ePos M hM φ hφ₂ hφ₃ U (a ⊗ₜ m) : Γ(X, U)) =
      algebraMap Γ(X, U) X.functionField a * φ U m := by
  haveI := flat_sections M hM U
  simp only [ePos, LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply]
  rw [algebraMap_equiv, mulMap_tmul]
  rfl

def eEmpty (U : X.affineOpens) (h : ¬ Nonempty (U : X.Opens)) :
    ↥(idealI M φ hφ₂ U) ⊗[Γ(X, U)] Γ(M, U) ≃ₗ[Γ(X, U)] ↥(idealJ M φ hφ₂ U) :=
  haveI : Subsingleton Γ(X, U) := subsingleton_of_not_nonempty h
  haveI : Subsingleton (↥(idealI M φ hφ₂ U) ⊗[Γ(X, U)] Γ(M, U)) := Module.subsingleton Γ(X, U) _
  haveI : Subsingleton ↥(idealJ M φ hφ₂ U) := Module.subsingleton Γ(X, U) _
  LinearEquiv.ofSubsingleton _ _

open Classical in

def eAll (U : X.affineOpens) :
    ↥(idealI M φ hφ₂ U) ⊗[Γ(X, U)] Γ(M, U) ≃ₗ[Γ(X, U)] ↥(idealJ M φ hφ₂ U) :=
  if h : Nonempty (U : X.Opens) then (haveI := h; ePos M hM φ hφ₂ hφ₃ U) else eEmpty M φ hφ₂ U h

theorem eAll_eq (U : X.affineOpens) [h : Nonempty (U : X.Opens)] :
    eAll M hM φ hφ₂ hφ₃ U = ePos M hM φ hφ₂ hφ₃ U := dif_pos h

include hM hφ₁ hφ₂ hφ₃ in
theorem main :
    ∃ (I J : X.IdealSheafData)
      (e : ∀ U : X.affineOpens, ↥(I.ideal U) ⊗[Γ(X, U)] Γ(M, U) ≃ₗ[Γ(X, U)] ↥(J.ideal U)),
      (∀ (U : X.affineOpens) [Nonempty U] (a : Γ(X, U)),
          a ∈ I.ideal U ↔ ∀ m : Γ(M, U), ∃ b : Γ(X, U),
            algebraMap Γ(X, U) X.functionField b = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.affineOpens, Nonempty U → I.ideal U ≠ ⊥ ∧ J.ideal U ≠ ⊥) ∧
      (∀ (U : X.affineOpens) [Nonempty U] (a : ↥(I.ideal U)) (m : Γ(M, U)),
          algebraMap Γ(X, U) X.functionField (e U (a ⊗ₜ m) : Γ(X, U)) =
            algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ (U V : X.affineOpens) (h : (V : X.Opens) ≤ U) (a : ↥(I.ideal U)) (m : Γ(M, U)),
          X.presheaf.map (homOfLE h).op (e U (a ⊗ₜ m) : Γ(X, U)) =
            e V (⟨X.presheaf.map (homOfLE h).op a, I.ideal_le_comap_ideal h a.2⟩ ⊗ₜ
              M.presheaf.map (homOfLE h).op m)) := by
  refine ⟨sheafI M φ hφ₂ hM hφ₁, sheafJ M φ hφ₂ hM hφ₁, eAll M hM φ hφ₂ hφ₃, ?_, ?_, ?_, ?_⟩
  ·
    intro U hU a
    rw [sheafI_ideal, idealI_eq]
    exact Iff.rfl
  ·
    intro U hU
    haveI := hU
    haveI := functionField_isFractionRing_of_isAffineOpen X (U : X.Opens) U.2
    haveI := finite_sections M hM U
    obtain ⟨s, hs, hsd⟩ := exists_mem_denom (φlin M φ hφ₂ U) (nonZeroDivisors Γ(X, U))
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    rw [sheafI_ideal, sheafJ_ideal, idealI_eq, idealJ_eq]
    refine ⟨fun h => hs0 ?_, ?_⟩
    · rw [h] at hsd; exact (Submodule.mem_bot _).mp hsd
    · obtain ⟨y, hy⟩ := exists_apply_ne_zero M hM φ hφ₁ hφ₂ hφ₃ U
      exact numer_ne_bot _ (X.germToFunctionField_injective U) hsd hs0 (p := y) hy
  ·
    intro U hU a m
    show algebraMap Γ(X, U) X.functionField (eAll M hM φ hφ₂ hφ₃ U (a ⊗ₜ m) : Γ(X, U)) = _
    rw [eAll_eq]
    exact algebraMap_ePos_tmul M hM φ hφ₂ hφ₃ U a m
  ·
    intro U V h a m
    by_cases hV : Nonempty (V : X.Opens)
    · haveI := hV
      haveI : Nonempty (U : X.Opens) := nonempty_of_le h
      apply X.germToFunctionField_injective V
      change algebraMap Γ(X, V) X.functionField _ = algebraMap Γ(X, V) X.functionField _
      show algebraMap Γ(X, V) X.functionField
          ((X.presheaf.map (homOfLE h).op).hom (eAll M hM φ hφ₂ hφ₃ U (a ⊗ₜ m) : Γ(X, U))) =
        algebraMap Γ(X, V) X.functionField (eAll M hM φ hφ₂ hφ₃ V
          (⟨X.presheaf.map (homOfLE h).op a, (sheafI M φ hφ₂ hM hφ₁).ideal_le_comap_ideal h a.2⟩ ⊗ₜ
            M.presheaf.map (homOfLE h).op m) : Γ(X, V))
      rw [algebraMap_res h, eAll_eq, eAll_eq, algebraMap_ePos_tmul, algebraMap_ePos_tmul]
      change algebraMap Γ(X, U) X.functionField a * φ U m =
        algebraMap Γ(X, V) X.functionField ((X.presheaf.map (homOfLE h).op).hom a) *
          φ V (M.presheaf.map (homOfLE h).op m)
      rw [algebraMap_res h, hφ₁ U V h hV m]
    · haveI : Subsingleton Γ(X, V) := subsingleton_of_not_nonempty hV
      exact Subsingleton.elim _ _

end Assembly

end Geom

end P2mDenomAlg

end

open CategoryTheory AlgebraicGeometry TensorProduct in
theorem solution
    {X : Scheme.{u}} [IsIntegral X] (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hφ : (∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m) ∧
      (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
          φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.Opens, Nonempty U → Function.Injective (φ U))) :
    ∃ (I J : X.IdealSheafData)
      (e : ∀ U : X.affineOpens, ↥(I.ideal U) ⊗[Γ(X, U)] Γ(M, U) ≃ₗ[Γ(X, U)] ↥(J.ideal U)),
      (∀ (U : X.affineOpens) [Nonempty U] (a : Γ(X, U)),
          a ∈ I.ideal U ↔ ∀ m : Γ(M, U), ∃ b : Γ(X, U),
            algebraMap Γ(X, U) X.functionField b = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.affineOpens, Nonempty U → I.ideal U ≠ ⊥ ∧ J.ideal U ≠ ⊥) ∧
      (∀ (U : X.affineOpens) [Nonempty U] (a : ↥(I.ideal U)) (m : Γ(M, U)),
          algebraMap Γ(X, U) X.functionField (e U (a ⊗ₜ m) : Γ(X, U)) =
            algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ (U V : X.affineOpens) (h : (V : X.Opens) ≤ U) (a : ↥(I.ideal U)) (m : Γ(M, U)),
          X.presheaf.map (homOfLE h).op (e U (a ⊗ₜ m) : Γ(X, U)) =
            e V (⟨X.presheaf.map (homOfLE h).op a, I.ideal_le_comap_ideal h a.2⟩ ⊗ₜ
              M.presheaf.map (homOfLE h).op m)) :=
  P2mDenomAlg.main M hM φ hφ.1 hφ.2.1 hφ.2.2

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation (solution)
