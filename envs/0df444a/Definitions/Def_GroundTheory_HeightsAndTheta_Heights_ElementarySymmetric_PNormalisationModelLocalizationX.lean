-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PNormalisationModelLocalizationX
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PNormalisationModelLocalizationX
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:27.942909+00:00
-- url     : https://prove2.me/theorems/0964c14a-a585-46a6-a1bd-a8fcaa417d9d
-- title:
--   PNormalisation Model Localization X
-- statement:
--   Definitions and structural lemmas for PNormalisation Model Localization X, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PNormalisationModelLocalizationX.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalisationModelLocalization
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isUnit_algebraMap_curveLocalRing_358a5a627391

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets
noncomputable section
namespace NormalisationModelLocalization
variable {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
theorem disjoint_primeCompl (hq : q ∈ zeroSet J) :
    Disjoint ((RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl : Set (MvPolynomial (Fin n) ℂ))
      (J : Set (MvPolynomial (Fin n) ℂ)) := by
  rw [Set.disjoint_left]
  intro f hf hfJ
  exact hf (RingHom.mem_ker.2 (hq f hfJ))
theorem isPrime_map (hJ : J.IsPrime) (hq : q ∈ zeroSet J) :
    (J.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint (RingHom.ker (eval q)).primeCompl _ J hJ (disjoint_primeCompl hq)
theorem isDomain (hJ : J.IsPrime) (hq : q ∈ zeroSet J) : IsDomain (curveLocalRing J q) := by
  haveI := isPrime_map hJ hq
  exact Ideal.Quotient.isDomain _
theorem algebraMap_eq_zero_iff (hJ : J.IsPrime) (hq : q ∈ zeroSet J) (f : MvPolynomial (Fin n) ℂ) :
    algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f = 0 ↔ f ∈ J := by
  change Ideal.Quotient.mk _ (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))) f) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap]
  have h := IsLocalization.under_map_of_isPrime_disjoint (M := (RingHom.ker (eval q)).primeCompl)
    (S := Localization.AtPrime (RingHom.ker (eval q))) hJ (disjoint_primeCompl hq)
  rw [Ideal.under] at h
  rw [h]
def toFrac (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ →+* FractionRing (curveLocalRing J q) :=
  (algebraMap (curveLocalRing J q) (FractionRing (curveLocalRing J q))).comp
    (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q))
theorem toFrac_eq_zero_iff (hJ : J.IsPrime) (hq : q ∈ zeroSet J) (f : MvPolynomial (Fin n) ℂ) :
    toFrac J q f = 0 ↔ f ∈ J := by
  rw [toFrac, RingHom.comp_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _), algebraMap_eq_zero_iff hJ hq]
variable (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
theorem rename_mem_iff (f : MvPolynomial (Fin n) ℂ) : rename Sum.inl f ∈ M.ideal ↔ f ∈ J := by
  constructor
  · intro h
    rw [← M.comap_eq]
    exact h
  · intro h
    rw [← M.comap_eq] at h
    exact h
def num (i : Fin M.m) : MvPolynomial (Fin n) ℂ := (M.birational i).choose
def den (i : Fin M.m) : MvPolynomial (Fin n) ℂ := (M.birational i).choose_spec.choose
theorem den_not_mem (i : Fin M.m) : den M i ∉ J := (M.birational i).choose_spec.choose_spec.1
theorem den_mul_sub_mem (i : Fin M.m) :
    rename Sum.inl (den M i) * X (Sum.inr i) - rename Sum.inl (num M i) ∈ M.ideal :=
  (M.birational i).choose_spec.choose_spec.2
def denProd : MvPolynomial (Fin n) ℂ := ∏ i, den M i
def relIdeal : Ideal (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) :=
  Ideal.span (Set.range fun i => rename Sum.inl (den M i) * X (Sum.inr i) - rename Sum.inl (num M i))
theorem relIdeal_le : relIdeal M ≤ M.ideal := by
  rw [relIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact den_mul_sub_mem M i
theorem clear (h : MvPolynomial (Fin n ⊕ Fin M.m) ℂ) :
    ∃ (N : ℕ) (g : MvPolynomial (Fin n) ℂ),
      rename Sum.inl (denProd M) ^ N * h - rename Sum.inl g ∈ relIdeal M := by
  induction h using MvPolynomial.induction_on with
  | C c => exact ⟨0, C c, by simp⟩
  | add p r hp hr =>
    obtain ⟨N₁, g₁, h₁⟩ := hp
    obtain ⟨N₂, g₂, h₂⟩ := hr
    refine ⟨N₁ + N₂, denProd M ^ N₂ * g₁ + denProd M ^ N₁ * g₂, ?_⟩
    have e : rename Sum.inl (denProd M) ^ (N₁ + N₂) * (p + r) -
        rename Sum.inl (denProd M ^ N₂ * g₁ + denProd M ^ N₁ * g₂) =
        rename Sum.inl (denProd M) ^ N₂ * (rename Sum.inl (denProd M) ^ N₁ * p - rename Sum.inl g₁) +
          rename Sum.inl (denProd M) ^ N₁ * (rename Sum.inl (denProd M) ^ N₂ * r - rename Sum.inl g₂) := by
      simp only [map_add, map_mul, map_pow]
      ring
    rw [e]
    exact add_mem (Ideal.mul_mem_left _ _ h₁) (Ideal.mul_mem_left _ _ h₂)
  | mul_X p s hp =>
    obtain ⟨N, g, hg⟩ := hp
    cases s with
    | inl i =>
      refine ⟨N, g * X i, ?_⟩
      have e : rename Sum.inl (denProd M) ^ N * (p * X (Sum.inl i)) - rename Sum.inl (g * X i) =
          (rename Sum.inl (denProd M) ^ N * p - rename Sum.inl g) * X (Sum.inl i) := by
        simp only [map_mul, rename_X]
        ring
      rw [e]
      exact Ideal.mul_mem_right _ _ hg
    | inr i =>
      set c := ∏ j ∈ Finset.univ.erase i, den M j with hc
      have hB : denProd M = den M i * c := (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
      refine ⟨N + 1, g * c * num M i, ?_⟩
      have e : rename Sum.inl (denProd M) ^ (N + 1) * (p * X (Sum.inr i)) - rename Sum.inl (g * c * num M i) =
          (rename Sum.inl (denProd M) ^ N * p - rename Sum.inl g) * (rename Sum.inl (denProd M) * X (Sum.inr i)) +
            rename Sum.inl g * rename Sum.inl c *
              (rename Sum.inl (den M i) * X (Sum.inr i) - rename Sum.inl (num M i)) := by
        rw [hB]
        simp only [map_mul]
        ring
      rw [e]
      exact add_mem (Ideal.mul_mem_right _ _ hg) (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))
def toFracModel (q : Fin n → ℂ) : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* FractionRing (curveLocalRing J q) :=
  eval₂Hom ((toFrac J q).comp C)
    (Sum.elim (fun j => toFrac J q (X j)) (fun i => toFrac J q (num M i) * Ring.inverse (toFrac J q (den M i))))
theorem toFracModel_rename (f : MvPolynomial (Fin n) ℂ) : toFracModel M q (rename Sum.inl f) = toFrac J q f := by
  rw [toFracModel, eval₂Hom_rename]
  have e : eval₂Hom ((toFrac J q).comp C) (Sum.elim (fun j => toFrac J q (X j))
      (fun i => toFrac J q (num M i) * Ring.inverse (toFrac J q (den M i))) ∘ Sum.inl) = toFrac J q := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro j
      simp
  rw [e]
variable {M}
theorem relIdeal_le_ker (hJ : J.IsPrime) (hq : q ∈ zeroSet J) : relIdeal M ≤ RingHom.ker (toFracModel M q) := by
  have := isDomain hJ hq
  rw [relIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have hu : IsUnit (toFrac J q (den M i)) :=
    isUnit_iff_ne_zero.2 (fun h => den_not_mem M i ((toFrac_eq_zero_iff hJ hq _).1 h))
  simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, toFracModel_rename]
  rw [toFracModel, eval₂Hom_X', Sum.elim_inr, mul_left_comm, Ring.mul_inverse_cancel _ hu, mul_one, sub_self]
theorem ker_toFracModel (hJ : J.IsPrime) (hq : q ∈ zeroSet J) : RingHom.ker (toFracModel M q) = M.ideal := by
  have := isDomain hJ hq
  have hBJ : toFrac J q (denProd M) ≠ 0 := by
    rw [denProd, map_prod]
    exact Finset.prod_ne_zero_iff.2 (fun i _ h => den_not_mem M i ((toFrac_eq_zero_iff hJ hq _).1 h))
  have hBM : rename Sum.inl (denProd M) ∉ M.ideal :=
    fun h => hBJ ((toFrac_eq_zero_iff hJ hq _).2 ((rename_mem_iff M _).1 h))
  ext h
  obtain ⟨N, g, hg⟩ := clear M h
  have hφ := relIdeal_le_ker hJ hq hg
  rw [RingHom.mem_ker, map_sub, map_mul, map_pow, toFracModel_rename, toFracModel_rename, sub_eq_zero] at hφ
  have hM := relIdeal_le M hg
  rw [RingHom.mem_ker]
  constructor
  · intro h0
    rw [h0, mul_zero, eq_comm, toFrac_eq_zero_iff hJ hq] at hφ
    have hg' : rename Sum.inl g ∈ M.ideal := (rename_mem_iff M g).2 hφ
    have hmul : rename Sum.inl (denProd M) ^ N * h ∈ M.ideal := by
      have := M.ideal.add_mem hM hg'
      rwa [sub_add_cancel] at this
    exact (M.isPrime.mem_or_mem hmul).resolve_left (fun hp => hBM (M.isPrime.mem_of_pow_mem N hp))
  · intro hh
    have hg' : rename Sum.inl g ∈ M.ideal := by
      have := M.ideal.sub_mem (M.ideal.mul_mem_left (rename Sum.inl (denProd M) ^ N) hh) hM
      rwa [sub_sub_cancel] at this
    rw [(toFrac_eq_zero_iff hJ hq g).2 ((rename_mem_iff M g).1 hg')] at hφ
    exact (mul_eq_zero.1 hφ).resolve_left (pow_ne_zero _ hBJ)
variable (M)
def modelToFrac (hJ : J.IsPrime) (hq : q ∈ zeroSet J) :
    (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) →+* FractionRing (curveLocalRing J q) :=
  Ideal.Quotient.lift M.ideal (toFracModel M q) (fun a ha => by
    rw [← RingHom.mem_ker, ker_toFracModel hJ hq]
    exact ha)
theorem modelToFrac_mk (hJ : J.IsPrime) (hq : q ∈ zeroSet J) (h : MvPolynomial (Fin n ⊕ Fin M.m) ℂ) :
    modelToFrac M hJ hq (Ideal.Quotient.mk M.ideal h) = toFracModel M q h :=
  Ideal.Quotient.lift_mk _ _ _
theorem modelToFrac_isUnit (hJ : J.IsPrime) (hq : q ∈ zeroSet J) (y : normalModelSubmonoid M q) :
    IsUnit (modelToFrac M hJ hq y) := by
  obtain ⟨f, hf, hfy⟩ := y.2
  have hy : (y : MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) = Ideal.Quotient.mk M.ideal (rename Sum.inl f) :=
    hfy.symm
  rw [hy, modelToFrac_mk, toFracModel_rename]
  exact (isUnit_algebraMap_curveLocalRing J q f (fun h0 => hf (RingHom.mem_ker.2 h0))).map
    (algebraMap (curveLocalRing J q) (FractionRing (curveLocalRing J q)))
def locToFrac (hJ : J.IsPrime) (hq : q ∈ zeroSet J) :
    Localization (normalModelSubmonoid M q) →+* FractionRing (curveLocalRing J q) :=
  IsLocalization.lift (M := normalModelSubmonoid M q) (S := Localization (normalModelSubmonoid M q))
    (modelToFrac_isUnit M hJ hq)
def polyLocToModel : Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) →+*
    Localization (normalModelSubmonoid M q) :=
  IsLocalization.lift (M := (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl)
    (S := Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))
    (P := Localization (normalModelSubmonoid M q))
    (g := (algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) (Localization (normalModelSubmonoid M q))).comp
      ((Ideal.Quotient.mk M.ideal).comp
        (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom))
    (fun y => IsLocalization.map_units (Localization (normalModelSubmonoid M q))
      (⟨_, Submonoid.mem_map_of_mem _ y.2⟩ : normalModelSubmonoid M q))
theorem polyLocToModel_algebraMap (f : MvPolynomial (Fin n) ℂ) :
    polyLocToModel M (algebraMap _ _ f) =
      algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) (Localization (normalModelSubmonoid M q))
        (Ideal.Quotient.mk M.ideal (rename Sum.inl f)) := by
  rw [polyLocToModel]
  exact IsLocalization.lift_eq _ _
def locToModel : curveLocalRing J q →+* Localization (normalModelSubmonoid M q) :=
  Ideal.Quotient.lift _ (polyLocToModel M) (fun a ha => by
    have hle : J.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) ≤
        RingHom.ker (polyLocToModel M) := by
      rw [Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap, RingHom.mem_ker, polyLocToModel_algebraMap,
        Ideal.Quotient.eq_zero_iff_mem.2 ((rename_mem_iff M f).2 hf), map_zero]
    exact hle ha)
end NormalisationModelLocalization
end
end GroundTheory.Heights₂.Heights


