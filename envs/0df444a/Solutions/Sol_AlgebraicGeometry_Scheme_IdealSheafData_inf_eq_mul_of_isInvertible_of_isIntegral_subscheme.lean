-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.inf_eq_mul_of_isInvertible_of_isIntegral_subscheme
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/930eaa0d-8eff-5f80-9678-e73ff5587af1

import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_inf_eq_mul_of_isInvertible_of_isIntegral_subscheme

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace FibProd

section Algebra
variable {R : Type*} [CommRing R]

theorem span_inf_span_eq_mul_of_isPrime_of_not_mem {s t : R} (hs : (Ideal.span {s}).IsPrime)
    (ht : t ∉ Ideal.span {s}) : Ideal.span {s} ⊓ Ideal.span {t} = Ideal.span {s} * Ideal.span {t} := by
  refine le_antisymm ?_ Ideal.mul_le_inf
  rintro x ⟨hxs, hxt⟩
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hxt
  have ha : a ∈ Ideal.span {s} := ((hs.mem_or_mem hxs).resolve_right ht)
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  rw [Ideal.span_singleton_mul_span_singleton]
  exact Ideal.mem_span_singleton'.mpr ⟨b, by ring⟩

theorem span_eq_span_of_le_of_isPrime_of_mem_nonZeroDivisors {s t : R} (hle : Ideal.span {t} ≤ Ideal.span {s})
    (ht : (Ideal.span {t}).IsPrime) (ht0 : t ∈ nonZeroDivisors R) (hs : Ideal.span {s} ≠ ⊤) :
    Ideal.span {s} = Ideal.span {t} := by
  refine le_antisymm ?_ hle
  obtain ⟨a, hat⟩ := Ideal.mem_span_singleton'.mp (hle (Ideal.mem_span_singleton_self t))

  have hmem : a * s ∈ Ideal.span {t} := hat ▸ Ideal.mem_span_singleton_self t
  rcases ht.mem_or_mem hmem with ha | hsmem
  ·
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    have h1 : (1 - b * s) * t = 0 := by linear_combination (-1 : R) * hat
    have h2 : 1 - b * s = 0 := (mul_right_mem_nonZeroDivisors_eq_zero_iff ht0).mp h1
    exfalso; apply hs
    rw [Ideal.eq_top_iff_one, show (1 : R) = b * s by rwa [sub_eq_zero] at h2]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self s)
  · exact (Ideal.span_singleton_le_iff_mem _).mpr hsmem

theorem span_inf_span_eq_mul_or_eq {s t : R}
    (hs : (Ideal.span {s}).IsPrime ∨ Ideal.span {s} = ⊤) (ht : (Ideal.span {t}).IsPrime ∨ Ideal.span {t} = ⊤)
    (ht0 : t ∈ nonZeroDivisors R) :
    Ideal.span {s} ⊓ Ideal.span {t} = Ideal.span {s} * Ideal.span {t} ∨
      (Ideal.span {s} = Ideal.span {t} ∧ Ideal.span {s} ≠ ⊤) := by
  rcases hs with hs | hs
  swap
  · left; rw [hs]; simp
  rcases ht with ht | ht
  swap
  · left; rw [ht]; simp
  by_cases hts : t ∈ Ideal.span {s}
  · right
    exact ⟨span_eq_span_of_le_of_isPrime_of_mem_nonZeroDivisors ((Ideal.span_singleton_le_iff_mem _).mpr hts)
      ht ht0 hs.ne_top, hs.ne_top⟩
  · left; exact span_inf_span_eq_mul_of_isPrime_of_not_mem hs hts

end Algebra

section Sheaf
variable {X : Scheme.{u}} (I : X.IdealSheafData)

theorem isRadical_ideal [IsReduced I.subscheme] (U : X.affineOpens) : (I.ideal U).IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced]
  have e := (I.subschemeObjIso U).commRingCatIsoToRingEquiv
  haveI : IsReduced Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U) := inferInstance
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

theorem radical_eq [IsReduced I.subscheme] : I.radical = I := by
  ext U : 2
  exact (isRadical_ideal I U).radical

theorem eq_vanishingIdeal_support [IsReduced I.subscheme] :
    I = Scheme.IdealSheafData.vanishingIdeal I.support := by
  rw [Scheme.IdealSheafData.vanishingIdeal_support, radical_eq]

theorem isPrime_or_eq_top_ideal [IsIntegral I.subscheme] (U : X.affineOpens) :
    (I.ideal U).IsPrime ∨ I.ideal U = ⊤ := by
  have e := (I.subschemeObjIso U).commRingCatIsoToRingEquiv
  rcases (I.subschemeι ⁻¹ᵁ (U : X.Opens)).1.eq_empty_or_nonempty with h | h
  · right
    have hbot : I.subschemeι ⁻¹ᵁ (U : X.Opens) = ⊥ := SetLike.ext' h
    haveI : Subsingleton Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U) :=
      CommRingCat.subsingleton_of_isTerminal (I.subscheme.sheaf.isTerminalOfEqEmpty hbot)
    haveI : Subsingleton (Γ(X, U) ⧸ I.ideal U) := e.symm.injective.subsingleton
    exact Ideal.Quotient.subsingleton_iff.mp this
  · left
    obtain ⟨x, hx⟩ := h
    haveI : IsDomain Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U) := @IsIntegral.component_integral _ _ _ ⟨⟨x, hx⟩⟩
    haveI : IsDomain (Γ(X, U) ⧸ I.ideal U) := MulEquiv.isDomain _ e.symm.toMulEquiv
    exact (Ideal.Quotient.isDomain_iff_prime _).mp this

theorem isIrreducible_support [IsIntegral I.subscheme] : IsIrreducible (I.support : Set X) := by
  have h := (IrreducibleSpace.isIrreducible_univ (X := ↥I.subscheme)).image I.subschemeι
    I.subschemeι.continuous.continuousOn
  rwa [Set.image_univ, Scheme.IdealSheafData.range_subschemeι] at h

theorem support_inter_nonempty_of_ideal_ne_top (U : X.affineOpens) (hU : I.ideal U ≠ ⊤) :
    ((I.support : Set X) ∩ U).Nonempty := by
  rw [Scheme.IdealSheafData.coe_support_inter, ← U.2.fromSpec_image_zeroLocus]
  refine Set.Nonempty.image _ ?_

  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hU
  exact ⟨⟨m, hm.isPrime⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr hle⟩

end Sheaf

section Main
variable {X : Scheme.{u}}

theorem eq_of_ideal_eq {I J : X.IdealSheafData} [IsIntegral I.subscheme] [IsIntegral J.subscheme]
    (U : X.affineOpens) (h : I.ideal U = J.ideal U) (hne : I.ideal U ≠ ⊤) : I = J := by
  have hsI := isIrreducible_support I
  have hsJ := isIrreducible_support J

  have hU : (I.support : Set X) ∩ U = (J.support : Set X) ∩ U := by
    rw [Scheme.IdealSheafData.coe_support_inter, Scheme.IdealSheafData.coe_support_inter, h]
  have hneI : ((I.support : Set X) ∩ U).Nonempty := support_inter_nonempty_of_ideal_ne_top I U hne
  have hneJ : ((J.support : Set X) ∩ U).Nonempty := hU ▸ hneI

  have hcl : ∀ (K : X.IdealSheafData), IsIrreducible (K.support : Set X) → ((K.support : Set X) ∩ U).Nonempty →
      (K.support : Set X) = closure ((K.support : Set X) ∩ U) := by
    intro K hK hKne
    refine le_antisymm (subset_closure_inter_of_isPreirreducible_of_isOpen hK.isPreirreducible U.1.isOpen hKne) ?_
    exact (closure_minimal Set.inter_subset_left K.support.isClosed)
  have hsupp : I.support = J.support := by
    apply TopologicalSpace.Closeds.ext
    rw [hcl I hsI hneI, hcl J hsJ hneJ, hU]
  rw [eq_vanishingIdeal_support I, eq_vanishingIdeal_support J, hsupp]

theorem inf_eq_mul {I J : X.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible)
    [IsIntegral I.subscheme] [IsIntegral J.subscheme] (hIJ : ¬ I ≤ J) (hJI : ¬ J ≤ I) :
    I ⊓ J = I * J := by
  classical

  have key : ∀ x : X, ∃ (W : X.affineOpens), x ∈ (W : X.Opens) ∧ ∃ s t : Γ(X, W),
      s ∈ nonZeroDivisors Γ(X, W) ∧ t ∈ nonZeroDivisors Γ(X, W) ∧
      I.ideal W = Ideal.span {s} ∧ J.ideal W = Ideal.span {t} := by
    intro x
    obtain ⟨U, f, hxf, g, hg, hIg⟩ := hI x
    obtain ⟨U', f', hxf', g', hg', hJg⟩ := hJ x
    obtain ⟨h, h', hhh', hxh⟩ := exists_basicOpen_le_affine_inter (X.affineBasicOpen f).2
      (X.affineBasicOpen f').2 x ⟨hxf, hxf'⟩
    have hW : (X.affineBasicOpen h : X.Opens) ≤ X.affineBasicOpen f := X.basicOpen_le h
    have hW' : (X.affineBasicOpen h : X.Opens) ≤ X.affineBasicOpen f' := hhh'.trans_le (X.basicOpen_le h')
    refine ⟨X.affineBasicOpen h, hxh, (X.presheaf.map (homOfLE hW).op).hom g,
      (X.presheaf.map (homOfLE hW').op).hom g', ?_, ?_, ?_, ?_⟩
    · letI := (X.affineBasicOpen f).2.isLocalization_basicOpen h
      exact IsLocalization.nonZeroDivisors_le_comap (M := .powers h) (S := Γ(X, X.basicOpen h)) hg
    · letI := (X.presheaf.map (homOfLE hW').op).hom.toAlgebra
      haveI := (X.affineBasicOpen f').2.isLocalization_of_eq_basicOpen h' (homOfLE hW') hhh'
      exact IsLocalization.nonZeroDivisors_le_comap (M := .powers h') (S := Γ(X, X.affineBasicOpen h)) hg'
    · rw [← I.map_ideal (U := X.affineBasicOpen h) (V := X.affineBasicOpen f) hW, hIg, Ideal.map_span,
        Set.image_singleton]
      rfl
    · rw [← J.map_ideal (U := X.affineBasicOpen h) (V := X.affineBasicOpen f') hW', hJg, Ideal.map_span,
        Set.image_singleton]
      rfl
  choose W hxW s t hs ht hIs hJt using key

  refine Scheme.IdealSheafData.ext_of_iSup_eq_top W ?_ ?_
  · rw [eq_top_iff]
    rintro y -
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hxW y⟩
  · intro x
    simp only [Scheme.IdealSheafData.ideal_inf, Scheme.IdealSheafData.ideal_mul, Pi.inf_apply, Pi.mul_apply]
    have hpI := isPrime_or_eq_top_ideal I (W x)
    have hpJ := isPrime_or_eq_top_ideal J (W x)
    rw [hIs] at hpI ⊢
    rw [hJt] at hpJ ⊢
    rcases span_inf_span_eq_mul_or_eq hpI hpJ (ht x) with hmul | ⟨heq, hne⟩
    · exact hmul
    ·
      exfalso
      have hIJW : I.ideal (W x) = J.ideal (W x) := by rw [hIs, hJt, heq]
      have hneW : I.ideal (W x) ≠ ⊤ := by rw [hIs]; exact hne
      exact hIJ (le_of_eq (eq_of_ideal_eq (W x) hIJW hneW))

end Main

end FibProd

theorem solution
    {X : Scheme.{u}} {I J : X.IdealSheafData}
    (hI : I.IsInvertible) (hJ : J.IsInvertible)
    [IsIntegral I.subscheme] [IsIntegral J.subscheme] (hIJ : ¬ I ≤ J) (hJI : ¬ J ≤ I) :
    I ⊓ J = I * J :=
  FibProd.inf_eq_mul hI hJ hIJ hJI

end S_AlgebraicGeometry_Scheme_IdealSheafData_inf_eq_mul_of_isInvertible_of_isIntegral_subscheme
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_inf_eq_mul_of_isInvertible_of_isIntegral_subscheme (solution)
