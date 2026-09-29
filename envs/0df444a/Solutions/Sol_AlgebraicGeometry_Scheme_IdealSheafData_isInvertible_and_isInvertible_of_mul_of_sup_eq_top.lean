-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.isInvertible_and_isInvertible_of_mul_of_sup_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/f9f4b34f-1a9d-53e3-97da-58a8065413b3

import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_and_isInvertible_of_mul_of_sup_eq_top

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace T7COPRIME

p2m_open "AlgebraicGeometry.Scheme.IdealSheafData"

variable {X : Scheme.{u}}

theorem mem_basicOpen_of_notMem {W : X.affineOpens} {x : X} (hxW : x ∈ (W : X.Opens))
    (b : Γ(X, W)) (hb : b ∉ (W.2.primeIdealOf ⟨x, hxW⟩).asIdeal) : x ∈ X.basicOpen b := by
  have h2 : W.2.primeIdealOf ⟨x, hxW⟩ ∈ PrimeSpectrum.basicOpen b :=
    (PrimeSpectrum.mem_basicOpen _ _).mpr hb
  rw [← W.2.fromSpec_preimage_basicOpen] at h2
  have h3 : W.2.fromSpec (W.2.primeIdealOf ⟨x, hxW⟩) ∈ X.basicOpen b := h2
  rwa [W.2.fromSpec_primeIdealOf] at h3

theorem at_affine {I J : X.IdealSheafData} {x : X} (W : X.affineOpens) (hxW : x ∈ (W : X.Opens))
    (g : Γ(X, W)) (hg : g ∈ nonZeroDivisors Γ(X, W))
    (hmul : I.ideal W * J.ideal W = Ideal.span {g}) (hsup : I.ideal W ⊔ J.ideal W = ⊤) :
    ∃ (U' : X.affineOpens) (f' : Γ(X, U')), x ∈ X.basicOpen f' ∧
      ∃ g' ∈ nonZeroDivisors Γ(X, X.affineBasicOpen f'),
        I.ideal (X.affineBasicOpen f') = Ideal.span {g'} := by

  have key : ∀ (b : Γ(X, W)), b ∉ (W.2.primeIdealOf ⟨x, hxW⟩).asIdeal →
      (b ∈ J.ideal W ∨ b ∈ I.ideal W) →
      ∃ (U' : X.affineOpens) (f' : Γ(X, U')), x ∈ X.basicOpen f' ∧
        ∃ g' ∈ nonZeroDivisors Γ(X, X.affineBasicOpen f'),
          I.ideal (X.affineBasicOpen f') = Ideal.span {g'} := by
    intro b hb𝔭 hb
    have hle : (X.affineBasicOpen b : X.Opens) ≤ W := X.basicOpen_le b
    letI := W.2.isLocalization_basicOpen b
    have hunit : IsUnit ((X.presheaf.map (homOfLE hle).op).hom b) :=
      IsLocalization.Away.algebraMap_isUnit (S := Γ(X, X.basicOpen b)) b
    refine ⟨W, b, mem_basicOpen_of_notMem hxW b hb𝔭, ?_⟩
    rcases hb with hbJ | hbI
    ·
      refine ⟨(X.presheaf.map (homOfLE hle).op).hom g, ?_, ?_⟩
      · exact IsLocalization.nonZeroDivisors_le_comap (M := .powers b)
          (S := Γ(X, X.basicOpen b)) hg
      · have hJtop : (J.ideal W).map (X.presheaf.map (homOfLE hle).op).hom = ⊤ :=
          Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hbJ) hunit
        have hIJ : ((I.ideal W).map (X.presheaf.map (homOfLE hle).op).hom) *
            ((J.ideal W).map (X.presheaf.map (homOfLE hle).op).hom)
              = Ideal.span {(X.presheaf.map (homOfLE hle).op).hom g} := by
          rw [← Ideal.map_mul, hmul, Ideal.map_span, Set.image_singleton]
        rw [← I.map_ideal hle, ← hIJ, hJtop, Ideal.mul_top]
        rfl
    ·
      refine ⟨1, one_mem _, ?_⟩
      rw [← I.map_ideal hle, Ideal.span_singleton_one]
      exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hbI) hunit
  by_cases hJ : J.ideal W ≤ (W.2.primeIdealOf ⟨x, hxW⟩).asIdeal
  · have hI : ¬ I.ideal W ≤ (W.2.primeIdealOf ⟨x, hxW⟩).asIdeal := by
      intro hI
      have : I.ideal W ⊔ J.ideal W ≤ (W.2.primeIdealOf ⟨x, hxW⟩).asIdeal := sup_le hI hJ
      rw [hsup, top_le_iff] at this
      exact (W.2.primeIdealOf ⟨x, hxW⟩).isPrime.ne_top this
    obtain ⟨a, haI, ha𝔭⟩ := SetLike.not_le_iff_exists.mp hI
    exact key a ha𝔭 (Or.inr haI)
  · obtain ⟨b, hbJ, hb𝔭⟩ := SetLike.not_le_iff_exists.mp hJ
    exact key b hb𝔭 (Or.inl hbJ)

theorem left {I J : X.IdealSheafData} (hIJ : (I * J).IsInvertible) (hcop : I ⊔ J = ⊤) :
    I.IsInvertible := by
  intro x
  obtain ⟨U, f, hxf, g, hg, hg'⟩ := hIJ x
  refine at_affine (J := J) (X.affineBasicOpen f) hxf g hg ?_ ?_
  · rw [← hg', ideal_mul, Pi.mul_apply]
  · have := congrArg (fun K : X.IdealSheafData => K.ideal (X.affineBasicOpen f)) hcop
    simpa [ideal_sup, ideal_top] using this

theorem main {I J : X.IdealSheafData} (hIJ : (I * J).IsInvertible) (hcop : I ⊔ J = ⊤) :
    I.IsInvertible ∧ J.IsInvertible :=
  ⟨left hIJ hcop, left (by rwa [mul_comm]) (by rwa [sup_comm])⟩

end T7COPRIME

theorem solution
    {X : Scheme.{u}} {I J : X.IdealSheafData} (hIJ : (I * J).IsInvertible) (hcop : I ⊔ J = ⊤) :
    I.IsInvertible ∧ J.IsInvertible :=
  T7COPRIME.main hIJ hcop

end S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_and_isInvertible_of_mul_of_sup_eq_top
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_and_isInvertible_of_mul_of_sup_eq_top (solution)
