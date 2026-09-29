-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.eq_comap_map_of_ideal_basicOpen_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/f6714842-726d-5f02-b2ae-3402b7a7cc5e

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span.AlgebraicGeometry HomogeneousLocalization"

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Proj.awayToSection_comp_appLE Scheme Proj Scheme.IdealSheafData.ext_of_iSup_eq_top Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.map_preimage_basicOpen Proj.iSup_basicOpen_eq_top Proj.awayToSection Scheme.IdealSheafData ProjSpace.irrelevant_le_span_X ProjSpace.X_mem_one ProjSpace.mvMapGraded ProjSpace.mvMapGraded_X ProjSpace.irrelevant_le_map_mvMapGraded ProjSpace.map ProjSpace.map_eq Scheme.IdealSheafData.ideal_comap_of_le"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "irrelevant_le_span_X X_mem_one mvMapGraded mvMapGraded_X irrelevant_le_map_mvMapGraded map map_eq"
namespace BCComap
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

section Dehom

variable {R : Type} [CommRing R] (n : ℕ) (i : Fin (n + 1))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

theorem X_pow_mem (e : ℕ) : (X i : MvPolynomial (Fin (n + 1)) R) ^ e ∈ 𝒜 e :=
  (MvPolynomial.mem_homogeneousSubmodule e _).mpr (MvPolynomial.isHomogeneous_X_pow i e)

def dh (e : ℕ) (G : 𝒜 e) : Γ(Proj 𝒜, Proj.basicOpen 𝒜 (X i)) :=
  Proj.awayToSection 𝒜 (X i)
    (HomogeneousLocalization.mk
      { deg := e
        num := G
        den := ⟨X i ^ e, X_pow_mem n i e⟩
        den_mem := ⟨e, rfl⟩ })

theorem dh_add (e : ℕ) (G H : 𝒜 e) : dh n i e (G + H) = dh n i e G + dh n i e H := by
  unfold dh
  rw [← map_add]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_add, HomogeneousLocalization.val_mk]
  exact (Localization.add_mk_self _ _ _).symm

theorem dh_zero (e : ℕ) : dh n i e (0 : 𝒜 e) = 0 := by
  unfold dh
  rw [← (Proj.awayToSection 𝒜 (X i)).hom.map_zero]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_zero, HomogeneousLocalization.val_mk]
  exact Localization.mk_zero _

theorem dh_congr {e : ℕ} {G H : 𝒜 e} (h : (G : MvPolynomial (Fin (n + 1)) R) = H) :
    dh n i e G = dh n i e H := by
  rw [Subtype.ext h]

theorem dh_eq_zero {e : ℕ} {G : 𝒜 e} (h : (G : MvPolynomial (Fin (n + 1)) R) = 0) : dh n i e G = 0 := by
  rw [show G = 0 from Subtype.ext h, dh_zero]

theorem dh_mul (a b : ℕ) (G : 𝒜 a) (H : 𝒜 b) :
    dh n i (a + b) ⟨(G : MvPolynomial (Fin (n + 1)) R) * (H : MvPolynomial (Fin (n + 1)) R),
        SetLike.GradedMul.mul_mem G.2 H.2⟩ =
      dh n i a G * dh n i b H := by
  unfold dh
  rw [← map_mul]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mk, Localization.mk_mul]
  congr 1
  exact Subtype.ext (pow_add _ _ _)

theorem dh_mul' {a b e : ℕ} (h : a + b = e) (G : 𝒜 a) (H : 𝒜 b) (K : 𝒜 e)
    (hK : (K : MvPolynomial (Fin (n + 1)) R) = (G : MvPolynomial (Fin (n + 1)) R) * (H : MvPolynomial (Fin (n + 1)) R)) :
    dh n i e K = dh n i a G * dh n i b H := by
  subst h
  rw [← dh_mul]
  exact dh_congr n i hK

theorem dh_sum {ι : Type} (s : Finset ι) (e : ℕ) (G : ι → 𝒜 e) :
    dh n i e (∑ j ∈ s, G j) = ∑ j ∈ s, dh n i e (G j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dh_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, dh_add, ih]

theorem coe_decompose (G : MvPolynomial (Fin (n + 1)) R) (e : ℕ) :
    ((DirectSum.decompose 𝒜 G) e : MvPolynomial (Fin (n + 1)) R) = homogeneousComponent e G :=
  MvPolynomial.decomposition.decompose'_apply G e

theorem decompose_sum_apply {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (Fin (n + 1)) R) (e : ℕ) :
    DirectSum.decompose 𝒜 (∑ j ∈ s, f j) e = ∑ j ∈ s, DirectSum.decompose 𝒜 (f j) e := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, DirectSum.decompose_zero, DirectSum.zero_apply]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, DirectSum.decompose_add, DirectSum.add_apply, ih]

theorem dh_decompose_mem_of_mem_span (S : Set (MvPolynomial (Fin (n + 1)) R))
    (T : Ideal Γ(Proj 𝒜, Proj.basicOpen 𝒜 (X i)))
    (hS : ∀ p ∈ S, ∀ e : ℕ, dh n i e (DirectSum.decompose 𝒜 p e) ∈ T)
    {F : MvPolynomial (Fin (n + 1)) R} (hF : F ∈ Ideal.span S) :
    ∀ e : ℕ, dh n i e (DirectSum.decompose 𝒜 F e) ∈ T := by
  classical
  induction hF using Submodule.span_induction with
  | mem p hp => exact hS p hp
  | zero => intro e; rw [DirectSum.decompose_zero, DirectSum.zero_apply, dh_zero]; exact T.zero_mem
  | add p q _ _ hp hq =>
    intro e
    rw [DirectSum.decompose_add, DirectSum.add_apply, dh_add]
    exact T.add_mem (hp e) (hq e)
  | smul c p _ hp =>
    intro e

    have hc : c = ∑ a ∈ (DirectSum.decompose 𝒜 c).support,
        ((DirectSum.decompose 𝒜 c) a : MvPolynomial (Fin (n + 1)) R) :=
      (DirectSum.sum_support_decompose 𝒜 c).symm
    rw [smul_eq_mul, hc, Finset.sum_mul, decompose_sum_apply, dh_sum]
    refine T.sum_mem fun a _ => ?_
    by_cases hae : a ≤ e
    · rw [dh_mul' n i (Nat.add_sub_cancel' hae) ((DirectSum.decompose 𝒜 c) a) ((DirectSum.decompose 𝒜 p) (e - a))
        _ (by rw [DirectSum.coe_decompose_mul_of_left_mem 𝒜 e ((DirectSum.decompose 𝒜 c) a).2, if_pos hae])]
      exact T.mul_mem_left _ (hp (e - a))
    · rw [dh_eq_zero n i
        (by rw [DirectSum.coe_decompose_mul_of_left_mem 𝒜 e ((DirectSum.decompose 𝒜 c) a).2, if_neg hae])]
      exact T.zero_mem

theorem decompose_of_isHomogeneous {d : ℕ} {F : MvPolynomial (Fin (n + 1)) R} (hF : F.IsHomogeneous d) :
    DirectSum.decompose 𝒜 F d = ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ :=
  Subtype.ext (DirectSum.decompose_of_mem_same 𝒜 ((MvPolynomial.mem_homogeneousSubmodule d F).mpr hF))

end Dehom

section Map

variable (n : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (i : Fin (n + 1))

local notation "𝒜A" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A
local notation "𝒜B" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B
local notation "φ" => MvPolynomial.map (algebraMap A B)

theorem homogeneousComponent_map (e : ℕ) (p : MvPolynomial (Fin (n + 1)) A) :
    homogeneousComponent e (φ p) = φ (homogeneousComponent e p) := by
  ext m
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp

theorem coe_decompose_map (e : ℕ) (p : MvPolynomial (Fin (n + 1)) A) :
    ((DirectSum.decompose 𝒜B (φ p)) e : MvPolynomial (Fin (n + 1)) B) =
      φ ((DirectSum.decompose 𝒜A p) e : MvPolynomial (Fin (n + 1)) A) := by
  rw [coe_decompose, coe_decompose, homogeneousComponent_map]

theorem basicOpen_le_preimage :
    Proj.basicOpen 𝒜B (X i) ≤ ProjSpace.map A B n ⁻¹ᵁ Proj.basicOpen 𝒜A (X i) := by
  rw [ProjSpace.map_eq, Proj.map_preimage_basicOpen, ProjSpace.mvMapGraded_X]

private theorem _root_.AlgebraicGeometry.ProjSpace.BCComap.map_mem (e : ℕ) (G : 𝒜A e) : φ (G : MvPolynomial (Fin (n + 1)) A) ∈ 𝒜B e :=
  (ProjSpace.mvMapGraded A B n).map_mem G.2

p2m_export "AlgebraicGeometry.ProjSpace.BCComap" "map_mem"

theorem appLE_dh (e : ℕ) (G : 𝒜A e) :
    (ProjSpace.map A B n).appLE (Proj.basicOpen 𝒜A (X i)) (Proj.basicOpen 𝒜B (X i))
        (basicOpen_le_preimage n A B i) (dh n i e G) =
      dh n i e ⟨φ (G : MvPolynomial (Fin (n + 1)) A), map_mem n A B e G⟩ := by

  have H : ∀ (t : MvPolynomial (Fin (n + 1)) B) (ht : ProjSpace.mvMapGraded A B n (X i) = t)
      (hle : Proj.basicOpen 𝒜B t ≤ ProjSpace.map A B n ⁻¹ᵁ Proj.basicOpen 𝒜A (X i)),
      (ProjSpace.map A B n).appLE (Proj.basicOpen 𝒜A (X i)) (Proj.basicOpen 𝒜B t) hle (dh n i e G) =
        Proj.awayToSection 𝒜B t
          (HomogeneousLocalization.mk (x := Submonoid.powers t)
            { deg := e
              num := ⟨φ (G : MvPolynomial (Fin (n + 1)) A), map_mem n A B e G⟩
              den := ⟨φ ((X i : MvPolynomial (Fin (n + 1)) A) ^ e),
                (ProjSpace.mvMapGraded A B n).map_mem (X_pow_mem n i e)⟩
              den_mem := ⟨e, by rw [← ht]; exact (map_pow _ _ _).symm⟩ }) := by
    intro t ht hle
    subst ht
    have h := ConcreteCategory.congr_hom
      (Proj.awayToSection_comp_appLE (ProjSpace.mvMapGraded A B n)
        (ProjSpace.irrelevant_le_map_mvMapGraded A B n) (ProjSpace.X_mem_one A n i))
      (HomogeneousLocalization.mk (𝒜 := 𝒜A) (x := Submonoid.powers (X i))
        { deg := e, num := G, den := ⟨X i ^ e, X_pow_mem n i e⟩, den_mem := ⟨e, rfl⟩ })
    exact h
  rw [H (X i) (ProjSpace.mvMapGraded_X A B n i) (basicOpen_le_preimage n A B i)]
  unfold dh
  congr 1
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mk]
  congr 1
  exact Subtype.ext (by simp)

end Map

end AlgebraicGeometry.ProjSpace.BCComap

end

p2m_open "MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span.AlgebraicGeometry AlgebraicGeometry.HilbertFunctor"

theorem solution
    (n : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal (MvPolynomial (Fin (n + 1)) A))
    (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I)
    (𝓘 : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)).IdealSheafData)
    (h𝓘 : ∀ i : Fin (n + 1),
        𝓘.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i) (ProjSpace.X_mem_one A n i) one_pos⟩ =
        Ideal.span { s | ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
          F ∈ I ∧
          s = (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                  den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) })
    (𝓙 : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)).IdealSheafData)
    (h𝓙 : ∀ i : Fin (n + 1),
        𝓙.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B) (X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B) (X i) (ProjSpace.X_mem_one B n i) one_pos⟩ =
        Ideal.span { s | ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) B) (hF : F.IsHomogeneous d),
          F ∈ I.map (MvPolynomial.map (algebraMap A B)) ∧
          s = (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B) (X i))
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                  den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) }) :
    𝓙 = 𝓘.comap (ProjSpace.map A B n) := by
  open AlgebraicGeometry.ProjSpace.BCComap in
  classical

  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun i : Fin (n + 1) => ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B) (X i),
      Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B) (X i)
        (ProjSpace.X_mem_one B n i) one_pos⟩)
    (Proj.iSup_basicOpen_eq_top _ (fun j => X j) (ProjSpace.irrelevant_le_span_X B n)) fun i => ?_
  rw [h𝓙 i, AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_le 𝓘 (ProjSpace.map A B n)
    ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i),
      Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i)
        (ProjSpace.X_mem_one A n i) one_pos⟩ _
    (AlgebraicGeometry.ProjSpace.BCComap.basicOpen_le_preimage n A B i), h𝓘 i, Ideal.map_span]
  apply le_antisymm
  ·
    refine Ideal.span_le.mpr ?_
    rintro s ⟨d, F, hF, hFI, rfl⟩
    change AlgebraicGeometry.ProjSpace.BCComap.dh n i d ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ ∈ _
    rw [← AlgebraicGeometry.ProjSpace.BCComap.decompose_of_isHomogeneous n hF]
    refine AlgebraicGeometry.ProjSpace.BCComap.dh_decompose_mem_of_mem_span n i
      ((MvPolynomial.map (algebraMap A B)) '' (I : Set (MvPolynomial (Fin (n + 1)) A))) _ ?_ hFI d
    rintro _ ⟨p, hp, rfl⟩ e
    have h1 : AlgebraicGeometry.ProjSpace.BCComap.dh n i e
        (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)
          (MvPolynomial.map (algebraMap A B) p) e) =
        (ProjSpace.map A B n).appLE (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
          (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B) (X i))
          (AlgebraicGeometry.ProjSpace.BCComap.basicOpen_le_preimage n A B i)
          (AlgebraicGeometry.ProjSpace.BCComap.dh n i e ⟨homogeneousComponent e p,
            (MvPolynomial.mem_homogeneousSubmodule e _).mpr (homogeneousComponent_isHomogeneous e p)⟩) := by
      rw [AlgebraicGeometry.ProjSpace.BCComap.appLE_dh]
      exact AlgebraicGeometry.ProjSpace.BCComap.dh_congr n i
        (by rw [AlgebraicGeometry.ProjSpace.BCComap.coe_decompose_map, AlgebraicGeometry.ProjSpace.BCComap.coe_decompose])
    rw [h1]
    exact Ideal.subset_span ⟨_, ⟨e, _, homogeneousComponent_isHomogeneous e p, hI p hp e, rfl⟩, rfl⟩
  ·
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨s, ⟨d, F, hF, hFI, rfl⟩, rfl⟩
    refine Ideal.subset_span ⟨d, MvPolynomial.map (algebraMap A B) F, hF.map _, Ideal.mem_map_of_mem _ hFI, ?_⟩
    have := AlgebraicGeometry.ProjSpace.BCComap.appLE_dh n A B i d
      ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
    simp only [AlgebraicGeometry.ProjSpace.BCComap.dh] at this
    exact this

end S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span (solution)
