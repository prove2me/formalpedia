-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_append_homogeneousIdeal
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:40.587113+00:00
-- url     : https://prove2.me/submissions/6ab69ddd-7993-4f3c-9faa-33a8ebeec10a

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_append
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isProper_toProj_of_isFinite
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_pointProjectivization_eq_mk_comp_of_sections_eq
import Theorems.Thm_AlgebraicGeometry_Proj_zeroLocus_vanishingIdeal_sup_span_eq_zero
import Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointOfVec_mem_homogeneousIdeal_iff_eval
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints
import Theorems.Thm_MvPolynomial_exists_rename_homogeneousIdeal
import Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointOfVec_surjective
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

theorem _root_.solution {K : Type} [Field K] [NumberField K]
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)} {M₁ M₂ : X.Modules} {N₁ N₂ : ℕ}
    (P₁ : M₁.ProjPresentation f N₁) (P₂ : M₂.ProjPresentation f N₂) (e : M₁ ≅ M₂)
    (hfin : IsFinite P₁.toProj) :
    ∃ I : HomogeneousIdeal
        (MvPolynomial.homogeneousSubmodule (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) K),
      (∀ z : (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) → AlgebraicClosure K,
        z ∈ MvPolynomial.zeroLocus (AlgebraicClosure K)
          (I.toIdeal ⊔ Ideal.span (Set.range
            (fun i : Fin (N₁ + 1) =>
              (MvPolynomial.X (Sum.inl i) :
                MvPolynomial (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) K)))) → z = 0) ∧
      (∀ z : (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) → AlgebraicClosure K,
        z ∈ MvPolynomial.zeroLocus (AlgebraicClosure K)
          (I.toIdeal ⊔ Ideal.span (Set.range
            (fun j : Fin (N₂ + 1) =>
              (MvPolynomial.X (Sum.inr j) :
                MvPolynomial (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) K)))) → z = 0) ∧
      ∀ x : Scheme.KPoint f,
        ∃ (z : (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) → K)
            (h₁ : z ∘ Sum.inl ≠ 0) (h₂ : z ∘ Sum.inr ≠ 0),
          P₁.pointProjectivization x = Projectivization.mk K (z ∘ Sum.inl) h₁ ∧
          P₂.pointProjectivization x = Projectivization.mk K (z ∘ Sum.inr) h₂ ∧
          ∀ p ∈ I.toIdeal, MvPolynomial.eval z p = 0  := by
  classical
  let η : Fin (N₁ + N₂ + 1 + 1) ≃ (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) :=
    (finCongr (by omega)).trans finSumFinEquiv.symm
  obtain ⟨Q, hσ, hU₁, hU₂⟩ := exists_append P₁ P₂ e η
  letI : IsProper Q.toProj := isProper_toProj_of_isFinite P₁ Q hfin
  let V : Set (ProjectiveSpectrum
      (MvPolynomial.homogeneousSubmodule (Fin (N₁ + N₂ + 1 + 1)) K)) :=
    Set.range Q.toProj
  have hV : IsClosed V := Q.toProj.isClosedMap.isClosed_range
  let I := ProjectiveSpectrum.vanishingIdeal V
  obtain ⟨J, hJ⟩ := MvPolynomial.exists_rename_homogeneousIdeal η I
  have hzero {T : Type} [Fintype T]
      (inc : T → (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)))
      (hcover : ∀ a : X, ∃ i : T, Q.toProj a ∈
        Proj.basicOpen _ (MvPolynomial.X (η.symm (inc i)))) :
      ∀ z : (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) → AlgebraicClosure K,
        z ∈ MvPolynomial.zeroLocus (AlgebraicClosure K)
          (J.toIdeal ⊔ Ideal.span (Set.range
            (fun i : T => (MvPolynomial.X (inc i) :
              MvPolynomial (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) K)))) → z = 0 := by
    intro z hz
    let B : Ideal (MvPolynomial (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) K) :=
      Ideal.span (Set.range (fun i : T => MvPolynomial.X (inc i)))
    have hleft : J.toIdeal ≤ J.toIdeal ⊔ B := le_sup_left
    have hright : B ≤ J.toIdeal ⊔ B := le_sup_right
    have hvan : ∀ p ∈ I.toIdeal,
        MvPolynomial.aeval (z ∘ η) p = 0 :=
      (hJ (AlgebraicClosure K) (algebraMap K (AlgebraicClosure K)) z).mp
        (fun p hp => hz p (hleft hp))
    have hz' : z ∘ η ∈ MvPolynomial.zeroLocus (AlgebraicClosure K)
        (I.toIdeal ⊔ Ideal.span (Set.range
          (fun i : T => (MvPolynomial.X (η.symm (inc i)) :
            MvPolynomial (Fin (N₁ + N₂ + 1 + 1)) K)))) := by
      change I.toIdeal ⊔ Ideal.span _ ≤
        RingHom.ker (MvPolynomial.aeval (z ∘ η)).toRingHom
      refine sup_le hvan (Ideal.span_le.mpr ?_)
      rintro p ⟨i, rfl⟩
      have hi := hz (MvPolynomial.X (inc i)) (hright (Ideal.subset_span ⟨i, rfl⟩))
      change MvPolynomial.aeval (R := K) (z ∘ η) (MvPolynomial.X (η.symm (inc i))) = 0
      simpa only [MvPolynomial.aeval_X, Function.comp_apply, Equiv.apply_symm_apply] using hi
    have heq := Proj.zeroLocus_vanishingIdeal_sup_span_eq_zero
      V hV (fun i => η.symm (inc i))
      (by rintro y ⟨a, rfl⟩; exact hcover a) (z ∘ η) hz'
    funext k
    have hk := congrFun heq (η.symm k)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply, Pi.zero_apply] using hk
  have hchart {M : X.Modules} {N : ℕ} (P : M.ProjPresentation f N) (a : X) :
      ∃ i, P.toProj a ∈ Proj.basicOpen _ (MvPolynomial.X i) := by
    have hc := Proj.iSup_basicOpen_eq_top
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
      (fun i : Fin (N + 1) => MvPolynomial.X i) (ProjSpace.irrelevant_le_span_X K N)
    have ha : P.toProj a ∈ (⨆ i : Fin (N + 1),
        Proj.basicOpen _ (MvPolynomial.X i)) := by rw [hc]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp ha
  refine ⟨J, hzero Sum.inl ?_, hzero Sum.inr ?_, ?_⟩
  · intro a
    obtain ⟨i, hi⟩ := hchart P₁ a
    exact ⟨i, hU₁ i hi⟩
  · intro a
    obtain ⟨i, hi⟩ := hchart P₂ a
    exact ⟨i, hU₂ i hi⟩
  · intro x
    let y : Scheme.KPoint (ProjSpace.π K (N₁ + N₂ + 1)) :=
      ⟨x.1 ≫ Q.toProj, by rw [Category.assoc, Q.toProj_π]; exact x.2⟩
    obtain ⟨v, hv, hpoint⟩ := ProjSpace.kPointOfVec_surjective K (N₁ + N₂ + 1) y
    have hvpoint : (ProjSpace.kPointOfVec K (N₁ + N₂ + 1) v hv).1 =
        x.1 ≫ Q.toProj := congrArg Subtype.val hpoint
    obtain ⟨h₁, hp₁⟩ := pointProjectivization_eq_mk_comp_of_sections_eq
      P₁ Q (Iso.refl M₁) (fun i => η.symm (Sum.inl i))
      (by intro i; simpa using (hσ (η.symm (Sum.inl i))).symm) hU₁ x v hv hvpoint
    obtain ⟨h₂, hp₂⟩ := pointProjectivization_eq_mk_comp_of_sections_eq
      P₂ Q e.symm (fun i => η.symm (Sum.inr i))
      (by intro i; simpa using (hσ (η.symm (Sum.inr i))).symm) hU₂ x v hv hvpoint
    let z : (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) → K := v ∘ η.symm
    refine ⟨z, h₁, h₂, hp₁, hp₂, ?_⟩
    apply (hJ K (RingHom.id K) z).mpr
    have hvan : ∀ p ∈ I.toIdeal, MvPolynomial.eval v p = 0 := by
      apply (ProjSpace.kPointOfVec_mem_homogeneousIdeal_iff_eval v hv I).mp
      intro p hp
      apply (ProjectiveSpectrum.mem_vanishingIdeal V p).mp hp
      rw [hvpoint]
      exact ⟨x.1 (IsLocalRing.closedPoint K), rfl⟩
    intro p hp
    change MvPolynomial.eval (z ∘ η) p = 0
    simpa only [z, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
      using hvan p hp

end AlgebraicGeometry.Scheme.Modules.ProjPresentation
