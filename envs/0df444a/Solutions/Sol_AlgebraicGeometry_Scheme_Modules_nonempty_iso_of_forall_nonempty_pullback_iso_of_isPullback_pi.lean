-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.nonempty_iso_of_forall_nonempty_pullback_iso_of_isPullback_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/3d666460-fd28-5c5b-ad73-b8d44072ee5c

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_existsUnique_map_pullback_eq_of_iSup_eq_top_of_disjoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_iso_of_forall_nonempty_pullback_iso_of_isPullback_pi

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace ClopenGlue29

variable {k : ℕ} (C : Fin k → Type u) [∀ i, CommRing (C i)]

def idem (i : Fin k) : (∀ j, C j) := Function.update 0 i 1

theorem idem_mul_idem_of_ne {i j : Fin k} (h : i ≠ j) : idem C i * idem C j = 0 := by
  ext l; simp only [idem, Pi.mul_apply, Pi.zero_apply, Function.update_apply]
  by_cases hl : l = i
  · subst hl; simp [h]
  · simp [hl]

theorem sum_idem : ∑ i, idem C i = 1 := by
  classical
  ext l
  rw [Finset.sum_apply, Finset.sum_eq_single_of_mem l (Finset.mem_univ l)
    (fun c _ hc => by simp only [idem]; rw [Function.update_of_ne (Ne.symm hc)]; rfl)]
  simp [idem]

theorem span_idem_eq_top : Ideal.span (Set.range (idem C)) = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← sum_idem C]
  exact Ideal.sum_mem _ fun i _ => Ideal.subset_span ⟨i, rfl⟩

theorem isLocalizationAway (i : Fin k) :
    letI := (Pi.evalRingHom C i).toAlgebra
    IsLocalization.Away (idem C i) (C i) := by
  classical
  letI := (Pi.evalRingHom C i).toAlgebra
  apply IsLocalization.away_of_isIdempotentElem_of_mul
  · ext j; by_cases h : j = i <;> aesop (add simp idem)
  · intro x y
    constructor
    · intro e; ext j; by_cases h : j = i <;> aesop (add simp idem)
    · intro e; (have h__af := congr_fun e i; simp [idem] at h__af; exact h__af)
  · exact Function.surjective_eval _

theorem opensRange_specMap_eval (i : Fin k) :
    (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))).opensRange =
      (PrimeSpectrum.basicOpen (idem C i) : (Spec (CommRingCat.of (∀ j, C j))).Opens) := by
  letI := (Pi.evalRingHom C i).toAlgebra
  haveI := isLocalizationAway C i
  exact TopologicalSpace.Opens.ext (PrimeSpectrum.localization_away_comap_range (C i) (idem C i))

variable {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of (∀ i, C i)))

noncomputable def U (i : Fin k) : X.Opens := g ⁻¹ᵁ (PrimeSpectrum.basicOpen (idem C i))

theorem iSup_U : ⨆ i, U C g i = ⊤ := by
  apply top_le_iff.mp
  intro x _
  let y : PrimeSpectrum (∀ j, C j) := g x
  have hx : y ∈ (⨆ i, PrimeSpectrum.basicOpen (idem C i)) := by
    rw [PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr (span_idem_eq_top C)]; exact TopologicalSpace.Opens.mem_top y
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩

theorem U_disjoint (i j : Fin k) (h : i ≠ j) : U C g i ⊓ U C g j = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hi, hj⟩
  exfalso
  let y : PrimeSpectrum (∀ j, C j) := g x
  change y ∈ PrimeSpectrum.basicOpen (idem C i) at hi
  change y ∈ PrimeSpectrum.basicOpen (idem C j) at hj
  rw [PrimeSpectrum.mem_basicOpen] at hi hj
  have h0 : idem C i * idem C j ∈ y.asIdeal := by rw [idem_mul_idem_of_ne C h]; exact Ideal.zero_mem _
  rcases y.isPrime.mem_or_mem h0 with h' | h'
  · exact hi h'
  · exact hj h'

noncomputable def compIso {A B D : Scheme.{u}} {p : A ⟶ B} {q : B ⟶ D} {r : A ⟶ D} (h : p ≫ q = r) (M : D.Modules) :
    (Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj M) ≅ (Scheme.Modules.pullback r).obj M :=
  (Scheme.Modules.pullbackComp p q).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M

theorem exists_iso_piece {i : Fin k} {Xi : Scheme.{u}} (gi : Xi ⟶ Spec (CommRingCat.of (C i))) (v : Xi ⟶ X)
    (hv : IsPullback v gi g (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i)))) :
    ∃ ψ : Xi ≅ (U C g i : Scheme.{u}), ψ.hom ≫ (U C g i).ι = v := by
  have hr : Set.range (pullback.fst g (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i)))) = Set.range (U C g i).ι := by
    rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange, opensRange_specMap_eval]; rfl
  refine ⟨hv.isoPullback ≪≫ IsOpenImmersion.isoOfRangeEq _ _ hr, ?_⟩
  rw [Iso.trans_hom, Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, IsPullback.isoPullback_hom_fst]

end ClopenGlue29

open ClopenGlue29 in
theorem solution
    {k : ℕ} (C : Fin k → Type u) [∀ i, CommRing (C i)]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of (∀ i, C i)))
    {Xi : Fin k → Scheme.{u}} (gi : ∀ i, Xi i ⟶ Spec (CommRingCat.of (C i))) (v : ∀ i, Xi i ⟶ X)
    (hv : ∀ i, IsPullback (v i) (gi i) g (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))))
    (M N : X.Modules)
    (h : ∀ i, Nonempty ((Scheme.Modules.pullback (v i)).obj M ≅ (Scheme.Modules.pullback (v i)).obj N)) :
    Nonempty (M ≅ N) := by
  classical

  have key : ∀ i : Fin k, Nonempty ((Scheme.Modules.pullback (ClopenGlue29.U C g i).ι).obj M ≅
      (Scheme.Modules.pullback (ClopenGlue29.U C g i).ι).obj N) := fun i => by
    obtain ⟨ψ, hψ⟩ := ClopenGlue29.exists_iso_piece C g (gi i) (v i) (hv i)
    have hι : ψ.inv ≫ v i = (ClopenGlue29.U C g i).ι := by rw [← hψ, Iso.inv_hom_id_assoc]
    obtain ⟨e⟩ := h i
    exact ⟨(ClopenGlue29.compIso hι M).symm ≪≫ (Scheme.Modules.pullback ψ.inv).mapIso e ≪≫ ClopenGlue29.compIso hι N⟩
  let e := fun i => (key i).some
  obtain ⟨Φ, hΦ, -⟩ := AlgebraicGeometry.Scheme.Modules.existsUnique_map_pullback_eq_of_iSup_eq_top_of_disjoint
    (ClopenGlue29.U C g) (ClopenGlue29.iSup_U C g) (ClopenGlue29.U_disjoint C g) M N (fun i => (e i).hom)
  obtain ⟨Ψ, hΨ, -⟩ := AlgebraicGeometry.Scheme.Modules.existsUnique_map_pullback_eq_of_iSup_eq_top_of_disjoint
    (ClopenGlue29.U C g) (ClopenGlue29.iSup_U C g) (ClopenGlue29.U_disjoint C g) N M (fun i => (e i).inv)
  have h1 := (AlgebraicGeometry.Scheme.Modules.existsUnique_map_pullback_eq_of_iSup_eq_top_of_disjoint
    (ClopenGlue29.U C g) (ClopenGlue29.iSup_U C g) (ClopenGlue29.U_disjoint C g) M M (fun i => 𝟙 _)).unique
    (y₁ := Φ ≫ Ψ) (y₂ := 𝟙 M)
    (fun i => by rw [Functor.map_comp, hΦ, hΨ, Iso.hom_inv_id]) (fun i => by rw [CategoryTheory.Functor.map_id])
  have h2 := (AlgebraicGeometry.Scheme.Modules.existsUnique_map_pullback_eq_of_iSup_eq_top_of_disjoint
    (ClopenGlue29.U C g) (ClopenGlue29.iSup_U C g) (ClopenGlue29.U_disjoint C g) N N (fun i => 𝟙 _)).unique
    (y₁ := Ψ ≫ Φ) (y₂ := 𝟙 N)
    (fun i => by rw [Functor.map_comp, hΨ, hΦ, Iso.inv_hom_id]) (fun i => by rw [CategoryTheory.Functor.map_id])
  exact ⟨⟨Φ, Ψ, h1, h2⟩⟩

end S_AlgebraicGeometry_Scheme_Modules_nonempty_iso_of_forall_nonempty_pullback_iso_of_isPullback_pi
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_iso_of_forall_nonempty_pullback_iso_of_isPullback_pi (solution)
