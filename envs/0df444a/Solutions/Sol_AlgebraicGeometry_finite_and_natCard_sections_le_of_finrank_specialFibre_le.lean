-- Prove2me | solution 1 for AlgebraicGeometry.finite_and_natCard_sections_le_of_finrank_specialFibre_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/b0941109-1745-583c-a568-a27f77ea4f64

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_exists_isFinite_isOpenImmersion_disjoint_cover_of_locallyQuasiFinite_of_henselianLocalRing
import Theorems.Thm_AlgebraicGeometry_exists_section_comp_eq_iff_factors_of_universallyClosed_of_valuationRing
import Theorems.Thm_AlgebraicGeometry_finite_and_natCard_le_finrank_tensorProduct_sections_of_isFinite
import Theorems.Thm_AlgebraicGeometry_finrank_sections_eq_finrank_tensorProduct_of_isPullback_residue_of_isFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_finite_and_natCard_sections_le_of_finrank_specialFibre_le

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X Y : Scheme.{u}} (g : X ⟶ Spec (.of R))
    [LocallyOfFiniteType g] [LocallyQuasiFinite g] [IsSeparated g] [QuasiCompact g]
    (q : Y ⟶ Spec (.of (IsLocalRing.ResidueField R))) (π : Y ⟶ X)
    (hY : IsPullback π q g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (B : ℕ)
    (hB : letI := Scheme.TwoAffineOpenCover.algebraOfHom q ⊤
      Module.Finite (IsLocalRing.ResidueField R) Γ(Y, ⊤) ∧
        Module.finrank (IsLocalRing.ResidueField R) Γ(Y, ⊤) ≤ B) :
    Finite {s : Spec (.of R) ⟶ X // s ≫ g = 𝟙 _} ∧ Nat.card {s : Spec (.of R) ⟶ X // s ≫ g = 𝟙 _} ≤ B := by
  classical

  obtain ⟨Xf, X', i, j, hi, hj, hfin, hcover, -, hempty⟩ :=
    exists_isFinite_isOpenImmersion_disjoint_cover_of_locallyQuasiFinite_of_henselianLocalRing g
  haveI := hi
  haveI := hfin

  have hfac : ∀ s : {s : Spec (.of R) ⟶ X // s ≫ g = 𝟙 _},
      ∃ xf : Spec (.of K) ⟶ Xf, xf ≫ i = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s.1 := fun s =>
    (exists_section_comp_eq_iff_factors_of_universallyClosed_of_valuationRing R K g i j hcover hempty
      (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s.1)
      (by rw [Category.assoc, s.2, Category.comp_id])).mp ⟨s.1, s.2, rfl⟩
  choose xf hxf using hfac

  let Φ : {s : Spec (.of R) ⟶ X // s ≫ g = 𝟙 _} →
      {x : Spec (.of K) ⟶ Xf // x ≫ i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R K))} :=
    fun s => ⟨xf s, by rw [← Category.assoc, hxf s, Category.assoc, s.2, Category.comp_id]⟩
  have hker : RingHom.ker (algebraMap R K) ≤ nilradical R := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R K)]
    exact bot_le
  haveI hdom : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr hker⟩
  have hΦ : Function.Injective Φ := by
    intro s s' h
    have h' : xf s = xf s' := congrArg Subtype.val h
    apply Subtype.ext
    refine ext_of_isDominant_of_isSeparated g (s.2.trans s'.2.symm)
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) ?_
    rw [← hxf s, ← hxf s', h']

  obtain ⟨hfinΩ, -, hle⟩ := finite_and_natCard_le_finrank_tensorProduct_sections_of_isFinite g i K
  obtain ⟨-, heq⟩ := finrank_sections_eq_finrank_tensorProduct_of_isPullback_residue_of_isFinite g i j hcover hempty q π hY
  haveI := hfinΩ
  refine ⟨Finite.of_injective Φ hΦ, ?_⟩
  calc Nat.card {s : Spec (.of R) ⟶ X // s ≫ g = 𝟙 _}
      ≤ Nat.card {x : Spec (.of K) ⟶ Xf // x ≫ i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R K))} :=
        Nat.card_le_card_of_injective Φ hΦ
    _ ≤ _ := hle
    _ = _ := heq.symm
    _ ≤ B := hB.2

end S_AlgebraicGeometry_finite_and_natCard_sections_le_of_finrank_specialFibre_le
end P2MW
export P2MW.S_AlgebraicGeometry_finite_and_natCard_sections_le_of_finrank_specialFibre_le (solution)
