-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_isImmersion_proj_comp_of_isImmersion_proj_of_finite_free
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/454d87bc-310f-54ff-bbfc-2f893c350bff

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_comp_of_isImmersion_proj_of_finite_free

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace FiniteBaseQPAux

theorem exists_isClosedImmersion_proj_of_finite (S : Type u) [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    [Module.Finite S S'] :
    ∃ (d : ℕ) (j : Spec (CommRingCat.of S') ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) S)),
      IsClosedImmersion j ∧ j ≫ ProjSpace.π S d = Spec.map (CommRingCat.ofHom (algebraMap S S')) := by
  classical
  obtain ⟨d, s, hs⟩ := Module.Finite.exists_fin (R := S) (M := S')

  let g : Fin (d + 1) → S' := Fin.cons 1 s
  let ev : MvPolynomial (Fin (d + 1)) S →+* S' := MvPolynomial.eval₂Hom (algebraMap S S') g
  have hev0 : ev (MvPolynomial.X 0) = 1 := by simp [ev, g]
  have hevs : ∀ i : Fin d, ev (MvPolynomial.X i.succ) = s i := by intro i; simp [ev, g]
  have hevC : ∀ r : S, ev (MvPolynomial.C r) = algebraMap S S' r := by intro r; simp [ev]
  have hunit : IsUnit (ev (MvPolynomial.X 0)) := isUnit_iff_exists_inv.mpr ⟨1, by rw [hev0, one_mul]⟩
  let evL : Localization.Away (MvPolynomial.X 0 : MvPolynomial (Fin (d + 1)) S) →+* S' :=
    Localization.awayLift ev (MvPolynomial.X 0) hunit
  let φ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) S) (MvPolynomial.X 0) →+* S' :=
    evL.comp (algebraMap _ (Localization.Away (MvPolynomial.X 0 : MvPolynomial (Fin (d + 1)) S)))
  have hφC : ∀ r : S, φ (algebraMap S _ r) = algebraMap S S' r := by
    intro r
    change evL ((algebraMap S (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) S)
      (MvPolynomial.X 0)) r).val) = _
    rw [ProjSpace.val_algebraMap]
    change Localization.awayLift ev (MvPolynomial.X 0) hunit (algebraMap _ _ (MvPolynomial.C r)) = _
    rw [Localization.awayLift, IsLocalization.Away.lift_eq, hevC]
  have hφratio : ∀ i : Fin d, φ (ProjSpace.ratio S d 0 i.succ) = s i := by
    intro i
    change evL (ProjSpace.ratio S d 0 i.succ).val = _
    rw [ProjSpace.ratio, HomogeneousLocalization.Away.val_mk]
    change Localization.awayLift ev (MvPolynomial.X 0) hunit (Localization.mk _ ⟨MvPolynomial.X 0 ^ 1, 1, rfl⟩) = _
    rw [Localization.awayLift_mk ev (MvPolynomial.X 0) _ 1 (by rw [hev0, one_mul]) 1, one_pow, mul_one, hevs]
  have hφsurj : Function.Surjective φ := by
    intro y
    have hy : y ∈ Submodule.span S (Set.range s) := by rw [hs]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := S)).mp hy
    refine ⟨∑ i, algebraMap S _ (c i) * ProjSpace.ratio S d 0 i.succ, ?_⟩
    rw [map_sum, ← hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hφC, hφratio, Algebra.smul_def]

  let j : Spec (CommRingCat.of S') ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) S) :=
    Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) S) (MvPolynomial.X 0) (ProjSpace.X_mem_one S d 0) one_pos
  have hjπ : j ≫ ProjSpace.π S d = Spec.map (CommRingCat.ofHom (algebraMap S S')) := by
    simp only [j, Category.assoc]
    rw [ProjSpace.awayι_comp_π, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    exact hφC r
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) := IsClosedImmersion.spec_of_surjective _ hφsurj
  haveI : Mono j := mono_comp _ _
  haveI : IsFinite (j ≫ ProjSpace.π S d) := by
    rw [hjπ, IsFinite.SpecMap_iff, CommRingCat.hom_ofHom]
    exact RingHom.finite_algebraMap.mpr inferInstance
  haveI : IsFinite j := IsFinite.of_comp j (ProjSpace.π S d)
  refine ⟨d, j, ?_, hjπ⟩
  exact (IsClosedImmersion.iff_isProper_and_mono j).mpr ⟨inferInstance, inferInstance⟩

end FiniteBaseQPAux

open FiniteBaseQPAux in
theorem solution
    (S : Type) [CommRing S] (S' : Type) [CommRing S'] [Algebra S S'] [Module.Finite S S'] [Module.Free S S']
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of S'))
    (hQP : ∃ (qpa : ℕ) (qpι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpa + 1)) S')),
      IsImmersion qpι ∧ qpι ≫ ProjSpace.π S' qpa = πX) :
    ∃ (qpn : ℕ) (qpι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) S)),
      IsImmersion qpι ∧ qpι ≫ ProjSpace.π S qpn = πX ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')) := by
  obtain ⟨n, ι, hι, hιπ⟩ := hQP
  haveI := hι
  obtain ⟨d, j, hj, hjπ⟩ := exists_isClosedImmersion_proj_of_finite S S'

  obtain ⟨K, ιK, -, hιK, hιKπ⟩ :=
    AlgebraicGeometry.exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
      (ProjSpace.π S n) (Spec.map (CommRingCat.ofHom (algebraMap S S'))) n (𝟙 _) inferInstance (Category.id_comp _)
      d j hj hjπ
  haveI := hιK

  have hpb := AlgebraicGeometry.ProjSpace.isPullback_map S S' n
  let e := hpb.isoPullback
  refine ⟨K, ι ≫ e.hom ≫ ιK, inferInstance, ?_⟩
  rw [Category.assoc, Category.assoc, hιKπ, ← Category.assoc e.hom, hpb.isoPullback_hom_fst,
    hpb.w, ← Category.assoc, hιπ]

end S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_comp_of_isImmersion_proj_of_finite_free
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_comp_of_isImmersion_proj_of_finite_free (solution)
