-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineLeOrDisjoint
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineLeOrDisjoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:56.463975+00:00
-- url     : https://prove2.me/theorems/fb4d78e6-72bc-4ab8-a68b-aaed5ba5be16
-- title:
--   Exists Affine Le Or Disjoint
-- statement:
--   Definitions and structural lemmas for Exists Affine Le Or Disjoint, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineLeOrDisjoint.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace GlobalTheory.DenseClosedAffineSubsets
instance dominant_restrict {V X : Scheme.{0}} (j : V ⟶ X) [IsSchemeTheoreticallyDominant j]
    [QuasiCompact j] (O : X.Opens) : IsSchemeTheoreticallyDominant (j ∣_ O) :=
  IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict j O).flip
instance dominant_toImage {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens ↦ ⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage _⟩) ?_ fun U ↦ ?_
  · change ⨆ U : Y.affineOpens, f.imageι ⁻¹ᵁ U.1 = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  · rw [Scheme.Hom.ker_apply]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (f.toImage_app_injective U)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] MvPolynomial.gradedAlgebra
theorem surjective_algebraMap_zero (R : Type) [CommRing R] (N : ℕ) :
    Function.Surjective
      (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)) := by
  rintro ⟨p, hp⟩
  rw [MvPolynomial.mem_homogeneousSubmodule, ← MvPolynomial.totalDegree_zero_iff_isHomogeneous,
    MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hp
  exact ⟨p.coeff 0, Subtype.ext hp.symm⟩
theorem adjoin_X (R : Type) [CommRing R] (N : ℕ) :
    Algebra.adjoin ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)
      (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) R)) = ⊤ := by
  refine top_le_iff.mp fun p _ ↦ ?_
  induction p using MvPolynomial.induction_on with
  | C a =>
    exact Subalgebra.algebraMap_mem _
      (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) a)
  | add p q hp hq => exact add_mem (hp trivial) (hq trivial)
  | mul_X p i hp => exact mul_mem (hp trivial) (Algebra.subset_adjoin ⟨i, rfl⟩)
instance isProper_str (R : Type) [CommRing R] (N : ℕ) : IsProper (PSpace.str R N) := by
  have : Algebra.FiniteType ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)
      (MvPolynomial (Fin (N + 1)) R) :=
    ⟨⟨(Set.finite_range MvPolynomial.X).toFinset, by
      rw [Set.Finite.coe_toFinset]; exact adjoin_X R N⟩⟩
  have : IsClosedImmersion
      (spMap (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0))) :=
    IsClosedImmersion.spec_of_surjective _ (surjective_algebraMap_zero R N)
  unfold PSpace.str
  infer_instance
def sec {A : Type} [CommRing A] {σ : Type} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
    [GradedRing 𝒜] (t : A) (z : HomogeneousLocalization.Away 𝒜 t) :
    Γ((Proj.basicOpen 𝒜 t).toScheme, ⊤) :=
  (Proj.basicOpenToSpec 𝒜 t).appTop ((Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away 𝒜 t))).inv z)
end GlobalTheory.DenseClosedAffineSubsets


