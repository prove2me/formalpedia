-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulAugmentation_Defs
-- name    : LPCA_Solutions_LPCA_CoordinateKoszulAugmentation_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:39:23.157194+00:00
-- url     : https://prove2.me/theorems/0f843ed4-a5de-4705-82f1-c1f8f7d04c4d
-- title:
--   Coordinate Koszul Augmentation for localized persistent commutative algebra
-- statement:
--   This bundle supplies coordinate Koszul Augmentation for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The genuine augmentation to the coordinate-power quotient concentrated in degree zero. Its being a quasi-isomorphism is still a separate theorem.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_CoordinateKoszulAugmentation.lean, selected declarations in lines 14–71; source SHA-256 3a3dea6c158f79f929287ef3397573895bfa8e968c2a196321e3ef1faa4790e1; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_dd_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_exists_insert_of_inc_ne_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_hc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_sdiff_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_erase_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_gt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_lt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_sdiff_add_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false

namespace LPCA

open CategoryTheory

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

noncomputable def coordinateKoszulAugmentation (n : ℕ) (T : Finset V) :
    CoordinateKoszulTerm k T 0 →ₗ[MvPolynomial V k]
      MvPolynomial V k ⧸ coordinatePowerIdeal k T n :=
  (coordinatePowerIdeal k T n).mkQ.comp
    (LinearMap.proj (⟨∅, Finset.empty_subset T, by simp⟩ : CechSlot T 0))

theorem coordinateKoszulAugmentation_surjective (n : ℕ) (T : Finset V) :
    Function.Surjective (coordinateKoszulAugmentation k n T) := by
  intro z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨fun _ => r, rfl⟩

theorem coordinateKoszulCoefficient_empty_mem
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) (G : CechSlot T 1) :
    coordinateKoszulCoefficient k rank n ∅ G.1 ∈ coordinatePowerIdeal k T n := by
  classical
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp G.2.2
  have hjT : j ∈ T := G.2.1 (by rw [hj]; simp)
  rw [hj]
  have hcoef : coordinateKoszulCoefficient k rank n ∅ {j} =
      (MvPolynomial.X j : MvPolynomial V k) ^ (n + 1) := by
    simp [coordinateKoszulCoefficient, cechCoefficient]
  rw [hcoef]
  exact Ideal.subset_span ⟨j, hjT, rfl⟩

theorem coordinateKoszulDifferential_comp_augmentation
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) :
    (coordinateKoszulAugmentation k n T).comp
      (coordinateKoszulDifferential k rank n T 0) = 0 := by
  classical
  apply LinearMap.ext
  intro y
  change Ideal.Quotient.mk (coordinatePowerIdeal k T n)
    (∑ G : CechSlot T 1, coordinateKoszulCoefficient k rank n ∅ G.1 * y G) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Submodule.sum_mem
  intro G _
  exact (coordinatePowerIdeal k T n).mul_mem_right (y G)
    (coordinateKoszulCoefficient_empty_mem k rank n T G)

/-- The genuine augmentation to the coordinate-power quotient concentrated
in degree zero. Its being a quasi-isomorphism is still a separate theorem. -/
noncomputable def coordinateKoszulAugmentationMap
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) :
    coordinateKoszulComplex k rank n T ⟶
      (ChainComplex.single₀ (ModuleCat (MvPolynomial V k))).obj
        (ModuleCat.of (MvPolynomial V k) (MvPolynomial V k ⧸ coordinatePowerIdeal k T n)) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (coordinateKoszulAugmentation k n T), by
      rw [coordinateKoszulComplex_d]
      apply ModuleCat.hom_ext
      exact coordinateKoszulDifferential_comp_augmentation k rank n T⟩

theorem coordinateKoszulAugmentationMap_zero
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) :
    (coordinateKoszulAugmentationMap k rank n T).f 0 =
      ModuleCat.ofHom (coordinateKoszulAugmentation k n T) :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _





end LPCA


