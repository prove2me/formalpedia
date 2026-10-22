-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_KoszulAugmentationNaturality_Defs
-- name    : LPCA_Solutions_LPCA_KoszulAugmentationNaturality_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:42:47.957311+00:00
-- url     : https://prove2.me/theorems/01cc2161-138b-4498-8237-1f6507be433d
-- title:
--   Koszul Augmentation Naturality for localized persistent commutative algebra
-- statement:
--   This bundle supplies koszul Augmentation Naturality for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The actual quotient map corresponding to the inclusion J_m ≤ J_n.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_KoszulAugmentationNaturality.lean, selected declarations in lines 14–38; source SHA-256 a2fe64dee528221496def9ba27945372082b9d0d2b5d97417d43d0a8e81315ae; source certificate Sapelo2 job 49172236.

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
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulAugmentation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
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

/-- The actual quotient map corresponding to the inclusion J_m ≤ J_n. -/
noncomputable def coordinatePowerQuotientMap
    (n m : ℕ) (hnm : n ≤ m) (T : Finset V) :
    (MvPolynomial V k ⧸ coordinatePowerIdeal k T m) →ₗ[MvPolynomial V k]
      (MvPolynomial V k ⧸ coordinatePowerIdeal k T n) :=
  (Ideal.Quotient.factorₐ (MvPolynomial V k)
    (coordinatePowerIdeal_antitone k T hnm)).toLinearMap



theorem coordinateKoszulTransition_zero (n m : ℕ) (T : Finset V) :
    coordinateKoszulTransition k n m T 0 = LinearMap.id := by
  ext y F
  have hF : F.1 = ∅ := Finset.card_eq_zero.mp F.2.2
  simp [coordinateKoszulTransition, polynomialFaceMonomial, hF]

theorem coordinateKoszulTransition_augmentation
    (n m : ℕ) (hnm : n ≤ m) (T : Finset V) :
    (coordinateKoszulAugmentation k n T).comp (coordinateKoszulTransition k n m T 0) =
      (coordinatePowerQuotientMap k n m hnm T).comp (coordinateKoszulAugmentation k m T) := by
  rw [coordinateKoszulTransition_zero, LinearMap.comp_id]
  rfl



end LPCA


