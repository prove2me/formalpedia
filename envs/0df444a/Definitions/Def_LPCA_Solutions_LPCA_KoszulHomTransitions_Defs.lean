-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_KoszulHomTransitions_Defs
-- name    : LPCA_Solutions_LPCA_KoszulHomTransitions_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:42:30.28478+00:00
-- url     : https://prove2.me/theorems/76ea5415-2608-496b-b56e-2b37530d9ffe
-- title:
--   Koszul Hom Transitions for localized persistent commutative algebra
-- statement:
--   This bundle supplies koszul Hom Transitions for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The actual Hom transition is multiplication by x_F^(m-n) on the F column. Thus adjacent stages give the previously constructed localization telescope.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_KoszulHomTransitions.lean, selected declarations in lines 15–42; source SHA-256 f9f2c00690e9cd8c9b2b334682c8b8c8dab7ed4be7879b7ee30d4a58126f2766; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
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
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulHom_Defs
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

theorem coordinateKoszulTransition_basis
    (n m : ℕ) (T : Finset V) (p : ℕ) (F : CechSlot T p) :
    coordinateKoszulTransition k n m T p
        ((Pi.basisFun (MvPolynomial V k) (CechSlot T p)) F) =
      polynomialFaceMonomial k F.1 ^ (m - n) •
        ((Pi.basisFun (MvPolynomial V k) (CechSlot T p)) F) := by
  classical
  funext G
  by_cases h : G = F
  · subst G
    simp [coordinateKoszulTransition, Pi.basisFun_apply, Pi.single_apply]
  · have h' : F ≠ G := Ne.symm h
    simp [coordinateKoszulTransition, Pi.basisFun_apply, Pi.single_apply, h, h']

/-- The actual Hom transition is multiplication by x_F^(m-n) on the F column.
Thus adjacent stages give the previously constructed localization telescope. -/
theorem coordinateKoszulHomCoordinates_transition
    (n m : ℕ) (T : Finset V) (p : ℕ)
    (M : ModuleCat.{u} (MvPolynomial V k))
    (f : ModuleCat.of (MvPolynomial V k) (CoordinateKoszulTerm k T p) ⟶ M)
    (F : CechSlot T p) :
    coordinateKoszulHomCoordinates k T p M
        (ModuleCat.ofHom (coordinateKoszulTransition k n m T p) ≫ f) F =
      polynomialFaceMonomial k F.1 ^ (m - n) • coordinateKoszulHomCoordinates k T p M f F := by
  rw [coordinateKoszulHomCoordinates_apply, coordinateKoszulHomCoordinates_apply]
  change f.hom (coordinateKoszulTransition k n m T p
    ((Pi.basisFun (MvPolynomial V k) (CechSlot T p)) F)) = _
  rw [coordinateKoszulTransition_basis, map_smul]

end LPCA


