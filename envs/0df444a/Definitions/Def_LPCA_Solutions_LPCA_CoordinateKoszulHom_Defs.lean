-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulHom_Defs
-- name    : LPCA_Solutions_LPCA_CoordinateKoszulHom_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:37:21.263803+00:00
-- url     : https://prove2.me/theorems/2a9b5651-0058-4ba8-a3a3-3139f87b139b
-- title:
--   Coordinate Koszul Hom for localized persistent commutative algebra
-- statement:
--   This bundle supplies coordinate Koszul Hom for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - Values on the genuine free S-basis identify Hom_S(K_p,M) with copies of M.
--   - Precomposition by the actual resolution differential has the weighted signed cochain matrix needed for the localization telescopes.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_CoordinateKoszulHom.lean, selected declarations in lines 16–76; source SHA-256 315889e0c910e74958f9595f55933405e4bcbcc9a3ba36a916b83f5f9c9ff114; source certificate Sapelo2 job 49172236.

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

/-- Values on the genuine free S-basis identify Hom_S(K_p,M) with copies of M. -/
noncomputable def coordinateKoszulHomCoordinates (T : Finset V) (p : ℕ)
    (M : ModuleCat.{u} (MvPolynomial V k)) :
    (ModuleCat.of (MvPolynomial V k) (CoordinateKoszulTerm k T p) ⟶ M) ≃ₗ[MvPolynomial V k]
      (CechSlot T p → M) :=
  ModuleCat.homLinearEquiv.trans ((Pi.basisFun (MvPolynomial V k) (CechSlot T p)).constr
    (MvPolynomial V k)).symm

@[simp] theorem coordinateKoszulHomCoordinates_apply (T : Finset V) (p : ℕ)
    (M : ModuleCat.{u} (MvPolynomial V k))
    (f : ModuleCat.of (MvPolynomial V k) (CoordinateKoszulTerm k T p) ⟶ M)
    (F : CechSlot T p) :
    coordinateKoszulHomCoordinates k T p M f F =
      f ((Pi.basisFun (MvPolynomial V k) (CechSlot T p)) F) := rfl

noncomputable def coordinateKoszulHomDifferential
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) (p : ℕ)
    (M : ModuleCat.{u} (MvPolynomial V k)) :
    (CechSlot T p → M) →ₗ[MvPolynomial V k] (CechSlot T (p + 1) → M) where
  toFun y G := ∑ F : CechSlot T p, coordinateKoszulCoefficient k rank n F.1 G.1 • y F
  map_add' x y := by funext G; simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    funext G
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro F _
    rw [mul_comm]

theorem coordinateKoszulDifferential_basis_apply
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) (p : ℕ)
    (F : CechSlot T p) (G : CechSlot T (p + 1)) :
    coordinateKoszulDifferential k rank n T p
      ((Pi.basisFun (MvPolynomial V k) (CechSlot T (p + 1))) G) F =
        coordinateKoszulCoefficient k rank n F.1 G.1 := by
  classical
  simp [coordinateKoszulDifferential, Pi.basisFun_apply, Pi.single_apply]

/-- Precomposition by the actual resolution differential has the weighted
signed cochain matrix needed for the localization telescopes. -/
theorem coordinateKoszulHomCoordinates_differential
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) (p : ℕ)
    (M : ModuleCat.{u} (MvPolynomial V k))
    (f : ModuleCat.of (MvPolynomial V k) (CoordinateKoszulTerm k T p) ⟶ M) :
    coordinateKoszulHomCoordinates k T (p + 1) M
        (ModuleCat.ofHom (coordinateKoszulDifferential k rank n T p) ≫ f) =
      coordinateKoszulHomDifferential k rank n T p M
        (coordinateKoszulHomCoordinates k T p M f) := by
  classical
  funext G
  rw [coordinateKoszulHomCoordinates_apply]
  change f.hom (coordinateKoszulDifferential k rank n T p
    ((Pi.basisFun (MvPolynomial V k) (CechSlot T (p + 1))) G)) = _
  rw [← (Pi.basisFun (MvPolynomial V k) (CechSlot T p)).sum_repr
    (coordinateKoszulDifferential k rank n T p
      ((Pi.basisFun (MvPolynomial V k) (CechSlot T (p + 1))) G))]
  rw [map_sum]
  change (∑ F : CechSlot T p, _) = ∑ F : CechSlot T p, _
  apply Finset.sum_congr rfl
  intro F _
  rw [map_smul, Pi.basisFun_repr, coordinateKoszulDifferential_basis_apply]
  rfl

end LPCA


