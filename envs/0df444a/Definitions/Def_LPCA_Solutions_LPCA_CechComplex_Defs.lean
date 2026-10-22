-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CechComplex_Defs
-- name    : LPCA_Solutions_LPCA_CechComplex_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:34:05.929909+00:00
-- url     : https://prove2.me/theorems/199f303e-6185-4678-8b21-eb814e4d1ace
-- title:
--   Čech Complex for localized persistent commutative algebra
-- statement:
--   This bundle supplies čech Complex for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The fixed-multidegree Cech cochain complex, built from the actual localized homogeneous subspaces and the signed localization-induced maps.
--   - This is Cech cohomology. Its identification with supportCohomology remains a separate theorem and is not assumed by this definition.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_CechComplex.lean, selected declarations in lines 17–88; source SHA-256 c4507c811dadad21ddcde9a68723e7a1508c377d36bdc9fd89b44bb6566b577f; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
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
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

attribute [local instance 2000] localizedTermAddCommGroup localizedTermModule

/-- The fixed-multidegree Cech cochain complex, built from the actual localized
homogeneous subspaces and the signed localization-induced maps. -/
noncomputable def localizedCechComplex
    (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) (a : V → ℤ) :
    CochainComplex (ModuleCat k) ℕ :=
  CochainComplex.of
    (fun p => ModuleCat.of k (LocalizedCechTerm k K T a p))
    (fun p => ModuleCat.ofHom (actualDifferential k (cechCoefficient k rank) K T a p))
    (fun p => by
      apply ModuleCat.hom_ext
      exact actualCechDifferential_comp_zero k rank K T a p)

theorem localizedCechComplex_d
    (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) (a : V → ℤ) (p : ℕ) :
    (localizedCechComplex k rank K T a).d p (p + 1) =
      ModuleCat.ofHom (actualDifferential k (cechCoefficient k rank) K T a p) := by
  exact CochainComplex.of_d
    (fun n => ModuleCat.of k (LocalizedCechTerm k K T a n))
    (fun n => ModuleCat.ofHom (actualDifferential k (cechCoefficient k rank) K T a n)) p







/-- This is Cech cohomology. Its identification with supportCohomology remains
a separate theorem and is not assumed by this definition. -/
noncomputable def localizedCechCohomology
    (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) (a : V → ℤ) (q : ℕ) : ModuleCat k :=
  (localizedCechComplex k rank K T a).homology q







end LPCA


