-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CechComplex_MinusOne20261025_Defs
-- name    : LPCA_Solutions_LPCA_CechComplex_MinusOne20261025_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-26T01:33:05.323526+00:00
-- url     : https://prove2.me/theorems/0e171aa4-dc45-4961-acc5-f031ea1a5633
-- title:
--   Cech Complex — degree minus-one interval dependencies
-- statement:
--   Selected constructions and proved compatibility results for cech complex, used in the explicit degree-minus-one interval presentations. The formal declarations retain their exact objects, hypotheses and structure maps.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Proposition3.12 and Corollary6.4, with their formalization dependencies. Certified Lean source: Solutions/LPCA_CechComplex.lean, selected declarations in lines 37–68; source SHA-256 c4507c811dadad21ddcde9a68723e7a1508c377d36bdc9fd89b44bb6566b577f; exact-source certificate Sapelo2 job 49311470.

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
import Definitions.Def_LPCA_Solutions_LPCA_CechComplex_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_MinusOne20261025_Defs

set_option autoImplicit false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

attribute [local instance 2000] localizedTermAddCommGroup localizedTermModule





noncomputable def zeroDegreeCechComplexIso
    (rank : V ↪ ℕ) (K : Complex V) (i : V) (T : Finset V) (a : V → ℤ)
    (hT : i ∉ T) (ha : a i = 0) :
    localizedCechComplex k rank K T a ≅ localizedCechComplex k rank (deletion K i) T a := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun p => (zeroDegreeActualTermEquiv k K i T a p hT ha).toModuleIso) ?_
  intro p q hpq
  change p + 1 = q at hpq
  subst q
  rw [localizedCechComplex_d, localizedCechComplex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  exact (zeroDegree_actualDifferential_compatibility k (cechCoefficient k rank)
    K i T a p hT ha y).symm

noncomputable def positiveDegreeCechComplexIso
    (rank : V ↪ ℕ) (K : Complex V) (i : V) (T : Finset V) (a : V → ℤ)
    (hT : i ∉ T) (ha : 0 < a i) :
    localizedCechComplex k rank K T a ≅
      localizedCechComplex k rank (link K {i}) T (Function.update a i 0) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun p => (positiveDegreeActualTermEquiv k K i T a p hT ha).toModuleIso) ?_
  intro p q hpq
  change p + 1 = q at hpq
  subst q
  rw [localizedCechComplex_d, localizedCechComplex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  exact (positiveDegree_actualDifferential_compatibility k (cechCoefficient k rank)
    K i T a p hT ha y).symm











end LPCA


