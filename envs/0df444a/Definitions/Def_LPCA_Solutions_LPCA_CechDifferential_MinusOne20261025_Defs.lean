-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_MinusOne20261025_Defs
-- name    : LPCA_Solutions_LPCA_CechDifferential_MinusOne20261025_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-26T01:31:47.002591+00:00
-- url     : https://prove2.me/theorems/ce0c4603-02b5-4f20-bb03-9a109edd59f8
-- title:
--   Cech Differential — degree minus-one interval dependencies
-- statement:
--   Selected constructions and proved compatibility results for cech differential, used in the explicit degree-minus-one interval presentations. The formal declarations retain their exact objects, hypotheses and structure maps.
--
--   The link term equivalences commute with the actual localization matrices.
--
--   The deletion term equivalences commute with the actual localization matrices.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Proposition3.12 and Corollary6.4, with their formalization dependencies. Certified Lean source: Solutions/LPCA_CechDifferential.lean, selected declarations in lines 95–147; source SHA-256 0ece4376c8edbe04c0850b2a9fed83bb558c40efa6d6b00f9f8ba0daaee39262; exact-source certificate Sapelo2 job 49311470.

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
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
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

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]











theorem zeroDegreeActualTermEquiv_coordinates
    (K : Complex V) (i : V) (T : Finset V) (a : V → ℤ) (p : ℕ)
    (hT : i ∉ T) (ha : a i = 0) (y : LocalizedCechTerm k K T a p) :
    actualToModel k (deletion K i) T a p
      (zeroDegreeActualTermEquiv k K i T a p hT ha y) =
    zeroDegreeTermEquiv k K i T a p hT ha (actualToModel k K T a p y) := by
  change (actualTermEquivModel k (deletion K i) T a p)
    ((actualTermEquivModel k (deletion K i) T a p).symm _) = _
  exact LinearEquiv.apply_symm_apply _ _

theorem positiveDegreeActualTermEquiv_coordinates
    (K : Complex V) (i : V) (T : Finset V) (a : V → ℤ) (p : ℕ)
    (hT : i ∉ T) (ha : 0 < a i) (y : LocalizedCechTerm k K T a p) :
    actualToModel k (link K {i}) T (Function.update a i 0) p
      (positiveDegreeActualTermEquiv k K i T a p hT ha y) =
    positiveDegreeTermEquiv k K i T a p hT ha (actualToModel k K T a p y) := by
  change (actualTermEquivModel k (link K {i}) T (Function.update a i 0) p)
    ((actualTermEquivModel k (link K {i}) T (Function.update a i 0) p).symm _) = _
  exact LinearEquiv.apply_symm_apply _ _

/-- The deletion term equivalences commute with the actual localization matrices. -/
theorem zeroDegree_actualDifferential_compatibility
    (coefficient : Finset V → Finset V → k)
    (K : Complex V) (i : V) (T : Finset V) (a : V → ℤ) (p : ℕ)
    (hT : i ∉ T) (ha : a i = 0) (y : LocalizedCechTerm k K T a p) :
    zeroDegreeActualTermEquiv k K i T a (p + 1) hT ha
      (actualDifferential k coefficient K T a p y) =
    actualDifferential k coefficient (deletion K i) T a p
      (zeroDegreeActualTermEquiv k K i T a p hT ha y) := by
  apply (actualTermEquivModel k (deletion K i) T a (p + 1)).injective
  change actualToModel k (deletion K i) T a (p + 1) _ =
    actualToModel k (deletion K i) T a (p + 1) _
  rw [zeroDegreeActualTermEquiv_coordinates, actualDifferential_coordinates,
    actualDifferential_coordinates, zeroDegreeActualTermEquiv_coordinates]
  exact zeroDegree_differential_compatibility k (incidenceCoefficient k coefficient)
    K i T a p hT ha (actualToModel k K T a p y)

/-- The link term equivalences commute with the actual localization matrices. -/
theorem positiveDegree_actualDifferential_compatibility
    (coefficient : Finset V → Finset V → k)
    (K : Complex V) (i : V) (T : Finset V) (a : V → ℤ) (p : ℕ)
    (hT : i ∉ T) (ha : 0 < a i) (y : LocalizedCechTerm k K T a p) :
    positiveDegreeActualTermEquiv k K i T a (p + 1) hT ha
      (actualDifferential k coefficient K T a p y) =
    actualDifferential k coefficient (link K {i}) T (Function.update a i 0) p
      (positiveDegreeActualTermEquiv k K i T a p hT ha y) := by
  apply (actualTermEquivModel k (link K {i}) T (Function.update a i 0) (p + 1)).injective
  change actualToModel k (link K {i}) T (Function.update a i 0) (p + 1) _ =
    actualToModel k (link K {i}) T (Function.update a i 0) (p + 1) _
  rw [positiveDegreeActualTermEquiv_coordinates, actualDifferential_coordinates,
    actualDifferential_coordinates, positiveDegreeActualTermEquiv_coordinates]
  exact positiveDegree_differential_compatibility k (incidenceCoefficient k coefficient)
    K i T a p hT ha (actualToModel k K T a p y)

end LPCA


