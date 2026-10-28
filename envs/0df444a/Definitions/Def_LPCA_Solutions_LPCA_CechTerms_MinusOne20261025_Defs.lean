-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CechTerms_MinusOne20261025_Defs
-- name    : LPCA_Solutions_LPCA_CechTerms_MinusOne20261025_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-26T01:31:03.075113+00:00
-- url     : https://prove2.me/theorems/0acdc4b6-251f-4f1a-809e-4b4fa5b5aed7
-- title:
--   Cech Terms — degree minus-one interval dependencies
-- statement:
--   Selected constructions and proved compatibility results for cech terms, used in the explicit degree-minus-one interval presentations. The formal declarations retain their exact objects, hypotheses and structure maps.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Proposition3.12 and Corollary6.4, with their formalization dependencies. Certified Lean source: Solutions/LPCA_CechTerms.lean, selected declarations in lines 91–106; source SHA-256 daa9522baa69513cf73223b5143e2e03c7b214f3f77e05fb74b3e507916b9fa5; exact-source certificate Sapelo2 job 49311470.

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
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_MinusOne20261025_Defs

set_option autoImplicit false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

















noncomputable def zeroDegreeActualTermEquiv
    (K : Complex V) (i : V) (T : Finset V) (a : V → ℤ) (p : ℕ)
    (hT : i ∉ T) (ha : a i = 0) :
    LocalizedCechTerm k K T a p ≃ₗ[k] LocalizedCechTerm k (deletion K i) T a p :=
  actualTermEquivModel k K T a p ≪≫ₗ
    zeroDegreeTermEquiv k K i T a p hT ha ≪≫ₗ
    (actualTermEquivModel k (deletion K i) T a p).symm

noncomputable def positiveDegreeActualTermEquiv
    (K : Complex V) (i : V) (T : Finset V) (a : V → ℤ) (p : ℕ)
    (hT : i ∉ T) (ha : 0 < a i) :
    LocalizedCechTerm k K T a p ≃ₗ[k]
      LocalizedCechTerm k (link K {i}) T (Function.update a i 0) p :=
  actualTermEquivModel k K T a p ≪≫ₗ
    positiveDegreeTermEquiv k K i T a p hT ha ≪≫ₗ
    (actualTermEquivModel k (link K {i}) T (Function.update a i 0) p).symm



end LPCA


