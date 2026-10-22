-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_HochsterSigns_Defs
-- name    : LPCA_Solutions_LPCA_HochsterSigns_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:26:05.867345+00:00
-- url     : https://prove2.me/theorems/f912b370-b405-424c-a9f5-840c9040e776
-- title:
--   Hochster Signs for localized persistent commutative algebra
-- statement:
--   This bundle supplies hochster Signs for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_HochsterSigns.lean, selected declarations in lines 12–42; source SHA-256 75065c07cbfd623495115f4b9cc5473114cab05ceebae31891240ef9f82c9b86; source certificate Sapelo2 job 49172236.

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
import Mathlib.Tactic.Ring
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V]

def hochsterLowerCount (rank : V ↪ ℕ) (F : Finset V) (j : V) : ℕ :=
  (F.filter (fun v => rank v < rank j)).card

def hochsterInversionCount (rank : V ↪ ℕ) (σ G : Finset V) : ℕ :=
  ∑ g ∈ G, hochsterLowerCount rank σ g





variable (R : Type u) [CommRing R]

def hochsterSign (rank : V ↪ ℕ) (σ G : Finset V) : R :=
  (-1 : R) ^ hochsterInversionCount rank σ G

theorem hochsterSign_mul_self (rank : V ↪ ℕ) (σ G : Finset V) :
    hochsterSign R rank σ G * hochsterSign R rank σ G = 1 := by
  rcases neg_one_pow_eq_or R (hochsterInversionCount rank σ G) with h | h <;>
    simp only [hochsterSign, h, one_mul, neg_mul_neg]





variable [Fintype V] (k : Type u) [Field k]



end LPCA


