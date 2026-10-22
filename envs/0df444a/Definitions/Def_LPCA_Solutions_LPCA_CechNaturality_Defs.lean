-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
-- name    : LPCA_Solutions_LPCA_CechNaturality_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:23:08.797474+00:00
-- url     : https://prove2.me/theorems/2844a00e-4f82-4cef-b821-b1e1a18b27a0
-- title:
--   Naturality of normalized localization coordinates
-- statement:
--   This bundle supplies naturality of normalized localization coordinates. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The chosen coordinate equivalence uses the coefficient-one fraction of the specified degree, independently of the representative used to write it.
--   - Nonzero homogeneous pieces have transition coefficient exactly one.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_CechNaturality.lean, selected declarations in lines 13–63; source SHA-256 d31e67b1785c832de9edc54b83d6909aa7ecd922fbb4edaee0c6a0b31b3801ba; source certificate Sapelo2 job 49172236.

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
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

/-- The chosen coordinate equivalence uses the coefficient-one fraction of the
specified degree, independently of the representative used to write it. -/
theorem pieceCoordinateEquiv_apply_val
    (K : Complex V) (F : Finset V) (a : V → ℤ)
    (hc : LocalizationCriterion K F a) (m : V →₀ ℕ) (N : ℕ)
    (hm : ∀ j : V, (m j : ℤ) - (if j ∈ F then (N : ℤ) else 0) = a j) (c : k) :
    (pieceCoordinateEquiv k K F a hc c).1 = c • localizedMonomial k K F m N := by
  let hexists := localizedPiece_nonzero_generator k K F a hc
  let m₀ := Classical.choose hexists
  let N₀ := Classical.choose (Classical.choose_spec hexists)
  have hspec := Classical.choose_spec (Classical.choose_spec hexists)
  change c • localizedMonomial k K F m₀ N₀ = _
  rw [localizedMonomial_eq_of_degree k K F a m₀ m N₀ N hspec.1 hm]

/-- Nonzero homogeneous pieces have transition coefficient exactly one. -/
theorem localizedPieceMap_coordinate
    (K : Complex V) (F G : Finset V) (hFG : F ⊆ G) (a : V → ℤ)
    (hF : LocalizationCriterion K F a) (hG : LocalizationCriterion K G a) (c : k) :
    localizedPieceMap k K F G hFG a (pieceCoordinateEquiv k K F a hF c) =
      pieceCoordinateEquiv k K G a hG c := by
  obtain ⟨m, N, hm, _, _⟩ := localizedPiece_nonzero_generator k K F a hF
  obtain ⟨m', N', hm', _, _⟩ := localizedPiece_nonzero_generator k K G a hG
  apply Subtype.ext
  change localizationMap k K F G hFG (pieceCoordinateEquiv k K F a hF c).1 = _
  rw [pieceCoordinateEquiv_apply_val k K F a hF m N hm,
    pieceCoordinateEquiv_apply_val k K G a hG m' N' hm', localizationMap_smul,
    localizationMap_monomial_of_degree k K F G hFG a m m' N N' hm hm']



theorem localization_transition_coordinates_apply
    (K : Complex V) (F G : Finset V) (hFG : F ⊆ G) (a : V → ℤ)
    (hF : LocalizationCriterion K F a) (hG : LocalizationCriterion K G a)
    (z : localizedPiece k K F a) :
    (pieceCoordinateEquiv k K G a hG).symm (localizedPieceMap k K F G hFG a z) =
      (pieceCoordinateEquiv k K F a hF).symm z := by
  have h := localizedPieceMap_coordinate k K F G hFG a hF hG
    ((pieceCoordinateEquiv k K F a hF).symm z)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [h, LinearEquiv.symm_apply_apply]

end LPCA


