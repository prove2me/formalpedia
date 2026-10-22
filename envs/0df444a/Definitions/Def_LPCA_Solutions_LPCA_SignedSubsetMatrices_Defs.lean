-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
-- name    : LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:33:26.073799+00:00
-- url     : https://prove2.me/theorems/f16b993f-f28b-4be1-9db5-9dd970569523
-- title:
--   Signed Subset Matrices for localized persistent commutative algebra
-- statement:
--   This bundle supplies signed Subset Matrices for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The full simplex on a finite subset of the ambient vertex type.
--   - Signed incidence cancellation on every p-element subset, obtained from the already proved convex-family cancellation without treating a polynomial ring as a field.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_SignedSubsetMatrices.lean, selected declarations in lines 12–46; source SHA-256 7b570b469a048334720fa4bd709526de48ba47a9d91938f47134d0c9c8ddb41f; source certificate Sapelo2 job 49172236.

import Mathlib
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

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

/-- The full simplex on a finite subset of the ambient vertex type. -/
def simplexComplex (T : Finset V) : Complex V where
  faces := T.powerset
  down_closed := by
    intro F G hF hGF
    exact Finset.mem_powerset.mpr (hGF.trans (Finset.mem_powerset.mp hF))

theorem simplexCriterion_zero (T F : Finset V) (hF : F ⊆ T) :
    LocalizationCriterion (simplexComplex T) F (fun _ => 0) := by
  refine ⟨fun _ _ => le_rfl, ?_⟩
  simpa [positiveSupport, simplexComplex] using hF

/-- Signed incidence cancellation on every p-element subset, obtained from
the already proved convex-family cancellation without treating a polynomial ring as a field. -/
theorem cechCoefficient_square_slots
    (rank : V ↪ ℕ) (T : Finset V) (p : ℕ)
    (F : CechSlot T p) (H : CechSlot T (p + 1 + 1)) :
    ∑ G : CechSlot T (p + 1),
      cechCoefficient k rank F.1 G.1 * cechCoefficient k rank G.1 H.1 = 0 := by
  let e : CechBasis (simplexComplex T) T (fun _ => 0) (p + 1) ≃
      CechSlot T (p + 1) := {
    toFun := fun G => ⟨G.1, G.2.1, G.2.2.1⟩
    invFun := fun G => ⟨G.1, G.2.1, G.2.2, simplexCriterion_zero T G.1 G.2.1⟩
    left_inv := fun G => Subtype.ext rfl
    right_inv := fun G => Subtype.ext rfl }
  rw [← e.sum_comp]
  exact cechCoefficient_square k rank (simplexComplex T) T (fun _ => 0) p
    ⟨F.1, F.2.1, F.2.2, simplexCriterion_zero T F.1 F.2.1⟩
    ⟨H.1, H.2.1, H.2.2, simplexCriterion_zero T H.1 H.2.1⟩

theorem cechCoefficient_zero_of_not_subset
    (rank : V ↪ ℕ) (F G : Finset V) (hFG : ¬ F ⊆ G) :
    cechCoefficient k rank F G = 0 := by
  classical
  simp [cechCoefficient, hFG]

end LPCA


