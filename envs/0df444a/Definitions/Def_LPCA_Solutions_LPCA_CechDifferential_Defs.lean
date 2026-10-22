-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
-- name    : LPCA_Solutions_LPCA_CechDifferential_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:24:20.448417+00:00
-- url     : https://prove2.me/theorems/fbd4e09d-0c20-485f-a8b8-aa22fd828f50
-- title:
--   Actual Čech differentials in homogeneous coordinates
-- statement:
--   This bundle supplies actual Čech differentials in homogeneous coordinates. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The nonzero localization indices contain every set between two of their members. This is the closure property needed for cancellation in d squared.
--   - Alternating incidence coefficient for an explicitly ordered list of variables. The rank embedding supplies the order without changing the vertex type.
--   - A matrix of genuine localization-induced maps. Zero homogeneous source summands are omitted from the finite sum. Choosing the alternating incidence coefficients gives the usual degree-preserving Cech differential; no assertion that an arbitrary coefficient matrix squares to zero is made here.
--   - The normalized matrix is derived from the actual localization maps.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_CechDifferential.lean, selected declarations in lines 12–93; source SHA-256 0ece4376c8edbe04c0850b2a9fed83bb558c40efa6d6b00f9f8ba0daaee39262; source certificate Sapelo2 job 49172236.

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

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

/-- The nonzero localization indices contain every set between two of their
members. This is the closure property needed for cancellation in d squared. -/
theorem localizationCriterion_between
    (K : Complex V) (a : V → ℤ) (F G H : Finset V)
    (hF : LocalizationCriterion K F a) (hH : LocalizationCriterion K H a)
    (hFG : F ⊆ G) (hGH : G ⊆ H) : LocalizationCriterion K G a := by
  refine ⟨fun j hj => hF.1 j (fun hjF => hj (hFG hjF)), ?_⟩
  exact K.down_closed hH.2
    (Finset.union_subset_union (Finset.Subset.refl _) hGH)

/-- Alternating incidence coefficient for an explicitly ordered list of variables.
The rank embedding supplies the order without changing the vertex type. -/
noncomputable def cechCoefficient (rank : V ↪ ℕ) (F G : Finset V) : k := by
  classical
  exact if F ⊆ G ∧ G.card = F.card + 1 then
    ∑ j ∈ G \ F, (-1 : k) ^ (F.filter (fun v => rank v < rank j)).card
  else 0

/-- A matrix of genuine localization-induced maps. Zero homogeneous source
summands are omitted from the finite sum. Choosing the alternating incidence
coefficients gives the usual degree-preserving Cech differential; no assertion
that an arbitrary coefficient matrix squares to zero is made here. -/
noncomputable def actualDifferential
    (coefficient : Finset V → Finset V → k)
    (K : Complex V) (T : Finset V) (a : V → ℤ) (p : ℕ) :
    LocalizedCechTerm k K T a p →ₗ[k] LocalizedCechTerm k K T a (p + 1) := by
  classical
  exact {
    toFun := fun y G => ∑ F : CechBasis K T a p,
      if hFG : F.1 ⊆ G.1 then
        coefficient F.1 G.1 • localizedPieceMap k K F.1 G.1 hFG a
          (y ⟨F.1, F.2.1, F.2.2.1⟩)
      else 0
    map_add' := by
      intro x y
      funext G
      simp only [Pi.add_apply, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro F _
      split_ifs <;> simp [map_add, smul_add]
    map_smul' := by
      intro c y
      funext G
      simp only [Pi.smul_apply, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro F _
      split_ifs
      · rw [map_smul]
        exact smul_comm _ _ _
      · simp only [smul_zero] }

noncomputable def incidenceCoefficient
    (coefficient : Finset V → Finset V → k) (F G : Finset V) : k := by
  classical
  exact if F ⊆ G then coefficient F G else 0

/-- The normalized matrix is derived from the actual localization maps. -/
theorem actualDifferential_coordinates
    (coefficient : Finset V → Finset V → k)
    (K : Complex V) (T : Finset V) (a : V → ℤ) (p : ℕ)
    (y : LocalizedCechTerm k K T a p) :
    actualToModel k K T a (p + 1) (actualDifferential k coefficient K T a p y) =
      basisDifferential k (incidenceCoefficient k coefficient) K T a p
        (actualToModel k K T a p y) := by
  classical
  funext G
  change (pieceCoordinateEquiv k K G.1 a G.2.2.2).symm
    (∑ F : CechBasis K T a p, if hFG : F.1 ⊆ G.1 then
      coefficient F.1 G.1 • localizedPieceMap k K F.1 G.1 hFG a
        (y ⟨F.1, F.2.1, F.2.2.1⟩) else 0) =
    ∑ F : CechBasis K T a p,
      incidenceCoefficient k coefficient F.1 G.1 *
        (pieceCoordinateEquiv k K F.1 a F.2.2.2).symm
          (y ⟨F.1, F.2.1, F.2.2.1⟩)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro F _
  by_cases hFG : F.1 ⊆ G.1
  · simp only [dif_pos hFG, incidenceCoefficient, if_pos hFG, map_smul,
      smul_eq_mul]
    rw [localization_transition_coordinates_apply k K F.1 G.1 hFG a F.2.2.2 G.2.2.2]
  · simp [hFG, incidenceCoefficient]









end LPCA


