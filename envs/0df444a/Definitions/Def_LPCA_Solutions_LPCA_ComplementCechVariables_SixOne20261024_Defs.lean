-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_ComplementCechVariables_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_ComplementCechVariables_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:10:48.721269+00:00
-- url     : https://prove2.me/theorems/654b13dd-a7cb-46d4-90f8-a501fb58e6aa
-- title:
--   Complement Čech Variables — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for complement čech variables used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_ComplementCechVariables.lean, selected declarations in lines 17–61; source SHA-256 d73ca8c69fb0f0df0a5aecbddb58288fa0a50516519664bb8f8b5520f00b048e; exact-source certificate Sapelo2 job 49296539.

import Mathlib
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
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
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableMaps_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCech_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementLocalizations_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VariableMultiplication_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false

namespace LPCA

open CategoryTheory
open scoped Classical

universe u

variable {V W : Type u} [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W]
variable (k : Type u) [Field k]

attribute [local instance 2000] localizedTermAddCommGroup localizedTermModule

theorem restrictionActualTermEquiv_variable
    (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e)
    (T : Finset W) (a b : V → ℤ) (j : W) (p : ℕ)
    (ha : ∀ v, v ∉ Set.range e → a v = 0)
    (hb : ∀ v, v ∉ Set.range e → b v = 0)
    (hab : ∀ v, b v = a v + if v = e j then 1 else 0)
    (y : LocalizedCechTerm k K (T.map e) a p) :
    restrictionActualTermEquiv k K e hK T b p hb
        (actualTermVariableMap k K (T.map e) a b (e j) p hab y) =
      actualTermVariableMap k (restrictComplex K e) T (a ∘ e) (b ∘ e) j p
        (increment_restrict e a b j hab)
          (restrictionActualTermEquiv k K e hK T a p ha y) := by
  funext F
  rw [restrictionActualTermEquiv_apply]
  apply (localizedPieceRestrictionEquiv k K e hK F.1 b hb).injective
  rw [LinearEquiv.apply_symm_apply]
  change pieceVariableMap k K (F.1.map e) a b (e j) hab
      (y (restrictionCechSlotEquiv e T p F)) =
    localizedPieceRestrictionEquiv k K e hK F.1 b hb
      (pieceVariableMap k (restrictComplex K e) F.1 (a ∘ e) (b ∘ e) j
        (increment_restrict e a b j hab)
          (restrictionActualTermEquiv k K e hK T a p ha y F))
  rw [localizedPieceRestriction_variable k K e hK F.1 a b j ha hb hab,
    restrictionActualTermEquiv_apply,
    LinearEquiv.apply_symm_apply]

theorem restrictionCechComplexIso_variable
    (rank : V ↪ ℕ) (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e)
    (T : Finset W) (a b : V → ℤ) (j : W)
    (ha : ∀ v, v ∉ Set.range e → a v = 0)
    (hb : ∀ v, v ∉ Set.range e → b v = 0)
    (hab : ∀ v, b v = a v + if v = e j then 1 else 0) :
    localizedCechVariableMap k rank K (T.map e) a b (e j) hab ≫
        (restrictionCechComplexIso k rank K e hK T b hb).hom =
      (restrictionCechComplexIso k rank K e hK T a ha).hom ≫
        localizedCechVariableMap k (e.trans rank) (restrictComplex K e) T
          (a ∘ e) (b ∘ e) j (increment_restrict e a b j hab) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  exact restrictionActualTermEquiv_variable k K e hK T a b j p ha hb hab y



end LPCA


