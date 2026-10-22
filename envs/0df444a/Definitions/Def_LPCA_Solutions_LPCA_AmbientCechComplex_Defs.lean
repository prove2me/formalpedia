-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_AmbientCechComplex_Defs
-- name    : LPCA_Solutions_LPCA_AmbientCechComplex_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:35:53.618156+00:00
-- url     : https://prove2.me/theorems/01e3c93a-981c-4bc4-a8af-1d772ab4974d
-- title:
--   Ambient Čech Complex for localized persistent commutative algebra
-- statement:
--   This bundle supplies ambient Čech Complex for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The full ungraded term, using the actual localized rings with explicitly restricted ambient polynomial scalars.
--   - The actual ungraded, ambient-S-linear Cech complex.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_AmbientCechComplex.lean, selected declarations in lines 16–98; source SHA-256 f1a5297da8735b5350b216ff96df1bd27d941760d4858a60513569e50124daf0; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.CategoryTheory.Adjunction.Limits
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
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace LPCA

open CategoryTheory

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

/-- The full ungraded term, using the actual localized rings with explicitly
restricted ambient polynomial scalars. -/
abbrev AmbientCechTerm (K : Complex V) (T : Finset V) (p : ℕ) : Type u :=
  ∀ F : CechSlot T p, ambientLocalizedModule k K F.1

noncomputable def ambientLocalizationEntry (K : Complex V) (F G : Finset V) :
    ambientLocalizedModule k K F →ₗ[MvPolynomial V k] ambientLocalizedModule k K G := by
  classical
  exact if h : F ⊆ G then (ambientLocalizationMap k K F G h).hom else 0

noncomputable def ambientCechEntry (rank : V ↪ ℕ) (K : Complex V) (F G : Finset V) :
    ambientLocalizedModule k K F →ₗ[MvPolynomial V k] ambientLocalizedModule k K G :=
  (MvPolynomial.C (cechCoefficient k rank F G) : MvPolynomial V k) • ambientLocalizationEntry k K F G

theorem ambientCechEntry_comp
    (rank : V ↪ ℕ) (K : Complex V) (F G H : Finset V) :
    (ambientCechEntry k rank K G H).comp (ambientCechEntry k rank K F G) =
      (MvPolynomial.C (cechCoefficient k rank F G * cechCoefficient k rank G H) : MvPolynomial V k) •
        ambientLocalizationEntry k K F H := by
  classical
  by_cases hFG : F ⊆ G
  · by_cases hGH : G ⊆ H
    · have hFH := hFG.trans hGH
      apply LinearMap.ext
      intro x
      simp only [ambientCechEntry, ambientLocalizationEntry, dif_pos hFG, dif_pos hGH,
        dif_pos hFH, LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_smul]
      have hc := congrArg (fun f => f.hom x) (ambientLocalizationMap_comp k K F G H hFG hGH)
      change (ambientLocalizationMap k K G H hGH).hom
        ((ambientLocalizationMap k K F G hFG).hom x) =
          (ambientLocalizationMap k K F H hFH).hom x at hc
      rw [hc, map_mul]
    · have hz := cechCoefficient_zero_of_not_subset k rank G H hGH
      simp [ambientCechEntry, hz]
  · have hz := cechCoefficient_zero_of_not_subset k rank F G hFG
    simp [ambientCechEntry, hz]

theorem ambientCechEntry_square
    (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) (p : ℕ)
    (F : CechSlot T p) (H : CechSlot T (p + 1 + 1)) :
    ∑ G : CechSlot T (p + 1),
      (ambientCechEntry k rank K G.1 H.1).comp (ambientCechEntry k rank K F.1 G.1) = 0 := by
  classical
  simp_rw [ambientCechEntry_comp]
  rw [← Finset.sum_smul, ← map_sum, cechCoefficient_square_slots, map_zero, zero_smul]

noncomputable def ambientCechDifferential
    (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) (p : ℕ) :
    AmbientCechTerm k K T p →ₗ[MvPolynomial V k] AmbientCechTerm k K T (p + 1) where
  toFun y G := ∑ F : CechSlot T p, ambientCechEntry k rank K F.1 G.1 (y F)
  map_add' x y := by
    funext G
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c y := by
    funext G
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]

theorem ambientCechDifferential_square
    (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) (p : ℕ)
    (y : AmbientCechTerm k K T p) :
    ambientCechDifferential k rank K T (p + 1) (ambientCechDifferential k rank K T p y) = 0 := by
  classical
  funext H
  change (∑ G : CechSlot T (p + 1), ambientCechEntry k rank K G.1 H.1
    (∑ F : CechSlot T p, ambientCechEntry k rank K F.1 G.1 (y F))) = 0
  simp_rw [map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro F _
  change (∑ G : CechSlot T (p + 1),
    ((ambientCechEntry k rank K G.1 H.1).comp (ambientCechEntry k rank K F.1 G.1)) (y F)) = 0
  rw [← LinearMap.sum_apply, ambientCechEntry_square, LinearMap.zero_apply]

/-- The actual ungraded, ambient-S-linear Cech complex. -/
noncomputable def ambientCechComplex (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) :
    CochainComplex (ModuleCat (MvPolynomial V k)) ℕ :=
  CochainComplex.of
    (fun p => ModuleCat.of (MvPolynomial V k) (AmbientCechTerm k K T p))
    (fun p => ModuleCat.ofHom (ambientCechDifferential k rank K T p))
    (fun p => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact ambientCechDifferential_square k rank K T p)

end LPCA


