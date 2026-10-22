-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
-- name    : LPCA_Solutions_LPCA_CechSquareZero_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:31:43.677419+00:00
-- url     : https://prove2.me/theorems/5e9b07a4-0e08-4f41-9999-1687119420fe
-- title:
--   Square-zero identity for actual Čech differentials
-- statement:
--   This bundle supplies square-zero identity for actual Čech differentials. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - Sign cancellation is imported from the existing SignedCore library. The localization criterion supplies exactly its convex-family hypothesis.
--   - The signed sums of actual localization maps form a square-zero differential.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_CechSquareZero.lean, selected declarations in lines 15–118; source SHA-256 1ff5fc6d0702f329d58dc32db20b0fdf88465f98dd4d2b3743578fb1624d6c41; source certificate Sapelo2 job 49172236.

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

attribute [local instance 2000] localizedTermAddCommGroup localizedTermModule

noncomputable local instance (priority := 3000) termZero
    (K : Complex V) (T : Finset V) (a : V → ℤ) (p : ℕ) :
    Zero (LocalizedCechTerm k K T a p) :=
  ⟨(localizedTermAddCommGroup k K T a p).zero⟩

noncomputable local instance (priority := 3000) termOfNatZero
    (K : Complex V) (T : Finset V) (a : V → ℤ) (p : ℕ) :
    OfNat (LocalizedCechTerm k K T a p) 0 :=
  ⟨(localizedTermAddCommGroup k K T a p).zero⟩

theorem incidenceCoefficient_cech (rank : V ↪ ℕ) :
    incidenceCoefficient k (cechCoefficient k rank) = cechCoefficient k rank := by
  classical
  funext F G
  by_cases hFG : F ⊆ G <;> simp [incidenceCoefficient, cechCoefficient, hFG]

/-- Sign cancellation is imported from the existing SignedCore library. The
localization criterion supplies exactly its convex-family hypothesis. -/
theorem cechCoefficient_square
    (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) (a : V → ℤ) (p : ℕ)
    (F : CechBasis K T a p) (H : CechBasis K T a (p + 1 + 1)) :
    ∑ G : CechBasis K T a (p + 1),
      cechCoefficient k rank F.1 G.1 * cechCoefficient k rank G.1 H.1 = 0 := by
  let decV : DecidableEq V := inferInstance
  let orderV : LinearOrder V := LinearOrder.lift' rank rank.injective
  letI : LinearOrder V :=
    { orderV with
      toDecidableEq := decV
      compare := fun v w => @compareOfLessAndEq V v w orderV.toLT (orderV.toDecidableLT v w) decV
      compare_eq_compareOfLessAndEq := by intro v w; rfl }
  classical
  let P : Finset V → Prop := fun G => G ⊆ T ∧ LocalizationCriterion K G a
  have hconv : Proofs.BassLyubeznik.SignedCore.IsConvex P := by
    intro F G H hF hH hFG hGH
    exact ⟨hGH.trans hH.1, localizationCriterion_between K a F G H hF.2 hH.2 hFG hGH⟩
  have hinc : ∀ F G : Finset V, cechCoefficient k rank F G =
      Proofs.BassLyubeznik.SignedCore.inc k F G := by
    intro F G
    rfl
  let e : CechBasis K T a (p + 1) ≃
      {G : Finset V // P G ∧ (G.card : ℤ) = (p : ℤ) + 1} := {
    toFun := fun G => ⟨G.1, ⟨G.2.1, G.2.2.2⟩, by exact_mod_cast G.2.2.1⟩
    invFun := fun G => ⟨G.1, G.2.1.1, by exact_mod_cast G.2.2, G.2.1.2⟩
    left_inv := fun G => Subtype.ext rfl
    right_inv := fun G => Subtype.ext rfl }
  calc
    _ = ∑ G : CechBasis K T a (p + 1),
        Proofs.BassLyubeznik.SignedCore.inc k F.1 G.1 *
          Proofs.BassLyubeznik.SignedCore.inc k G.1 H.1 := by simp only [hinc]
    _ = ∑ G : {G : Finset V // P G ∧ (G.card : ℤ) = (p : ℤ) + 1},
        Proofs.BassLyubeznik.SignedCore.inc k F.1 G.1 *
          Proofs.BassLyubeznik.SignedCore.inc k G.1 H.1 :=
      Equiv.sum_comp e (fun G => Proofs.BassLyubeznik.SignedCore.inc k F.1 G.1 *
        Proofs.BassLyubeznik.SignedCore.inc k G.1 H.1)
    _ = 0 := Proofs.BassLyubeznik.SignedCore.dd_sum_inner hconv
      ⟨F.2.1, F.2.2.2⟩ ⟨H.2.1, H.2.2.2⟩ (by exact_mod_cast congrArg (fun n : ℕ => n + 1) F.2.2.1)

theorem cechBasisDifferential_square
    (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) (a : V → ℤ) (p : ℕ)
    (x : CechBasis K T a p → k) :
    basisDifferential k (cechCoefficient k rank) K T a (p + 1)
      (basisDifferential k (cechCoefficient k rank) K T a p x) = 0 := by
  classical
  funext H
  change (∑ G : CechBasis K T a (p + 1), cechCoefficient k rank G.1 H.1 *
    ∑ F : CechBasis K T a p, cechCoefficient k rank F.1 G.1 * x F) = 0
  calc
    _ = ∑ G : CechBasis K T a (p + 1), ∑ F : CechBasis K T a p,
        cechCoefficient k rank F.1 G.1 * cechCoefficient k rank G.1 H.1 * x F := by
      apply Finset.sum_congr rfl
      intro G _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro F _
      ring
    _ = ∑ F : CechBasis K T a p, ∑ G : CechBasis K T a (p + 1),
        cechCoefficient k rank F.1 G.1 * cechCoefficient k rank G.1 H.1 * x F :=
      Finset.sum_comm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro F _
      rw [← Finset.sum_mul, cechCoefficient_square, zero_mul]

/-- The signed sums of actual localization maps form a square-zero differential. -/
theorem actualCechDifferential_square
    (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) (a : V → ℤ) (p : ℕ)
    (y : LocalizedCechTerm k K T a p) :
    actualDifferential k (cechCoefficient k rank) K T a (p + 1)
      (actualDifferential k (cechCoefficient k rank) K T a p y) = 0 := by
  letI : AddCommMonoid (LocalizedCechTerm k K T a (p + 1 + 1)) :=
    (localizedTermAddCommGroup k K T a (p + 1 + 1)).toAddCommMonoid
  apply (actualTermEquivModel k K T a (p + 1 + 1)).injective
  change actualToModel k K T a (p + 1 + 1) _ = actualToModel k K T a (p + 1 + 1) 0
  rw [actualDifferential_coordinates, actualDifferential_coordinates,
    incidenceCoefficient_cech, map_zero]
  exact cechBasisDifferential_square k rank K T a p (actualToModel k K T a p y)

theorem actualCechDifferential_comp_zero
    (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) (a : V → ℤ) (p : ℕ) :
    (actualDifferential k (cechCoefficient k rank) K T a (p + 1)).comp
      (actualDifferential k (cechCoefficient k rank) K T a p) = 0 := by
  apply LinearMap.ext
  intro y
  exact actualCechDifferential_square k rank K T a p y

end LPCA


