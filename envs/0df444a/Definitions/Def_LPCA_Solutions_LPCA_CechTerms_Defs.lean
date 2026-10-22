-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
-- name    : LPCA_Solutions_LPCA_CechTerms_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:21:17.575996+00:00
-- url     : https://prove2.me/theorems/8b6d796f-0708-4567-be61-504905e15d69
-- title:
--   Čech Terms for localized persistent commutative algebra
-- statement:
--   This bundle supplies čech Terms for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - A term built from the actual homogeneous subspaces of the localized face ring. The index family is finite, so the product agrees with the finite direct sum.
--   - Coefficients are normalized using a genuine coefficient-one monomial fraction.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_CechTerms.lean, selected declarations in lines 13–89; source SHA-256 daa9522baa69513cf73223b5143e2e03c7b214f3f77e05fb74b3e507916b9fa5; source certificate Sapelo2 job 49172236.

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
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

abbrev CechSlot (T : Finset V) (p : ℕ) : Type u :=
  {F : Finset V // F ⊆ T ∧ F.card = p}

/-- A term built from the actual homogeneous subspaces of the localized face ring.
The index family is finite, so the product agrees with the finite direct sum. -/
abbrev LocalizedCechTerm (K : Complex V) (T : Finset V) (a : V → ℤ) (p : ℕ) : Type u :=
  (F : CechSlot T p) → ↥(localizedPiece k K F.1 a)

noncomputable instance localizedTermAddCommGroup
    (K : Complex V) (T : Finset V) (a : V → ℤ) (p : ℕ) :
    AddCommGroup (LocalizedCechTerm k K T a p) :=
  @Pi.addCommGroup (CechSlot T p) (fun F => ↥(localizedPiece k K F.1 a))
    (fun F => inferInstance)

noncomputable instance localizedTermModule
    (K : Complex V) (T : Finset V) (a : V → ℤ) (p : ℕ) :
    Module k (LocalizedCechTerm k K T a p) :=
  @Pi.module (CechSlot T p) (fun F => ↥(localizedPiece k K F.1 a)) k
    inferInstance (fun F => inferInstance) (fun F => inferInstance)

/-- Coefficients are normalized using a genuine coefficient-one monomial fraction. -/
noncomputable def pieceCoordinateEquiv
    (K : Complex V) (F : Finset V) (a : V → ℤ)
    (hcriterion : LocalizationCriterion K F a) :
    k ≃ₗ[k] localizedPiece k K F a := by
  let hexists := localizedPiece_nonzero_generator k K F a hcriterion
  let m := Classical.choose hexists
  let N := Classical.choose (Classical.choose_spec hexists)
  have hspec := Classical.choose_spec (Classical.choose_spec hexists)
  exact localizedPieceEquivOfRep k K F a m N hspec.1 hspec.2.1

noncomputable def actualToModel
    (K : Complex V) (T : Finset V) (a : V → ℤ) (p : ℕ) :
    LocalizedCechTerm k K T a p →ₗ[k] (CechBasis K T a p → k) where
  toFun y F := (pieceCoordinateEquiv k K F.1 a F.2.2.2).symm
    (y ⟨F.1, F.2.1, F.2.2.1⟩)
  map_add' x y := by
    ext F
    simp only [Pi.add_apply, map_add]
  map_smul' c x := by
    ext F
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply]

noncomputable def modelToActual
    (K : Complex V) (T : Finset V) (a : V → ℤ) (p : ℕ) :
    (CechBasis K T a p → k) →ₗ[k] LocalizedCechTerm k K T a p := by
  classical
  letI : ∀ F : CechSlot T p, AddCommMonoid (localizedPiece k K F.1 a) :=
    fun F => inferInstance
  letI : ∀ F : CechSlot T p, Module k (localizedPiece k K F.1 a) :=
    fun F => inferInstance
  exact LinearMap.pi fun F : CechSlot T p =>
    if hc : LocalizationCriterion K F.1 a then
      (pieceCoordinateEquiv k K F.1 a hc).toLinearMap.comp
        (LinearMap.proj ⟨F.1, F.2.1, F.2.2, hc⟩)
    else 0

noncomputable def actualTermEquivModel
    (K : Complex V) (T : Finset V) (a : V → ℤ) (p : ℕ) :
    LocalizedCechTerm k K T a p ≃ₗ[k] (CechBasis K T a p → k) where
  __ := actualToModel k K T a p
  invFun := modelToActual k K T a p
  left_inv y := by
    classical
    funext F
    by_cases hc : LocalizationCriterion K F.1 a
    · simp [modelToActual, actualToModel, hc] <;> (cases F; rfl)
    · have hzero : localizedPiece k K F.1 a = ⊥ :=
        (localizedPiece_eq_bot_iff k K F.1 a).mpr hc
      haveI : Subsingleton (localizedPiece k K F.1 a) := by
        rw [hzero]
        infer_instance
      apply Subsingleton.elim
  right_inv x := by
    classical
    funext F
    simp [modelToActual, actualToModel, F.2.2.2] <;> (cases F; rfl)







end LPCA


