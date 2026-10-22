-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CechTermGrading_Defs
-- name    : LPCA_Solutions_LPCA_CechTermGrading_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:26:36.164898+00:00
-- url     : https://prove2.me/theorems/c2455414-10c9-4f11-9afe-1c984497c5dd
-- title:
--   Čech Term Grading for localized persistent commutative algebra
-- statement:
--   This bundle supplies čech Term Grading for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The existing fixed-degree term is precisely the homogeneous submodule of the full, ungraded product term.
--   - Every actual full Cech term is the direct sum of its previously defined fixed-degree terms. Finiteness is in subset slots, not in integer degrees.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_CechTermGrading.lean, selected declarations in lines 17–67; source SHA-256 edd90ee33804ada23e25644d6bf4693ec6a8be3d9f2bdea72276e117addbd7e5; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.MonoidAlgebra.Basic
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
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LaurentFaceEvaluation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDegreeSeparation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedGradingSpan_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

attribute [local instance 2000] localizedTermAddCommGroup localizedTermModule

noncomputable local instance (priority := 3000) cechGradingTermAddCommMonoid
    (K : Complex V) (T : Finset V) (a : V → ℤ) (p : ℕ) :
    AddCommMonoid (LocalizedCechTerm k K T a p) :=
  (localizedTermAddCommGroup k K T a p).toAddCommMonoid

abbrev FullCechTerm (K : Complex V) (T : Finset V) (p : ℕ) : Type u :=
  ∀ F : CechSlot T p, LocalizedFaceRing k K F.1

noncomputable abbrev cechTermPiece (K : Complex V) (T : Finset V) (p : ℕ) (a : V → ℤ) :
    Submodule k (FullCechTerm k K T p) :=
  finitePiPiece (fun F : CechSlot T p => localizedPiece k K F.1) a

/-- The existing fixed-degree term is precisely the homogeneous submodule
of the full, ungraded product term. -/
noncomputable def cechTermPieceEquiv (K : Complex V) (T : Finset V)
    (p : ℕ) (a : V → ℤ) :
    LocalizedCechTerm k K T a p ≃ₗ[k] cechTermPiece k K T p a where
  toFun y := ⟨fun F => (y F).1, fun F _ => (y F).2⟩
  invFun y F := ⟨y.1 F, (Submodule.mem_pi.mp y.2) F (Set.mem_univ F)⟩
  left_inv y := by rfl
  right_inv y := by rfl
  map_add' x y := rfl
  map_smul' c y := rfl

theorem cechTermGradingIsInternal (K : Complex V) (T : Finset V) (p : ℕ) :
    DirectSum.IsInternal (cechTermPiece k K T p) := by
  classical
  exact finitePiGradingIsInternal _ (fun F : CechSlot T p =>
    localizedGradingIsInternal k K F.1)

/-- Every actual full Cech term is the direct sum of its previously defined
fixed-degree terms. Finiteness is in subset slots, not in integer degrees. -/
noncomputable def cechTermSumEquiv (K : Complex V) (T : Finset V) (p : ℕ) :
    DirectSum (V → ℤ) (fun a => LocalizedCechTerm k K T a p) ≃ₗ[k]
      FullCechTerm k K T p := by
  classical
  exact (DirectSum.congrLinearEquiv (fun a => cechTermPieceEquiv k K T p a)).trans
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap (cechTermPiece k K T p))
      (cechTermGradingIsInternal k K T p))

theorem cechTermSumEquiv_lof (K : Complex V) (T : Finset V) (p : ℕ)
    (a : V → ℤ) (y : LocalizedCechTerm k K T a p) :
    cechTermSumEquiv k K T p
        (DirectSum.lof k (V → ℤ) (fun b => LocalizedCechTerm k K T b p) a y) =
      fun F => (y F).1 := by
  classical
  change DirectSum.coeLinearMap (cechTermPiece k K T p)
    (DirectSum.lmap (fun b => (cechTermPieceEquiv k K T p b).toLinearMap)
      (DirectSum.lof k (V → ℤ) (fun b => LocalizedCechTerm k K T b p) a y)) = _
  rw [DirectSum.lmap_lof, DirectSum.coeLinearMap_lof]
  rfl

end LPCA


