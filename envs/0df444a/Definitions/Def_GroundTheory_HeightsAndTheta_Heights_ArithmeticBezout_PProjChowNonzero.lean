-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjChowNonzero
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjChowNonzero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:22.922504+00:00
-- url     : https://prove2.me/theorems/2a17d326-99ec-4b33-8951-be3ee78a3056
-- title:
--   PProj Chow Nonzero
-- statement:
--   Definitions and structural lemmas for PProj Chow Nonzero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjChowNonzero.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjChowNonzero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace ProjChowNonzero
abbrev Loc (e : ℕ) : Type := Localization.Away (X 0 : MvPolynomial (Fin (e + 1)) ℂ)
theorem projVar_zero_ne (e : ℕ) : projVar e 0 ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Fin (e + 1)) ℂ) _)).mpr (X_ne_zero 0)
def toK (e : ℕ) : Loc e →+* FractionRing (MvPolynomial (Fin (e + 1)) ℂ) :=
  IsLocalization.Away.lift (X 0) (g := algebraMap _ _) (IsUnit.mk0 _ (projVar_zero_ne e))
def pt (e : ℕ) : Fin (e + 1) → ℂ := fun i => if i = 0 then 1 else 0
def atPt (e : ℕ) : Loc e →+* AlgebraicClosure ℂ :=
  IsLocalization.Away.lift (X 0) (g := (algebraMap ℂ (AlgebraicClosure ℂ)).comp (eval (pt e)))
    (by simp [pt])
def locPar {n e : ℕ} (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (ij : Fin (e + 1) × Fin n) : Loc e :=
  Fin.cases (motive := fun _ => Loc e)
    (algebraMap ℂ (Loc e) (A 0 ij.2) * IsLocalization.Away.invSelf (X 0 : MvPolynomial (Fin (e + 1)) ℂ))
    (fun i => algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (Loc e)
      (X i.succ * C (A 0 ij.2) - X 0 * C (A i.succ ij.2))) ij.1
end ProjChowNonzero
end
end GroundTheory.Heights₂.Heights


