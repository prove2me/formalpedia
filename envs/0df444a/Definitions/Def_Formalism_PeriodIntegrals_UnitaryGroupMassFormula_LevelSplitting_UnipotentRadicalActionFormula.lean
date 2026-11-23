-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:26:27.062863+00:00
-- url     : https://prove2.me/theorems/30fd5306-c349-479a-8444-1f4b1434b93e
-- title:
--   Unipotent Radical Action Formula
-- statement:
--   Definitions and structural lemmas for Unipotent Radical Action Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/UnipotentRadicalActionFormula.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LevelKSplit.W.NCH
open PI.VolSemiDirect.W.PG PI.VolSemiDirect.W.PG.Dat
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
def Xp (D : Dat A n r) (v : n → A) : Prop := ∀ a, D.h (D.e a) v = 0
def IsWp (D : Dat A n r) (w : n → A) : Prop :=
  (∀ a, D.h (D.e a) w = 0) ∧ ∀ a, D.h (D.f a) w = 0
def pWp (D : Dat A n r) : (n → A) →ₗ[A] (n → A) := LinearMap.id - D.pX - D.pXv
structure Half (D : Dat A n r) (half : A) : Prop where
  two : half + half = 1
  sig : D.σA half = half
def cf (D : Dat A n r) (half : A) (y : Fin r → n → A) (a b : Fin r) : A :=
  -(half * D.h (y b) (y a))
def uv (D : Dat A n r) (half : A) (y : Fin r → n → A) (a : Fin r) : n → A :=
  y a + ∑ b, cf D half y a b • D.e b
def sL (D : Dat A n r) (half : A) (y : Fin r → n → A) : (n → A) →ₗ[A] (n → A) :=
  LinearMap.id + ∑ a, (D.hL (D.e a)).smulRight (uv D half y a) -
    ∑ b, (D.hL (y b)).smulRight (D.e b)
def tV (D : Dat A n r) (half : A) (y : Fin r → n → A) (v : n → A) : n → A :=
  ∑ a, D.h (D.e a) v • uv D half y a - ∑ b, D.h (y b) v • D.e b
variable {D : Dat A n r}
section Sec
variable (H : D.Hyp) {half : A} {y : Fin r → n → A} (hy : ∀ a, IsWp D (y a))
include H hy
end Sec
def ND (D : Dat A n r) : Prop := ∀ x : n → A, (∀ v, D.h v x = 0) → x = 0
end PI.LevelKSplit.W.NCH


