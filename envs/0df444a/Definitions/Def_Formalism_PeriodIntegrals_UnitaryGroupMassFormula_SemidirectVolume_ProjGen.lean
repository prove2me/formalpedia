-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:07:40.165818+00:00
-- url     : https://prove2.me/theorems/76836f4a-29a7-427e-ac31-32cebddf816e
-- title:
--   Proj Gen
-- statement:
--   Definitions and structural lemmas for Proj Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProjGen.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolSemiDirect.W.PG
open Formalism.UG
structure Dat (A : Type) [CommRing A] (n : Type) (r : ℕ) where
  σA : A →+* A
  JA : Matrix n n A
  e : Fin r → n → A
  f : Fin r → n → A
  z : n → A
  tz : A
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
namespace Dat
variable (D : Dat A n r)
def h (x y : n → A) : A := hform D.σA D.JA x y
def hL (x : n → A) : (n → A) →ₗ[A] A where
  toFun y := D.h x y
  map_add' y y' := by
    simp only [h, hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [h, hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
structure Hyp : Prop where
  σσ : ∀ x, D.σA (D.σA x) = x
  herm : ∀ i j, D.σA (D.JA j i) = D.JA i j
  ee : ∀ a b, D.h (D.e a) (D.e b) = 0
  ff : ∀ a b, D.h (D.f a) (D.f b) = 0
  ef : ∀ a b, D.h (D.e a) (D.f b) = if a = b then 1 else 0
  ez : ∀ a, D.h (D.e a) D.z = 0
  fz : ∀ a, D.h (D.f a) D.z = 0
  zz : D.tz * D.h D.z D.z = 1
variable {D}
variable (D)
def pX : (n → A) →ₗ[A] (n → A) := ∑ a, (D.hL (D.f a)).smulRight (D.e a)
def pXv : (n → A) →ₗ[A] (n → A) := ∑ a, (D.hL (D.e a)).smulRight (D.f a)
def pz : (n → A) →ₗ[A] (n → A) := (D.tz • D.hL D.z).smulRight D.z
def pU : (n → A) →ₗ[A] (n → A) := D.pX + D.pXv + D.pz
def pW : (n → A) →ₗ[A] (n → A) := LinearMap.id - D.pU
def Pi (S : (n → A) →ₗ[A] (n → A)) : (n → A) →ₗ[A] (n → A) := D.pU + D.pW ∘ₗ S ∘ₗ D.pW
variable {D}
def IsW (D : Dat A n r) (w : n → A) : Prop :=
  (∀ a, D.h (D.e a) w = 0) ∧ (∀ a, D.h (D.f a) w = 0) ∧ D.h D.z w = 0
end Dat
end PI.VolSemiDirect.W.PG


