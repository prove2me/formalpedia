-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TestObj
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TestObj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:02:25.773804+00:00
-- url     : https://prove2.me/theorems/86c531e2-87cf-4ebe-b7c8-d4956111adb0
-- title:
--   Test Obj
-- statement:
--   Definitions and structural lemmas for Test Obj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/TestObj.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.Test
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
lemma tensor_punit_eq_zero (x : ℝ ⊗[ℤ] PUnit.{1}) : x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul r u => rw [Subsingleton.elim u 0, TensorProduct.tmul_zero]
  | add a b ha hb => rw [ha, hb, add_zero]
instance : Subsingleton (ℝ ⊗[ℤ] PUnit.{1}) :=
  ⟨fun a b => by rw [tensor_punit_eq_zero a, tensor_punit_eq_zero b]⟩
def zeroDatum (H : Host E) : Datum H where
  La := PUnit
  fin := inferInstance
  proj := inferInstance
  EF := 0
  alt _ := rfl
  unimod := ⟨fun _ _ _ => Subsingleton.elim _ _, fun f => ⟨PUnit.unit, LinearMap.ext fun x => by
    have : x = 0 := Subsingleton.elim _ _
    subst this
    exact (map_zero f).symm⟩⟩
  adj _ _ _ := rfl
  p := 0
  q := 0
  rank := Module.finrank_zero_of_subsingleton
  dom := ⟨0, fun _ => Subsingleton.elim _ _, fun _ _ => by simp, fun x hx => absurd (Subsingleton.elim x 0) hx,
    fun a A t _ ht => by
      have hA : A = 0 := LinearMap.ext fun _ => Subsingleton.elim _ _
      subst hA
      simp [ht]⟩
example (H : Host E) : (zeroDatum H).p * (zeroDatum H).q = 0 := rfl
def trivLB (X : Scheme.{0}) : LB X := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩
example (H : Host E) (l : Level H) : l.GoodAt 1 ↔ 3 ≤ l.M := by
  simp [Level.GoodAt, Nat.factorization_eq_zero_of_not_prime _ Nat.not_prime_one]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor.Test


