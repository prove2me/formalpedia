-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
-- name    : KLS408915f_FunctionalInequalities_Energy_Form_Functional
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:33:53.937212+00:00
-- url     : https://prove2.me/theorems/c8f90d95-3fe5-4acc-be5f-69555ec4aa79
-- title:
--   Extended nonnegative energy functionals
-- statement:
--   `Energy.Functional X` is a function from a test type X to `ENNReal`, so values may be any element of $[0,\infty]$. `FiniteAt`, `domain`, and `finiteValue` record the tests where the value is not $\top$ and return its finite `NNReal` value there; `comap` pulls a functional back along a map of test spaces. The zero functional and its evaluation identities are also included.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Form/Functional.lean#L12-L106 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Form.Functional`, definition bundle `KLS408915f_FunctionalInequalities_Energy_Form_Functional`; the repository is private at upload time).

import Mathlib.Data.ENNReal.Basic

namespace FunctionalInequalities
namespace Energy
/-- An extended nonnegative energy on tests of type `X`. -/
structure Functional (X : Type*) where
  /-- The energy of a test, possibly `⊤`. -/
  toFun : X → ENNReal
namespace Functional
variable {X : Type*}
/-- An energy functional can be applied to a test. -/
instance : CoeFun (Functional X) fun _ ↦ X → ENNReal where
  coe energy := energy.toFun
/-- Applying a functional built from a function returns that function's value. -/
@[simp]
theorem mk_apply (energy : X → ENNReal) (x : X) : mk energy x = energy x := rfl
/-- Pull an extended energy back along a map of test spaces. -/
def comap {Y : Type*} (energy : Functional Y) (f : X → Y) : Functional X where
  toFun x := energy (f x)
/-- A pulled-back functional evaluates by first applying the test-space map. -/
@[simp]
theorem comap_apply {Y : Type*} (energy : Functional Y) (f : X → Y) (x : X) :
    energy.comap f x = energy (f x) :=
  rfl
/-- The energy is finite at `x`. -/
def FiniteAt (energy : Functional X) (x : X) : Prop :=
  energy x ≠ ⊤
/-- The set of tests with finite energy. It can be used as a subtype. -/
def domain (energy : Functional X) : Set X :=
  {x | energy.FiniteAt x}
/-- The finite energy as an `NNReal`.

The domain witness excludes `⊤`, so this does not use the fallback-to-zero behavior of
`ENNReal.toNNReal` on an infinite value.
-/
def finiteValue (energy : Functional X) (x : energy.domain) : NNReal :=
  (energy x.1).toNNReal
/-- The zero functional assigns zero energy to every test. -/
instance : Zero (Functional X) where
  zero := ⟨fun _ ↦ 0⟩
/-- The zero functional evaluates to zero. -/
@[simp]
theorem zero_apply (x : X) : (0 : Functional X) x = 0 := rfl
/-- The finite value of the zero functional is zero. -/
@[simp]
theorem finiteValue_zero (x : (0 : Functional X).domain) :
    (0 : Functional X).finiteValue x = 0 :=
  rfl
end Functional
end Energy
end FunctionalInequalities


