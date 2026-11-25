-- Prove2me | solution 1 for AllOnesLab.trace_sq_add_self_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:54:44.277136+00:00
-- url     : https://prove2.me/submissions/9c02bfff-caa5-4e19-905a-a96c62581bf0

import Definitions.Def_AllOnesLab_Basic
import Definitions.Def_AllOnesLab_Trace
section
open Polynomial
namespace AllOnesLab
private lemma zmod_two_add_self : ∀ t : ZMod 2, t + t = 0 := by decide
end AllOnesLab
end

set_option autoImplicit true
open Polynomial
open AllOnesLab
namespace AllOnesLab
theorem _root_.solution {K : Type*} [Field K] [Algebra (ZMod 2) K]
    [FiniteDimensional (ZMod 2) K] (z : K) :
    Algebra.trace (ZMod 2) K (z ^ 2 + z) = 0 := by
  haveI halg : Algebra.IsAlgebraic (ZMod 2) K := Algebra.IsAlgebraic.of_finite (ZMod 2) K
  -- the Frobenius `x ↦ x ^ 2` is a `ZMod 2`-algebra automorphism of `K`
  let e : K ≃ₐ[ZMod 2] K := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K
  have hcard : Fintype.card (ZMod 2) = 2 := by simp
  have hez : e z = z ^ 2 := by
    have h1 : e z = z ^ Fintype.card (ZMod 2) :=
      congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic (ZMod 2) K) z
    rw [h1, hcard]
  have hsq : Algebra.trace (ZMod 2) K (z ^ 2) = Algebra.trace (ZMod 2) K z := by
    rw [← hez]
    exact Algebra.trace_eq_of_algEquiv e z
  rw [map_add, hsq, zmod_two_add_self]
end AllOnesLab
