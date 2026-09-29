-- Prove2me | solution 1 for AddChar.exists_continuousLinearMap_fourierChar_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/bad39063-8b44-50aa-a09a-2e94f746d255

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddChar_exists_continuousLinearMap_fourierChar_eq

set_option autoImplicit false

open scoped FourierTransform
open Real

theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : AddChar E Circle) (hχ : Continuous χ) :
    ∃ l : E →L[ℝ] ℝ, ∀ x, χ x = 𝐞 (l x) := by

  obtain ⟨F, ⟨hF0, hFlift⟩, huniq⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts (⟨χ, hχ⟩ : C(E, Circle)) 0 0
      (by simp)
  have hF : ∀ x, Circle.exp (F x) = χ x := fun x => congrFun hFlift x

  have hadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    let G : C(E, ℝ) := ⟨fun z => F (z + y) - F y, by fun_prop⟩
    have hG : G = F := by
      refine huniq G ⟨by simp [G], ?_⟩
      funext z
      simp only [Function.comp_apply, ContinuousMap.coe_mk, G, Circle.exp_sub, hF,
        AddChar.map_add_eq_mul, mul_div_cancel_right]
    have := congrArg (fun (H : C(E, ℝ)) => H x) hG
    simp only [G, ContinuousMap.coe_mk] at this
    linarith

  let Fhom : E →+ ℝ := { toFun := F, map_zero' := hF0, map_add' := hadd }
  let l₀ : E →L[ℝ] ℝ := Fhom.toRealLinearMap F.continuous
  refine ⟨(2 * π)⁻¹ • l₀, fun x => ?_⟩
  rw [Real.fourierChar_apply', ContinuousLinearMap.smul_apply, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (by positivity), one_mul]
  exact (hF x).symm

end S_AddChar_exists_continuousLinearMap_fourierChar_eq
end P2MW
export P2MW.S_AddChar_exists_continuousLinearMap_fourierChar_eq (solution)
