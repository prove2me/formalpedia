-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.problemPM_instance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:36:36.151873+00:00
-- url     : https://prove2.me/submissions/3a644d04-2219-4a42-a9fb-e3cc56847ae2

import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Definitions.Def_AaronsonAmbainis_Bridge_Instance
import Theorems.Thm_AaronsonAmbainis_Bridge_evPM_X
import Theorems.Thm_AaronsonAmbainis_Bridge_evPM_X_eq_dict
import Theorems.Thm_AaronsonAmbainis_Bridge_evPMt_bound_iff
import Theorems.Thm_AaronsonAmbainis_Bridge_inflR_dict_self
import Theorems.Thm_AaronsonAmbainis_Bridge_inflR_eq_Ex
import Theorems.Thm_AaronsonAmbainis_Bridge_infl_evPMt
import Theorems.Thm_AaronsonAmbainis_Bridge_variance_dict
import Theorems.Thm_AaronsonAmbainis_Bridge_variance_eq_Ex
import Theorems.Thm_AaronsonAmbainis_Bridge_variance_evPMt
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_flipSet_singleton
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_singleton_self
import Theorems.Thm_AaronsonAmbainis_Row_sgn_false
import Theorems.Thm_AaronsonAmbainis_Row_sgn_true
attribute [local simp] AaronsonAmbainis.DetLow.flipSet_flipSet_singleton
attribute [local simp] AaronsonAmbainis.DetLow.flipSet_singleton_self
attribute [local simp] AaronsonAmbainis.Row.sgn_false
attribute [local simp] AaronsonAmbainis.Row.sgn_true



set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution :
    (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ).totalDegree ≤ 1 ∧
    (∀ Y : Fin 1 → Bool,
      |MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else -1)
          (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)| ≤ 1) ∧
    (∑ Y : Fin 1 → Bool,
        (MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else -1)
            (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)
          - (∑ Z : Fin 1 → Bool, MvPolynomial.eval (fun i => if Z i then (1 : ℝ) else -1)
              (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)) / 2 ^ 1) ^ 2) / 2 ^ 1 = 1 ∧
    (∑ Y : Fin 1 → Bool,
        ((MvPolynomial.eval (fun k => if Y k then (1 : ℝ) else -1)
            (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)
          - MvPolynomial.eval (fun k => if Function.update Y 0 (!Y 0) k then (1 : ℝ) else -1)
              (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)) / 2) ^ 2) / 2 ^ 1 = 1 := by
  refine ⟨(MvPolynomial.totalDegree_X _).le, ?_, ?_, ?_⟩
  · show ∀ Y, |evPMt (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) Y| ≤ 1
    rw [evPMt_bound_iff]
    intro Y
    rw [evPM_X]
    split_ifs <;> simp
  · show Ex (fun Y => (evPMt (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) Y
        - Ex (evPMt (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ))) ^ 2) = 1
    rw [variance_evPMt]
    have h := variance_eq_Ex (evPM (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ))
    have h1 : variance (evPM (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) : Cube (Fin 1) → ℝ)
        = 1 := by
      rw [evPM_X_eq_dict, variance_dict]
    exact h.symm.trans h1
  · show Ex (fun Y => ((evPMt (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) Y
        - evPMt (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) (flipBit Y 0)) / 2) ^ 2) = 1
    rw [infl_evPMt]
    have h := inflR_eq_Ex (evPM (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)) 0
    have h1 : inflR (evPM (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) : Cube (Fin 1) → ℝ) 0
        = 1 := by
      rw [evPM_X_eq_dict, inflR_dict_self]
    exact h.symm.trans h1
end AaronsonAmbainis.Bridge
