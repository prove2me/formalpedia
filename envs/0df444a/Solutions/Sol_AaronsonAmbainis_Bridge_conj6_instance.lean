-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.conj6_instance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:39:32.655199+00:00
-- url     : https://prove2.me/submissions/765d2b91-c9e7-47cf-a07b-771dcb9b6bd4

import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Definitions.Def_AaronsonAmbainis_Bridge_Instance
import Theorems.Thm_AaronsonAmbainis_Bridge_ev01_X
import Theorems.Thm_AaronsonAmbainis_Bridge_aaInfl_X
import Theorems.Thm_AaronsonAmbainis_Bridge_variance_ev01_X
import Theorems.Thm_AaronsonAmbainis_Bridge_variance_eq_Ex


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution :
    (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ).totalDegree ≤ 1 ∧
    (∀ Y : Fin 1 → Bool,
      0 ≤ MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else 0)
            (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) ∧
        MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else 0)
            (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) ≤ 1) ∧
    (∑ Y : Fin 1 → Bool,
        (MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else 0)
            (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)
          - (∑ Z : Fin 1 → Bool, MvPolynomial.eval (fun i => if Z i then (1 : ℝ) else 0)
              (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)) / 2 ^ 1) ^ 2) / 2 ^ 1 = 1 / 4 ∧
    (∑ Y : Fin 1 → Bool,
        (MvPolynomial.eval (fun k => if Y k then (1 : ℝ) else 0)
            (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)
          - MvPolynomial.eval (fun k => if Function.update Y 0 (!Y 0) k then (1 : ℝ) else 0)
              (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)) ^ 2) / 2 ^ 1 = 1 := by
  refine ⟨(MvPolynomial.totalDegree_X _).le, fun Y => ?_, ?_, ?_⟩
  · show 0 ≤ ev01 (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) Y ∧
      ev01 (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) Y ≤ 1
    rw [ev01_X]
    split_ifs <;> norm_num
  · have h := variance_eq_Ex (ev01 (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ))
    exact h.symm.trans (variance_ev01_X 0)
  · exact aaInfl_X (0 : Fin 1)
end AaronsonAmbainis.Bridge
