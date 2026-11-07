-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.conj6_instance_conclusion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:04:24.491839+00:00
-- url     : https://prove2.me/submissions/145d8a20-2ca6-4eb5-bc79-74d4689f56bf

import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Definitions.Def_AaronsonAmbainis_Bridge_Instance
import Theorems.Thm_AaronsonAmbainis_Bridge_conj6_instance
import Theorems.Thm_AaronsonAmbainis_Bridge_explicitBound


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution :
    ∃ i : Fin 1,
      (∑ Y : Fin 1 → Bool,
        (MvPolynomial.eval (fun k => if Y k then (1 : ℝ) else 0)
            (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)
          - MvPolynomial.eval (fun k => if Function.update Y i (!Y i) k then (1 : ℝ) else 0)
              (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)) ^ 2) / 2 ^ 1
        ≥ 8 * Real.sqrt 15 / (125 * Real.pi ^ 4) * (1 / 4 : ℝ) ^ ((5 : ℝ) / 2)
            / ((1 : ℕ) : ℝ) ^ 6 :=
  explicitBound 1 1 (MvPolynomial.X 0) conj6_instance.1 conj6_instance.2.1 (1 / 4)
    (by norm_num) (le_of_eq conj6_instance.2.2.1.symm)
end AaronsonAmbainis.Bridge
