-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.printedConcl_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:15:43.285206+00:00
-- url     : https://prove2.me/submissions/c864d15a-ff46-4e0d-9f23-2b3fdd9e7bd2

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {n : ℕ} (f : Cube (Fin n) → ℝ) (d : ℕ) :
    PrintedConcl f d ↔ ∃ c : Cube (Fin n) → Fin n → ℝ,
      (∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, c x i) ∧
      (∀ x, ∑ i, c x i ≤ Real.pi ^ 2 / 4 * (d : ℝ) ^ 2) :=
  Iff.rfl
end AaronsonAmbainis.Bridge
