-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.explicitBoundImproved_sq_of_fbsDegreeBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:58:04.8431+00:00
-- url     : https://prove2.me/submissions/8452a401-9e56-4eab-b8a7-5356f28725dd

import Definitions.Def_AaronsonAmbainis_Chain
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Definitions.Def_AaronsonAmbainis_Conjecture
import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Theorems.Thm_AaronsonAmbainis_Bridge_rowBound_of_printed
import Theorems.Thm_AaronsonAmbainis_Bridge_zo_sq_of_mainTheoremImproved
import Theorems.Thm_AaronsonAmbainis_mainTheoremImproved_of_rowBound


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (h : FbsDegreeBound) (N d : ℕ)
    (p : MvPolynomial (Fin N) ℝ) (hp : p.totalDegree ≤ d)
    (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    ∃ i, 3072 * ε ^ 5 ≤ 3125 * Real.pi ^ 8 * (d : ℝ) ^ 12
      * Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2) ^ 2 :=
  zo_sq_of_mainTheoremImproved
    (AaronsonAmbainis.mainTheoremImproved_of_rowBound (rowBound_of_printed h))
    N d p hp hrange ε hε hvar
end AaronsonAmbainis.Bridge
