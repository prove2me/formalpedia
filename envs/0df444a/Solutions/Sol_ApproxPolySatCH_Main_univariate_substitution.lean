-- Prove2me | solution 1 for ApproxPolySatCH.Main.univariate_substitution
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:40:45.9944+00:00
-- url     : https://prove2.me/submissions/c649650a-e9e8-4a3c-a27c-f6b156b141f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages
import Theorems.Thm_ApproxPolySatCH_Main_univariate_substitution_coefficient_valuations
import Theorems.Thm_ApproxPolySatCH_Main_gauss_strict_of_valuation_shift

set_option autoImplicit false

open ApproxPolySatCH.Main

theorem solution {k : Type} [Field k] (v : EpsilonValuation k)
    (P : Poly k 4) (hP : P ≠ 0) (D0 : ℕ)
    (hT : MvPolynomial.degreeOf 0 P ≤ D0) (hW : MvPolynomial.degreeOf 1 P ≤ D0)
    (heps : MvPolynomial.degreeOf 2 P ≤ D0) :
    kroneckerSubstitution D0 P ≠ 0 ∧
      (let P2 := asZPolynomial (twiceTrailing (MvPolynomial.map (algebraMap k (Constants k)) P))
       let Phat := asZPolynomial (MvPolynomial.map (algebraMap k (Constants k))
         (kroneckerSubstitution D0 P))
       gaussValuation v P2 < v.val (P2.eval 0) ↔
         gaussValuation v Phat < v.val (Phat.eval 0)) := by
  let P2 := asZPolynomial (twiceTrailing (MvPolynomial.map (algebraMap k (Constants k)) P))
  let Phat := asZPolynomial (MvPolynomial.map (algebraMap k (Constants k))
    (kroneckerSubstitution D0 P))
  obtain ⟨hsubst, hP2, N, hmatch, htail⟩ :=
    univariate_substitution_coefficient_valuations v P hP D0 hT hW heps
  refine ⟨hsubst, ?_⟩
  exact gauss_strict_of_valuation_shift v P2 Phat D0 N hP2
    (fun i hi => (hmatch i hi).1) (fun i hi => (hmatch i hi).2) htail
