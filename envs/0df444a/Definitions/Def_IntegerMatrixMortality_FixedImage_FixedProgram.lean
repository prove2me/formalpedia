-- Prove2me | Definitions.Def_IntegerMatrixMortality_FixedImage_FixedProgram
-- name    : IntegerMatrixMortality_FixedImage_FixedProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:29:44.96118+00:00
-- url     : https://prove2.me/theorems/bdc0c92a-829b-4968-b6c6-3c41ad8f44b1
-- title:
--   The concrete reversed prime-exponent program
-- statement:
--   Construct P from the fixed quotient machine U. Reverse an increment of counter zero or one into Div₂ or Div₃. Reverse a positive decrement branch into Con₂ or Con₃. Reverse its zero branch into Test(2,{0}) or Test(3,{0,1}), respectively. Add the reversed cleanup edge, an Inc loop at state 278. Every reversed edge has the destinations specified by U, in reversed order. Its fixed source and input-dependent target are
--
--   $$(278,0),\qquad(1,2^\rho-1),\quad\rho\in\mathbb N.$$
--
--   The construction reverses exactly the forward simulation on n+1, where counter values are its exponents at 2 and 3. The positive forward branches multiply by 5/2 and 5/3, so the factor 5 is retained in the reversed contractions. No simulation or undecidability property is assumed in defining P.
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), §§4.2–4.3, PDF pp. 7–8 / printed pp. 5–6; Appendix B.3, PDF pp. 16–17 / printed pp. 14–15

import Mathlib
import Definitions.Def_IntegerMatrixMortality_FixedImage_ArithmeticProgram
import Definitions.Def_IntegerMatrixMortality_FixedImage_SourceMachine

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage
/-- Reverses exactly the forward simulation branches, including the factor 5. -/
def reversedEdgesAt (q : ℕ) : List InstructionEdge :=
  match U q with
  | .inc .zero r => [⟨r, q, .div2⟩]
  | .inc .one r => [⟨r, q, .div3⟩]
  | .dec .zero r s => [⟨r, q, .con2⟩, ⟨s, q, .test 2 {0}⟩]
  | .dec .one r s => [⟨r, q, .con3⟩, ⟨s, q, .test 3 {0,1}⟩]
  | .halt => []

def fixedInstructionEdges : List InstructionEdge :=
  ((((List.range 278).map (fun q => mergeState (q+1))).dedup).flatMap reversedEdgesAt) ++ [⟨278,278,.inc⟩]

def P : ArithmeticProgram := ⟨uStates,
  fixedInstructionEdges.map (fun e => ⟨e.source,e.target,instructionUpdate e.instruction⟩)⟩

end IntegerMatrixMortality.FixedImage


