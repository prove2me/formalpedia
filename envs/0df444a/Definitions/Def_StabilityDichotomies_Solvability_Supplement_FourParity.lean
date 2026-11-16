-- Prove2me | Definitions.Def_StabilityDichotomies_Solvability_Supplement_FourParity
-- name    : StabilityDichotomies_Solvability_Supplement_FourParity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:35:41.521498+00:00
-- url     : https://prove2.me/theorems/f1015bcc-8d0c-4754-94c1-ad25acf70f55
-- title:
--   The four-variable parity language Λ₄
-- statement:
--   For b ∈ {0,1}, let R_b be the relation of arity four given by
--
--   $$R_b=\{x\in\{0,1\}^4:x_1\oplus x_2\oplus x_3\oplus x_4=b\},\qquad\Lambda_4=\{R_0,R_1\}.$$
--
--   Here ⊕ is Boolean exclusive-or. Both relations are nonempty: the tuple (b,0,0,0) belongs to R_b. The language has both parity relations and uses the existing unrestricted constraint model. Its four argument positions can receive repeated variables; for example R_b(u,v,u,u) is the equation u ⊕ v = b.
--
--   This is the fixed source language for Proposition 4.11 and the approximation lower branch. **Formalization Note** The four positions are numbered 0 through 3 in Lean, and neither relation depends on any algorithm or code family.
-- source:
--   Chunyang Wang, Yuichi Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535 (October 2026), canonical source.pdf, SHA-256 9eeb0875db685945a8b4c78bc4d30bfdbf3289a943d06f464836530d0eb22467. p.24, Section 4.3.1, parity-relation display immediately before Proposition 4.11.

import Definitions.Def_StabilityDichotomies_Solvability_Model

noncomputable section
open scoped Classical

namespace StabilityDichotomies.Solvability.Supplement

/-- The XOR of the four argument positions, which remain distinct positions even under substitution. -/
def fourParity (x : Fin 4 → Bool) : Bool :=
  Bool.xor (Bool.xor (Bool.xor (x 0) (x 1)) (x 2)) (x 3)

/-- Section 4.3.1, p.24: R_b consists of all four-bit tuples of parity b. -/
def parityRelation (b : Bool) : Relation where
  arity := 4
  arity_pos := by decide
  tuples := Finset.univ.filter (fun x : Fin 4 → Bool => fourParity x = b)
  tuples_nonempty := by
    refine ⟨(fun i => if i = 0 then b else false), ?_⟩
    simp [fourParity]

/-- The entire language Λ₄ = {R₀,R₁}, with unrestricted scopes in the base CSP model. -/
def parityLanguage : Language where
  relations := {parityRelation false, parityRelation true}
  relations_nonempty := by simp

end StabilityDichotomies.Solvability.Supplement


