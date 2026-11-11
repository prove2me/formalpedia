-- Prove2me | Definitions.Def_ApproxCountRwPHP_Unprovability_HerbrandSyntax
-- name    : ApproxCountRwPHP_Unprovability_HerbrandSyntax
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:55:16.048206+00:00
-- url     : https://prove2.me/theorems/d5a86b53-a659-4e61-b969-a2e5aa9065e5
-- title:
--   Universal axiom matrices and ground substitution
-- statement:
--   A universal axiom certificate contains a finite number of variable positions, a quantifier-free matrix, and membership of its universal closure in the given theory. Ground substitution replaces each displayed variable with a closed term, including terms involving fresh parameter constants.
--
--   $$\theta(\bar s(\bar c))$$
--
--   Finite conjunction and disjunction use truth and falsity for their empty cases. Certificates name actual axioms, rather than arbitrary consequences of the theory. The language remains completely general and may contain relations as well as functions and equality.
-- source:
--   Oliver Korten, Jiatu Li, Igor Oliveira, Hanlin Ren, STOC 2027 submission #1023 (October 2026), Theorem 2.1, printed p. 14, PDF p. 16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1023.pdf#page=16

import Mathlib

open FirstOrder

namespace ApproxCountRwPHP.Unprovability

/-- A universal axiom with its actual quantifier-free matrix, not an arbitrary
consequence of the theory. Source: Theorem 2.1, printed 14 / PDF 16. -/
structure UniversalAxiom {K : Language} (T : K.Theory) where
  variableCount : ℕ
  matrix : K.BoundedFormula Empty variableCount
  quantifierFree : matrix.IsQF
  membership : matrix.alls ∈ T

/-- Ground substitution into all the displayed variableCount; equality and every
relation of the arbitrary original language are preserved. -/
def groundSubstitution {K : Language} {n : ℕ}
    (φ : K.BoundedFormula Empty n) (ts : Fin n → K.Term Empty) : K.Sentence :=
  φ.toFormula.subst (Sum.elim Empty.elim ts)

def axiomGroundInstance {K : Language} {T : K.Theory} {p : ℕ}
    (A : UniversalAxiom T) (ts : Fin A.variableCount → K[[Fin p]].Term Empty) : K[[Fin p]].Sentence :=
  groundSubstitution ((K.lhomWithConstants (Fin p)).onBoundedFormula A.matrix) ts

def conjunction {K : Language} (xs : List K.Sentence) : K.Sentence := xs.foldr (· ⊓ ·) ⊤

def disjunction {K : Language} (xs : List K.Sentence) : K.Sentence := xs.foldr (· ⊔ ·) ⊥

end ApproxCountRwPHP.Unprovability


