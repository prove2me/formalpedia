-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexPolynomial
-- name    : liuyao_ca_fd889115_k1_Analysis_ComplexPolynomial
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:49:42.214208+00:00
-- url     : https://prove2.me/theorems/508cd999-dda1-4e3b-b7ed-e405be4221af
-- title:
--   Computable analysis · ComplexPolynomial · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/ComplexPolynomial.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Basic

set_option autoImplicit true

namespace ComputableAnalysis

namespace CPoly

abbrev Coeffs := List QComplex

def eval (coeffs : Coeffs) (z : QComplex) : QComplex :=
  coeffs.foldr (fun c acc => QComplex.add c (QComplex.mul z acc)) QComplex.zero

def degreeBound (coeffs : Coeffs) : Nat :=
  coeffs.length

def coeffNonzero (c : QComplex) : Bool :=
  decide (c != QComplex.zero)

def isZeroPoly (coeffs : Coeffs) : Bool :=
  coeffs.all (fun c => decide (c = QComplex.zero))

def positiveDegree (coeffs : Coeffs) : Prop :=
  Exists fun n : Nat => Exists fun c : QComplex =>
    coeffs[n]? = some c /\ n != 0 /\ c != QComplex.zero

def hasExactRoot (coeffs : Coeffs) (z : QComplex) : Prop :=
  eval coeffs z = QComplex.zero

end CPoly

end ComputableAnalysis


