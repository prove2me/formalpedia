-- Prove2me | Definitions.Def_CatalyticTreeEval_MultilinearCoordinates
-- name    : CatalyticTreeEval_MultilinearCoordinates
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T02:15:58.458574+00:00
-- url     : https://prove2.me/theorems/a5db974a-34ad-40fa-8db4-71865ad5036f
-- title:
--   Square-free monomials indexed by subsets
-- statement:
--   Associate to a finite subset the monomial whose exponents are its characteristic function. Degree-tagged subsets describe the square-free monomials of degree less than a given cutoff. Enumeration and cardinality properties are subsequent proof obligations.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Appendix B, Lemmas B.1 and B.4.

import Definitions.Def_CatalyticTreeEval_PolynomialCoordinates
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit false

namespace CatalyticTreeEval.Main

/-- The square-free monomial belonging to a subset of the variables. -/
noncomputable def squarefreeMonomial {H : ℕ} (T : Finset (Fin H)) : Monomial H :=
  ∑ i ∈ T, Finsupp.single i 1

/-- Degree-tagged subsets enumerate the square-free monomials of degree below δ. -/
abbrev SmallSubset (H δ : ℕ) := (j : Fin δ) × {T : Finset (Fin H) // T.card = j.val}

end CatalyticTreeEval.Main


