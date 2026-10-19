-- Prove2me | Definitions.Def_QAlgorithms_Defs_SchurCharacters
-- name    : QAlgorithms_Defs_SchurCharacters
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:38:04.003528+00:00
-- url     : https://prove2.me/theorems/2830081e-87e7-4dfd-9609-31dc08e2647c
-- title:
--   SchurCharacters
-- statement:
--   SchurCharacters
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\SchurCharacters.lean

import Definitions.Def_QAlgorithms_Defs_SchurShapes
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Schur

/-- Bounded-alphabet fillings weakly increasing along rows and strictly along columns;
Fin d is the source's alphabet [d] in zero-based form (1508.01797 pp.4-5). -/
def IsSemistandardFilling {d n : ℕ} (lambda : Partition d n) (T : lambda.val.cells → Fin d) :
    Prop :=
  ∀ a b : lambda.val.cells,
    (a.val.1 = b.val.1 → a.val.2 < b.val.2 → T a ≤ T b) ∧
    (a.val.2 = b.val.2 → a.val.1 < b.val.1 → T a < T b)

/-- Source Schur polynomial as a sum of monomials over all bounded-alphabet SSYTs;
Kostka multiplicities arise by grouping equal weights (1508.01797 p.5, Eq.(5)). -/
def schurPolynomial {d n : ℕ} (lambda : Partition d n) : MvPolynomial (Fin d) ℝ :=
  ∑ T ∈ Finset.univ.filter (IsSemistandardFilling lambda),
    ∏ a : lambda.val.cells, MvPolynomial.X (T a)

/-- The source representation dimension s_lambda(1,...,1), determined by the shape
(1508.01797 p.5, §III; 1508.01907 pp.4-5). -/
def schurDimension {d n : ℕ} (lambda : Partition d n) : ℝ :=
  MvPolynomial.eval (fun _ => 1) (schurPolynomial lambda)

example {d n : ℕ} (lambda : Partition d n) :
    schurDimension lambda =
      ((Finset.univ.filter (IsSemistandardFilling lambda)).card : ℝ) := by
  simp [schurDimension, schurPolynomial]

end QAlgorithms.Schur


