-- Prove2me | Definitions.Def_QAlgorithms_Defs_MatrixQSVTCompletion
-- name    : QAlgorithms_Defs_MatrixQSVTCompletion
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:23:59.557711+00:00
-- url     : https://prove2.me/theorems/6737228d-32e0-4b39-9d38-e3113b2dc5af
-- title:
--   MatrixQSVTCompletion
-- statement:
--   MatrixQSVTCompletion
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\MatrixQSVTCompletion.lean

import Definitions.Def_QAlgorithms_Defs_MatrixQSVTData
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.MatrixQSVT

/-- QAlgorithms.MatrixQSVT.IsComplementaryCompletion: arxiv-2408.01439v4 PDF p.8, arxiv-2408.01439v4 PDF p.9. Source domains are explicit below. -/
def IsComplementaryCompletion {r c d a b : ℕ} (P : PolynomialData r c d)
    (P1 : Matrix (Fin a) (Fin c) (Polynomial ℂ))
    (Q1 : Matrix (Fin b) (Fin c) (Polynomial ℂ)) : Prop :=
  (∀ i j, (P1 i j).natDegree ≤ d ∧ HasParity (P1 i j) d) ∧
  (if d = 0 then Q1 = 0 else ∀ i j, (Q1 i j).natDegree ≤ d-1 ∧ HasParity (Q1 i j) (d-1)) ∧
  ∀ x ∈ Set.Icc (-1 : ℝ) 1,
    let V := P.eval x
    let V1 := P1.map (Polynomial.eval (x : ℂ))
    let W1 := Q1.map (Polynomial.eval (x : ℂ))
    Vᴴ*V+V1ᴴ*V1+((1-x^2 : ℝ) : ℂ) • (W1ᴴ*W1) = 1

example {r c a b : ℕ} (P : PolynomialData r c 0)
    (P1 : Matrix (Fin a) (Fin c) (Polynomial ℂ))
    (Q1 : Matrix (Fin b) (Fin c) (Polynomial ℂ)) (h : IsComplementaryCompletion P P1 Q1) :
    Q1 = 0 := by simpa using h.2.1

end QAlgorithms.MatrixQSVT


