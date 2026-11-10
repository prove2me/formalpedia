-- Prove2me | Definitions.Def_GEPPGrowth_Main_ThinQR
-- name    : GEPPGrowth_Main_ThinQR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T23:35:04.563101+00:00
-- url     : https://prove2.me/theorems/752f07f1-f900-437a-932d-2f3b9f3bbfd6
-- title:
--   Thin real QR factorization with positive diagonal
-- statement:
--   For $G,Q\in\mathbb R^{n\times p}$ and $R\in\mathbb R^{p\times p}$, the thin QR relation means
--
--   $$G=QR,\qquad Q^\top Q=I_p,\qquad R_{ij}=0\ (j<i),\qquad R_{ii}>0.$$
--
--   The positive diagonal convention fixes the signs of the factors. In Lemma 4.6 the factors are measurable functions of the same Gaussian input and this relation is required almost surely, allowing arbitrary definitions on the null set of rank-deficient inputs.
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), Lemma 4.6 (factorization convention), printed p.9, PDF p.10

import Definitions.Def_GEPPGrowth_Main_Gaussian
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- The thin QR relation, with the positive diagonal convention. -/
def ThinQR {n p : ℕ} (G Q : Matrix (Fin n) (Fin p) ℝ) (R : Mat p) : Prop :=
  G = Q * R ∧ Q.transpose * Q = 1 ∧
    (∀ i j, j < i → R i j = 0) ∧ (∀ i, 0 < R i i)

end GEPPGrowth.Main


