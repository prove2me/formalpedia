-- Prove2me | Definitions.Def_QAlgorithms_Defs_PrimeFieldDQIMoments
-- name    : QAlgorithms_Defs_PrimeFieldDQIMoments
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:20:31.955791+00:00
-- url     : https://prove2.me/theorems/c85e4b7a-abbd-4775-9d11-39894ef19aeb
-- title:
--   PrimeFieldDQIMoments
-- statement:
--   PrimeFieldDQIMoments
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\PrimeFieldDQIMoments.lean

import Definitions.Def_QAlgorithms_Defs_DQI
import Definitions.Def_QAlgorithms_Defs_FieldCodeGeometry
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.PrimeFieldDQI

/-- Already-normalized real polynomial probability weights; 2607.28120 pp.3,13.
The normalization binder excludes zero or arbitrary unnormalized polynomials.
No averaging over the acceptance sets occurs. -/
def realPolynomialWeights {p m n : ℕ} [NeZero p]
    (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p))
    (P : Polynomial ℝ)
    (_normalized : ∑ x : Fin n → ZMod p, (P.eval (linsatObjective B F x : ℝ))^2 = 1) :
    (Fin n → ZMod p) → ℝ :=
  fun x => (P.eval (linsatObjective B F x : ℝ))^2

example {p m n : ℕ} [NeZero p] (B : Matrix (Fin m) (Fin n) (ZMod p))
    (F : Fin m → Finset (ZMod p)) (P : Polynomial ℝ)
    (h : ∑ x : Fin n → ZMod p, (P.eval (linsatObjective B F x : ℝ))^2 = 1) :
    ∑ x, realPolynomialWeights B F P h x = 1 := h

end QAlgorithms.PrimeFieldDQI


