-- Prove2me | Definitions.Def_Kyprianou_Ch06_TimePositionCharFun
-- name    : Kyprianou_Ch06_TimePositionCharFun
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:09:49.978522+00:00
-- url     : https://prove2.me/theorems/853c7f13-9d1e-4580-ac71-efde0190a10a
-- title:
--   Joint characteristic function of a time-position law
-- statement:
--   Defines the joint characteristic function of a nonnegative chronological time and a d-dimensional real position, with a full coordinatewise dot product. Used to state the Lévy–Khintchine factorisation and infinite divisibility without collapsing d to one.
-- source:
--   Kyprianou (2006), Lemma 6.17, printed p. 160, equation before its proof.

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Joint characteristic function of time and a d-dimensional position
under an arbitrary probability measure on nonnegative time-position pairs. -/
noncomputable def TimePositionCharFun
    (d : Nat) (mu : Measure (NNReal × (Fin d → Real)))
    (vartheta : Real) (theta : Fin d → Real) : Complex :=
  ∫ z : NNReal × (Fin d → Real),
    Complex.exp (Complex.I *
      (↑(vartheta * (z.1 : Real) +
        ∑ i : Fin d, theta i * z.2 i) : Complex)) ∂mu

end Kyprianou.Ch06


