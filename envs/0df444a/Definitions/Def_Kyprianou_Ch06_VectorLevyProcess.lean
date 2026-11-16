-- Prove2me | Definitions.Def_Kyprianou_Ch06_VectorLevyProcess
-- name    : Kyprianou_Ch06_VectorLevyProcess
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:09:38.531288+00:00
-- url     : https://prove2.me/theorems/b83bdccf-e93d-4194-8ba9-3745d90c030d
-- title:
--   Joint d-dimensional Lévy-process path and increment laws
-- statement:
--   The d-dimensional Lévy-process predicate requires measurable vector marginals, zero initial state, joint stationary independent vector increments over every finite ordered time grid, and coordinatewise càdlàg sample paths. It supplies Lemma 6.17's genuinely multivariate setting.
-- source:
--   Kyprianou (2006), §2.1 and Lemma 6.17, printed p. 160; physical PDF p. 85.

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- A finite-dimensional real Levy process with joint independent
stationary increments. Crucially, independence is for all time increments
of the full vector, rather than independent scalar coordinates. -/
def IsVectorLevyProcess
    {Omega : Type} [MeasurableSpace Omega] (d : Nat)
    (P : Measure Omega)
    (X : NNReal → Omega → (Fin d → Real)) : Prop :=
  (∀ t : NNReal, Measurable (X t)) ∧
  (∀ᵐ omega ∂P, X 0 omega = 0) ∧
  (∀ s t : NNReal,
    Measure.map (fun omega => X (s + t) omega - X s omega) P =
      Measure.map (X t) P) ∧
  (∀ (n : Nat) (times : Fin (n + 1) → NNReal),
    StrictMono times →
      ∀ A : Fin n → Set (Fin d → Real),
        (∀ i, MeasurableSet (A i)) →
        P {omega | ∀ i : Fin n,
          X (times i.succ) omega -
            X (times i.castSucc) omega ∈ A i} =
          ∏ i : Fin n,
            P {omega | X (times i.succ) omega -
              X (times i.castSucc) omega ∈ A i}) ∧
  (∀ᵐ omega ∂P, ∀ i : Fin d, ∀ t : NNReal,
    ContinuousWithinAt
      (fun s : NNReal => X s omega i) (Set.Ici t) t ∧
    (t = 0 ∨ ∃ x : Real,
      Tendsto (fun s : NNReal => X s omega i)
        (nhdsWithin t (Set.Iio t)) (nhds x)))

end Kyprianou.Ch06


