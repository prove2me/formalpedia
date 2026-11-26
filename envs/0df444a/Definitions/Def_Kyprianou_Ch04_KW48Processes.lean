-- Prove2me | Definitions.Def_Kyprianou_Ch04_KW48Processes
-- name    : Kyprianou_Ch04_KW48Processes
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T23:29:29.656724+00:00
-- url     : https://prove2.me/theorems/a29bd5ec-c49a-5cab-a17e-6f6a0f121d46
-- title:
--   Complex two-parameter Kella–Whitt processes and grids
-- statement:
--   Definitions of the characteristic exponential, predictable weight, reflected characteristic process, time and record-level integrals, candidate martingale, finite product grids and integrable envelope for Exercise 4.8(i).
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection

open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04.KW48

variable {Ω : Type} [mΩ : MeasurableSpace Ω]
variable {P : Measure Ω} {F : Filtration NNReal mΩ}

/-- Characteristic exponential process. -/
noncomputable def E (L : SpectrallyNegativeLevy P F)
    (Psi : Real → Complex) (alpha : Real) (t : NNReal) (w : Ω) : Complex :=
  Complex.exp (Complex.I * (alpha : Complex) * (L.X t w : Complex) +
    ((t : Real) : Complex) * Psi alpha)

/-- Logarithmic predictable weight. -/
noncomputable def G (L : SpectrallyNegativeLevy P F)
    (Psi : Real → Complex) (alpha beta : Real) (t : NNReal) (w : Ω) : Complex :=
  Complex.I * ((beta-alpha : Real) : Complex) * (runningSup L t w : Complex) -
    ((t : Real) : Complex) * Psi alpha

/-- Predictable exponential weight. -/
noncomputable def H (L : SpectrallyNegativeLevy P F)
    (Psi : Real → Complex) (alpha beta : Real) (t : NNReal) (w : Ω) : Complex :=
  Complex.exp (G L Psi alpha beta t w)

/-- Reflected two-parameter characteristic process. -/
noncomputable def Z (L : SpectrallyNegativeLevy P F)
    (alpha beta : Real) (t : NNReal) (w : Ω) : Complex :=
  Complex.exp (Complex.I * (alpha : Complex) *
    ((L.X t w-runningSup L t w : Real) : Complex) +
      Complex.I * (beta : Complex) * (runningSup L t w : Complex))

/-- Time integral. -/
noncomputable def J (L : SpectrallyNegativeLevy P F)
    (alpha beta : Real) (t : NNReal) (w : Ω) : Complex :=
  ∫ s in Icc (0 : Real) (t : Real), Z L alpha beta s.toNNReal w ∂volume

/-- Primitive along the running record level. -/
noncomputable def S (L : SpectrallyNegativeLevy P F)
    (beta : Real) (t : NNReal) (w : Ω) : Complex :=
  ∫ y in Icc (0 : Real) (runningSup L t w),
    Complex.exp (Complex.I * (beta : Complex) * (y : Complex)) ∂volume

/-- Candidate complex Kella--Whitt process. -/
noncomputable def M (L : SpectrallyNegativeLevy P F)
    (Psi : Real → Complex) (alpha beta : Real) (t : NNReal) (w : Ω) : Complex :=
  -Psi alpha * J L alpha beta t w + 1 - Z L alpha beta t w -
    Complex.I * ((alpha-beta : Real) : Complex) * S L beta t w

/-- Left-point predictable product gain. -/
noncomputable def Q (L : SpectrallyNegativeLevy P F)
    (Psi : Real → Complex) (alpha beta : Real)
    (u : Nat → NNReal) (N : Nat) (w : Ω) : Complex :=
  ∑ i ∈ Finset.range N, H L Psi alpha beta (u i) w *
    (E L Psi alpha (u (i+1)) w-E L Psi alpha (u i) w)

/-- Right-point correction. -/
noncomputable def C (L : SpectrallyNegativeLevy P F)
    (Psi : Real → Complex) (alpha beta : Real)
    (u : Nat → NNReal) (N : Nat) (w : Ω) : Complex :=
  ∑ i ∈ Finset.range N, E L Psi alpha (u (i+1)) w *
    (H L Psi alpha beta (u (i+1)) w-H L Psi alpha beta (u i) w)

/-- Common integrable envelope. -/
noncomputable def envelope (L : SpectrallyNegativeLevy P F)
    (Psi : Real → Complex) (alpha beta : Real) (T : NNReal) (w : Ω) : Real :=
  2 + Real.exp (2 * ‖Psi alpha‖ * (T : Real)) *
    (|beta-alpha| * runningSup L T w + ‖Psi alpha‖ * (T : Real))

end Kyprianou.Ch04.KW48


