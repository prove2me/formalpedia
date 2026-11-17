-- Prove2me | Definitions.Def_Kyprianou_Ch07_TransienceAndRecurrence
-- name    : Kyprianou_Ch07_TransienceAndRecurrence
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T14:43:27.349849+00:00
-- url     : https://prove2.me/theorems/504cc825-ba62-499f-b00c-edd80e93d020
-- title:
--   Definition 7.3: transience and recurrence via occupation time
-- statement:
--   For a real-valued Lévy process X, define the total occupation time of the interval (-a,a) as the integral over non-negative time of the indicator of |X_t|<a. Transience requires that for each a>0 this occupation time be finite almost surely. Recurrence requires that for each a>0 this occupation time be infinite almost surely. The quantifiers are outside the probability-one event, as printed.
-- source:
--   Kyprianou (2006), first edition, Definition 7.3, printed p. 184; Windows Ky.pdf landscape sheet 97 (original single-page p. 193).

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Occupation time of the open interval (-a,a) over the entire time axis. -/
noncomputable def occupationTime
    {Omega : Type} (X : NNReal → Omega → Real)
    (a : Real) (omega : Omega) : ENNReal :=
  ∫⁻ t : Real in Set.Ici (0 : Real),
    if |X (Real.toNNReal t) omega| < a then (1 : ENNReal) else 0

/-- Definition 7.3: finite occupation for every open interval around zero. -/
def IsTransientLevyProcess
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : NNReal → Omega → Real) : Prop :=
  ∀ a : Real, 0 < a →
    P {omega : Omega | occupationTime X a omega < ⊤} = 1

/-- Definition 7.3: infinite occupation for every open interval around zero. -/
def IsRecurrentLevyProcess
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : NNReal → Omega → Real) : Prop :=
  ∀ a : Real, 0 < a →
    P {omega : Omega | occupationTime X a omega = ⊤} = 1

end Kyprianou.Ch07


