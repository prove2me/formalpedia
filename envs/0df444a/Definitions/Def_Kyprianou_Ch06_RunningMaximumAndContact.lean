-- Prove2me | Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
-- name    : Kyprianou_Ch06_RunningMaximumAndContact
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:01:32.975765+00:00
-- url     : https://prove2.me/theorems/9888686b-4038-463f-9733-3bcceabecba3
-- title:
--   Running maxima, drawdowns and local-time support observables
-- statement:
--   Defines the running maximum and drawdown, contact times, and the exact support of the associated Lebesgue–Stieltjes measure. An initial Dirac mass of size L₀ at time zero handles the exponential-mark clock. Provides last maximum/minimum epochs using running-contact suprema, including non-attained terminal supremum limits.
-- source:
--   Kyprianou (2006), first edition, Chapter 6, §6.1, printed pp. 139–141, supporting Definition 6.1.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- The running supremum of the actual real-valued path up to time t.
For a càdlàg Lévy sample path the image is nonempty and bounded above. -/
noncomputable def runningMaximum
    {Omega : Type} (X : NNReal → Omega → Real)
    (t : NNReal) (omega : Omega) : Real :=
  sSup ((fun u : NNReal => X u omega) '' Set.Icc 0 t)

/-- The drawdown process: running supremum minus current level. -/
noncomputable def drawdown
    {Omega : Type} (X : NNReal → Omega → Real)
    (t : NNReal) (omega : Omega) : Real :=
  runningMaximum X t omega - X t omega

/-- The set of times at which the path attains its running supremum. -/
noncomputable def MaximumContactTimes
    {Omega : Type} (X : NNReal → Omega → Real)
    (omega : Omega) : Set NNReal :=
  {t : NNReal | X t omega = runningMaximum X t omega}

/-- The full Stieltjes support of the local-time clock, including the
initial exponential mark in the irregular case. On (s,t] the associated
Stieltjes measure has mass L_t-L_s. The atom L_0 at time zero restores
the correct support for processes with no later maximum contacts; the
ordinary Stieltjes measure on NNReal necessarily has zero mass at zero. -/
def HasLocalTimeSupportAtMaximum
    {Omega : Type}
    (X : NNReal → Omega → Real)
    (L : NNReal → Omega → NNReal)
    (omega : Omega) : Prop :=
  ∃ f : StieltjesFunction NNReal,
    (∀ t : NNReal, f t = (L t omega : Real)) ∧
    (f.measure +
      ENNReal.ofReal (L 0 omega : Real) •
        Measure.dirac (0 : NNReal)).support =
      closure (MaximumContactTimes X omega)

/-- Last upward ladder epoch strictly prior to t, with initial epoch 0.
The supremum over running-maximum contact times captures left limits at
downward jumps even when the terminal running supremum is not attained. -/
noncomputable def lastEpochAtRunningMaximum
    {Omega : Type} (X : NNReal → Omega → Real)
    (t : NNReal) (omega : Omega) : NNReal :=
  sSup (insert 0 {s : NNReal | s < t ∧
    X s omega = runningMaximum X s omega})

/-- Dual last epoch for the running minimum of the original process. -/
noncomputable def lastEpochAtRunningMinimum
    {Omega : Type} (X : NNReal → Omega → Real)
    (t : NNReal) (omega : Omega) : NNReal :=
  lastEpochAtRunningMaximum (fun s w => -X s w) t omega

end Kyprianou.Ch06


