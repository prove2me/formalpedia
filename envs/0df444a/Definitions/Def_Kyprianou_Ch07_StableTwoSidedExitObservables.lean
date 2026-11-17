-- Prove2me | Definitions.Def_Kyprianou_Ch07_StableTwoSidedExitObservables
-- name    : Kyprianou_Ch07_StableTwoSidedExitObservables
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T15:03:18.789891+00:00
-- url     : https://prove2.me/theorems/ef16dafe-5cae-4f1f-aed2-e4f6447cefdb
-- title:
--   Exercise 7.7: stable two-sided exit clocks, overshoot laws and beta kernel
-- statement:
--   Defines first strictly positive exit above one and below zero from starting position x, with infinity for missing passage. The finite upper and lower exit overshoot measures restrict the original probability law to the appropriate first-exit ordering, push forward the actual overshoot, and retain their subprobability masses. Also defines Φ_q(u)=(sin πq/π)∫₀ᵘt^(−q)/(1+t)dt for u≥0 and zero for u<0, as used in Exercise 7.7.
-- source:
--   Kyprianou (2006), Exercise 7.7(i)-(iii), printed p.209, original PDF p.218, Windows Ky.pdf sheet 110.

import Mathlib
open MeasureTheory Filter Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- First strict upcrossing of one by the original Lévy path started at x. -/
noncomputable def firstUpOfOne
    {Omega : Type} (X : NNReal → Omega → Real)
    (x : Real) (omega : Omega) : WithTop NNReal :=
  sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
    {t : NNReal | 0 < t ∧ 1 < x + X t omega})

/-- First strict downcrossing of zero, from starting position x. -/
noncomputable def firstDownOfZero
    {Omega : Type} (X : NNReal → Omega → Real)
    (x : Real) (omega : Omega) : WithTop NNReal :=
  sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
    {t : NNReal | 0 < t ∧ x + X t omega < 0})

/-- Upper overshoot distribution for exits through one before zero. -/
noncomputable def upperExitOvershootLaw
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : NNReal → Omega → Real)
    (x : Real) : Measure Real :=
  Measure.map
    (fun omega => x + X ((firstUpOfOne X x omega).untopD 0) omega - 1)
    (P.restrict {omega | firstUpOfOne X x omega < firstDownOfZero X x omega})

/-- Lower overshoot distribution for exits through zero before one. -/
noncomputable def lowerExitOvershootLaw
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : NNReal → Omega → Real)
    (x : Real) : Measure Real :=
  Measure.map
    (fun omega => -(x + X ((firstDownOfZero X x omega).untopD 0) omega))
    (P.restrict {omega | firstDownOfZero X x omega < firstUpOfOne X x omega})

/-- Rogozin's beta-prime upper CDF kernel, zero below zero. -/
noncomputable def rogozinPhi (q u : Real) : Real :=
  if u < 0 then 0 else
    (Real.sin (Real.pi * q) / Real.pi) *
      ∫ t : Real in Set.Ioc 0 u, t ^ (-q) / (1 + t) ∂volume

end Kyprianou.Ch07


