-- Prove2me | Definitions.Def_Kyprianou_Ch06_IndexedExcursion
-- name    : Kyprianou_Ch06_IndexedExcursion
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:01:17.318193+00:00
-- url     : https://prove2.me/theorems/cd69627b-54dd-4caf-93ee-555be0f5564c
-- title:
--   Definition 6.13: excursions indexed by inverse local time
-- statement:
--   The right-continuous inverse of local time is the first chronological time at which the accumulated local time exceeds a specified level. Its left limit is defined as the supremum of earlier inverse epochs, with zero convention. A positive jump of the inverse defines a translated excursion path from the pre-jump to the post-jump epoch, with possibly infinite lifetime; no jump produces the cemetery state.
-- source:
--   Kyprianou (2006), first edition, Definition 6.13, printed p. 154; physical two-up PDF p. 82.

import Mathlib
open Filter
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- First strict passage of a local-time path above a level, extended by infinity. -/
noncomputable def inverseLocalTime
    {Omega : Type} (L : NNReal → Omega → NNReal)
    (s : NNReal) (omega : Omega) : WithTop NNReal :=
  sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
    {t : NNReal | s < L t omega})

/-- The left limit of the inverse local time, with the book's zero convention. -/
noncomputable def inverseLocalTimeLeft
    {Omega : Type} (L : NNReal → Omega → NNReal)
    (s : NNReal) (omega : Omega) : WithTop NNReal :=
  if s = 0 then 0 else
    sSup ((fun u : NNReal => inverseLocalTime L u omega) ''
      {u : NNReal | u < s})

/-- The duration of a time interval between successive inverse-local-time
epochs, possibly infinite when an excursion never terminates. -/
noncomputable def excursionDuration
    {Omega : Type} (L : NNReal → Omega → NNReal)
    (s : NNReal) (omega : Omega) : WithTop NNReal :=
  let tauMinus := inverseLocalTimeLeft L s omega
  let tau := inverseLocalTime L s omega
  if tau = ⊤ then ⊤ else
    ((tau.untopD 0 - tauMinus.untopD 0) : WithTop NNReal)

/-- Definition 6.13. An excursion at local time s is the real process
between consecutive inverse-local-time epochs, translated to start at
zero. Return none (the dummy state) when there is no jump of the inverse
local time; allow an infinite terminal epoch. -/
noncomputable def indexedExcursion
    {Omega : Type} (X : NNReal → Omega → Real) (L : NNReal → Omega → NNReal)
    (s : NNReal) (omega : Omega) :
    Option ((NNReal → Real) × WithTop NNReal) :=
  let tauMinus := inverseLocalTimeLeft L s omega
  let tau := inverseLocalTime L s omega
  if tauMinus < tau then
    some ((fun r : NNReal =>
      X (tauMinus.untopD 0 + r) omega - X (tauMinus.untopD 0) omega),
      excursionDuration L s omega)
  else none

end Kyprianou.Ch06


