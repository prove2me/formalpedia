-- Prove2me | Definitions.Def_Kyprianou_Ch06_ExcursionObservables
-- name    : Kyprianou_Ch06_ExcursionObservables
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:03:47.52274+00:00
-- url     : https://prove2.me/theorems/a4cc96f5-3460-47bf-a7db-34190778c851
-- title:
--   Definition 6.14: excursion terminal value and height
-- statement:
--   The excursion terminal value is the value at its finite lifetime; its height is minus the infimum of the excursion path over the open lifetime. These are the two excursion observables explicitly named in Definition 6.14 and used in Theorem 6.15.
-- source:
--   Kyprianou (2006), Definition 6.14, printed p. 155, physical PDF p. 83.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_ExcursionSpace
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Terminal value h(epsilon) for an excursion of finite lifetime. -/
noncomputable def excursionTerminalValue (e : Excursion) : Real :=
  e.1.1 (e.1.2.untopD 0)

/-- Excursion height: minus the infimum over its open lifetime. -/
noncomputable def excursionHeight (e : Excursion) : Real :=
  -sInf (e.1.1 '' {t : NNReal |
    0 < t ∧ (t : WithTop NNReal) < e.1.2})

end Kyprianou.Ch06


