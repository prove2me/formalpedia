-- Prove2me | Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
-- name    : Kyprianou_Ch03_ReflectedProcesses
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T09:49:10.638395+00:00
-- url     : https://prove2.me/theorems/97ef02e3-8017-44e9-889f-2fe7a4fca99b
-- title:
--   Running supremum/infimum reflected Lévy processes with initial level
-- statement:
--   The two reflected processes, including their nonnegative starting values. Each uses the running supremum of X or -X.
-- source:
--   Kyprianou (2006), Exercise 3.2, printed p. 83; solution pp. 312–313.

import Mathlib
import Definitions.Def_LevyExtrema_SBA_runSup
set_option autoImplicit false
namespace Kyprianou.Ch03
noncomputable def reflectedSup
    {Omega : Type} (X : NNReal → Omega → ℝ)
    (y : ℝ) (t : NNReal) (omega : Omega) : ℝ :=
  max y (LevyExtrema.SBA.runSup (fun s => X s omega) t) - X t omega
noncomputable def reflectedInf
    {Omega : Type} (X : NNReal → Omega → ℝ)
    (y : ℝ) (t : NNReal) (omega : Omega) : ℝ :=
  max y (LevyExtrema.SBA.runSup (fun s => -(X s omega)) t) + X t omega
end Kyprianou.Ch03


