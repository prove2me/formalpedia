-- Prove2me | Definitions.Def_lnMonster
-- name    : lnMonster
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-22T03:26:37.378003+00:00
-- url     : https://prove2.me/theorems/d8fbd58b-dfbe-45c7-9dad-2689d93b0435
-- title:
--   lnMonster
-- statement:
--   The natural logarithm of the Monster order, $\ln |\mathbb{M}|$.

import Definitions.Def_monsterOrder
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable def lnMonster : Real := Real.log (monsterOrder : Real)


