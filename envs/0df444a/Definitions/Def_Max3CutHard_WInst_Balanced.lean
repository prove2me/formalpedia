-- Prove2me | Definitions.Def_Max3CutHard_WInst_Balanced
-- name    : Max3CutHard_WInst_Balanced
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:44:52.273539+00:00
-- url     : https://prove2.me/theorems/cae31813-019b-4388-a97b-97d4ca87b04a
-- title:
--   Balanced instance
-- statement:
--   The instance $\Phi$ is **balanced** if each type has total weight $1/3$:
--
--   $$\sum_{e:\ t_e=t}\lambda_e=\tfrac13\qquad\text{for } t=0,1,2.$$
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Håstad's equations, p.4

import Mathlib
import Definitions.Def_Max3CutHard_WInst

namespace Max3CutHard

/-- **Balanced instance.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Håstad's equations, p.4: "`Φ` is balanced if each
type has total weight `1/3`." -/
def WInst.Balanced {U W : Type} (Φ : WInst U W) : Prop :=
  ∀ t : ZMod 3, (Φ.eqs.map fun p => if p.1.t = t then p.2 else 0).sum = 1 / 3

end Max3CutHard


