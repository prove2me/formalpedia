-- Prove2me | Definitions.Def_Max3CutHard_LinInst_toWInst
-- name    : Max3CutHard_LinInst_toWInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:45:14.727211+00:00
-- url     : https://prove2.me/theorems/33642db2-fbd2-4069-8b56-0340171cff4c
-- title:
--   The weighted instance of an encodable instance
-- statement:
--   For an encodable instance with $m$ listed equations, the weighted instance $\Phi$ gives every listed equation the weight
--
--   $$\lambda=\frac1m.$$
--
--   For $m\ge1$ these weights are non-negative and sum to $1$.
--
--   **Formalization Note** For $m=0$ the instance has no equations; it is neither a weighting nor balanced.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Håstad's equations, p.4

import Mathlib
import Definitions.Def_Max3CutHard_LinInst
import Definitions.Def_Max3CutHard_WInst

namespace Max3CutHard

/-- **The weighted instance of an encodable instance.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Håstad's equations, p.4.
Each of the `m` listed equations gets weight `λ = 1/m`.

**Formalization Note.** For `m = 0` the instance is empty (weights do not sum to 1; such an
instance is neither balanced nor a weighting). -/
noncomputable def LinInst.toWInst (Φ : LinInst) : WInst (Fin Φ.nU) (Fin Φ.nW) :=
  ⟨Φ.eqs.map fun e => (e, 1 / (Φ.eqs.length : ℝ))⟩

end Max3CutHard


