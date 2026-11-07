-- Prove2me | Definitions.Def_Max3CutHard_WInst_IsWeighting
-- name    : Max3CutHard_WInst_IsWeighting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:44:59.059375+00:00
-- url     : https://prove2.me/theorems/ccced1d2-b158-4627-8e27-0a1d45979b93
-- title:
--   The weights $\lambda_e\ge0$ sum to $1$
-- statement:
--   The instance $\Phi$ is a **weighting** if its weights satisfy
--
--   $$\lambda_e\ge0\ \text{for every }e,\qquad \sum_e\lambda_e=1.$$
--
--   This is the standing condition on the instances of Section 2.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Håstad's equations, p.4

import Mathlib
import Definitions.Def_Max3CutHard_WInst

namespace Max3CutHard

/-- **The weights of `Φ` are `λ_e ≥ 0` summing to 1.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Håstad's equations,
p.4: "weights `λ_e ≥ 0` summing to 1". -/
def WInst.IsWeighting {U W : Type} (Φ : WInst U W) : Prop :=
  (∀ p ∈ Φ.eqs, 0 ≤ p.2) ∧ (Φ.eqs.map Prod.snd).sum = 1

end Max3CutHard


