-- Prove2me | Definitions.Def_DSICCompComp_Supplement_IsBIR
-- name    : DSICCompComp_Supplement_IsBIR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:21:01.938429+00:00
-- url     : https://prove2.me/theorems/d2f074ae-951f-41dd-bbe3-ca36da01305b
-- title:
--   Bayesian individual rationality (BIR) with respect to $D$
-- statement:
--   A mechanism $(x, p)$ for $n$ additive bidders with values drawn iid from the product distribution $D$ is **Bayesian individually rational (BIR)** if for all bidders $i$ and all values $v_i$,
--
--   $$
--   \mathbb E_{v_{-i}\sim D^{n-1}}\Big[\sum_{j=1}^m x_{ij}(v)\, v_{ij} - p_i(v)\Big] \;\ge\; 0 .
--   $$
--
--   **Formalization Note** $v_i$ ranges over all of $\mathbb R_{\ge 0}^m$; the definition requires the truthful interim-utility integrand to be integrable before applying `interimUtility`.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Section 2, p.6 (pdf p.7)

import Mathlib
import Definitions.Def_DSICCompComp_Supplement_interimUtility

open MeasureTheory
open scoped NNReal

namespace DSICCompComp

namespace Supplement

/-- Bayesian Individual Rationality with respect to `D` (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*, STOC 2027
submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…,
Section 2, p.6 (pdf p.7)): for all bidders `i` and values `v_i`,
`E_{v_{-i}∼D^{n-1}}[∑_j x_ij(v)·v_ij − p_i(v)] ≥ 0`.

**Formalization Note** `v_i` ranges over all of `ℝ≥0^m`; integrability of the truthful
interim-utility integrand is included here, so the Bochner integral cannot silently take Lean's
default value `0`. -/
def IsBIR {n m : ℕ} (D : Fin m → ProbabilityMeasure ℝ≥0)
    (M : MultiItemRev.MultiBuyer.MechanismN n (Fin m)) : Prop :=
  ∀ (i : Fin n) (vi : Fin m → ℝ≥0),
    ∃ htruth : Integrable (interimIntegrand M i vi vi) (profileLaw n D),
      0 ≤ interimUtility D M i vi vi htruth

end Supplement

end DSICCompComp


