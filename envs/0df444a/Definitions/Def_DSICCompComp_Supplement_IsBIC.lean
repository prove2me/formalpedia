-- Prove2me | Definitions.Def_DSICCompComp_Supplement_IsBIC
-- name    : DSICCompComp_Supplement_IsBIC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:20:22.425209+00:00
-- url     : https://prove2.me/theorems/6d68b073-d0e3-47ce-bba9-136568e5773f
-- title:
--   Bayesian incentive compatibility (BIC) with respect to $D$
-- statement:
--   A mechanism $(x, p)$ for $n$ additive bidders with values drawn iid from the product distribution $D$ is **Bayesian incentive compatible (BIC)** if for all bidders $i$ and all values $v_i, v'_i$,
--
--   $$
--   \mathbb E_{v_{-i}\sim D^{n-1}}\Big[\sum_{j=1}^m x_{ij}(v)\, v_{ij} - p_i(v)\Big] \;\ge\; \mathbb E_{v_{-i}\sim D^{n-1}}\Big[\sum_{j=1}^m x_{ij}(v'_i, v_{-i})\, v_{ij} - p_i(v'_i, v_{-i})\Big].
--   $$
--
--   That is, truthful reporting maximizes a bidder's expected utility when the others report truthfully.
--
--   **Formalization Note** $v_i$ and $v'_i$ range over all of $\mathbb R_{\ge 0}^m$, as the page's "for all values" says. Integrability of both interim-utility integrands is included in the definition, so neither Bochner integral can silently default to $0$.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Section 2, p.5 (pdf p.6)

import Mathlib
import Definitions.Def_DSICCompComp_Supplement_interimUtility

open MeasureTheory
open scoped NNReal

namespace DSICCompComp

namespace Supplement

/-- Bayesian Incentive Compatibility with respect to `D` (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*, STOC 2027
submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…,
Section 2, p.5 (pdf p.6)): for all bidders `i` and values `v_i` and `v'_i`,
`E_{v_{-i}∼D^{n-1}}[∑_j x_ij(v)·v_ij − p_i(v)] ≥ E_{v_{-i}∼D^{n-1}}[∑_j x_ij(v'_i,v_{-i})·v_ij − p_i(v'_i,v_{-i})]`.

**Formalization Note** `v_i` and `v'_i` range over all of `ℝ≥0^m`, as the page's "for all values"
says. Integrability of both interim-utility integrands is included here, so neither Bochner
integral can silently take Lean's default value `0`. -/
def IsBIC {n m : ℕ} (D : Fin m → ProbabilityMeasure ℝ≥0)
    (M : MultiItemRev.MultiBuyer.MechanismN n (Fin m)) : Prop :=
  ∀ (i : Fin n) (vi vi' : Fin m → ℝ≥0),
    ∃ hdev : Integrable (interimIntegrand M i vi vi') (profileLaw n D),
      ∃ htruth : Integrable (interimIntegrand M i vi vi) (profileLaw n D),
        interimUtility D M i vi vi' hdev ≤ interimUtility D M i vi vi htruth

end Supplement

end DSICCompComp


