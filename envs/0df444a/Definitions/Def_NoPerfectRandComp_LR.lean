-- Prove2me | Definitions.Def_NoPerfectRandComp_LR
-- name    : NoPerfectRandComp_LR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:44:28.596174+00:00
-- url     : https://prove2.me/theorems/91a31988-853f-46bb-b2c2-01e3fe1be75e
-- title:
--   Linearised query complexity $\mathrm{LR}(f)$
-- statement:
--   Following Ben-David, Blais, Göös and Maystre, the **linearised randomized query complexity** of a possibly partial Boolean function $f$ is
--   $$
--   \mathrm{LR}(f) = \inf_{A\,:\ \mathrm{sbias}(A,x) > 0\ \forall x \in \mathrm{Dom}(f)}\ \max_{x \in \mathrm{Dom}(f)} \frac{\mathrm{cost}(A,x)}{\mathrm{sbias}(A,x)} .
--   $$
--   The infimum is over algorithms with positive signed bias on every input of the domain; an algorithm with nonpositive bias anywhere does not count (equivalently, it has infinite cost-to-bias ratio). Allowing negative denominators would define a different quantity.
--
--   $\mathrm{LR}$ is the inner side of the composition question: $\mathrm{R}(f\circ g) = \Omega(\mathrm{R}(f)\,\mathrm{LR}(g))$.
--
--   **Formalization Note** The value is in $[0,\infty]$. On the range of the infimum the denominator is positive, so the ratio is an honest quotient.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §2.4, p.6

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_NoPerfectRandComp_PartialFn
import Definitions.Def_NoPerfectRandComp_expCost
import Definitions.Def_NoPerfectRandComp_sbias
open scoped ENNReal

namespace NoPerfectRandComp

/-- Linearised randomized query complexity (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §2.4, p.6, following [8]):
`LR(f) = inf_{A : sbias(A,x) > 0 ∀ x} max_{x ∈ Dom(f)} cost(A, x) / sbias(A, x)`.

**Formalization Note** The infimum ranges only over algorithms whose signed bias is positive at
every `x ∈ Dom(f)` (the page: allowing negative denominators would define a different quantity).
The ratio is computed in `ℝ≥0∞`; on that range the denominator is positive, so no junk division
occurs. The maximum over the finite domain is a supremum. -/
noncomputable def LR {ι : Type} (f : PartialFn ι) : ℝ≥0∞ :=
  ⨅ (A : QAlgorithms.RandDecisionTree ι Bool Bool) (_ : ∀ x ∈ f.dom, 0 < sbias A f x),
    ⨆ x ∈ f.dom, expCost A x / ENNReal.ofReal (sbias A f x)

end NoPerfectRandComp


