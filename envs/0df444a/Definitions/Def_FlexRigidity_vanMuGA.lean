-- Prove2me | Definitions.Def_FlexRigidity_vanMuGA
-- name    : FlexRigidity_vanMuGA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:20:16.757201+00:00
-- url     : https://prove2.me/theorems/bad7dc5f-b84e-4344-83cf-43a8774450d9
-- title:
--   The function $\mathrm{van}_{\mu,\mathsf G,\alpha}$, eq. (53)
-- statement:
--   $$\mathrm{van}_{\mu,\mathsf G,\alpha}(\delta)=\frac{\alpha}{\alpha-1}\log\max_{0\le\eta\le\min\{1,\mathrm{van}_{\mathsf G}(\delta)^2\}}\Big[(1-\eta)^{1/\alpha}+\Big(\frac{a_\mu|S|(|S|-1)}{\mu}\Big)^{(\alpha-1)/\alpha}\eta^{1/\alpha}\Big],$$
--   log base 2, $|S|=|A||S_{\mathrm A}||S_{\mathrm B}|$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), eq. (53), p. 47

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_aMu
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The function `van_{µ,G,α}`, eq. (53)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 47):
`van_{µ,G,α}(δ) = (α/(α−1)) log max_{0 ≤ η ≤ min{1, van_G(δ)²}} [ (1−η)^{1/α} + (a_µ|S|(|S|−1)/µ)^{(α−1)/α} η^{1/α} ]`,
log base 2, with `a_µ = 1 − µ + µ/|S|`; `s` is `|S| = |A||S_A||S_B|`.

**Formalization Note** The maximum of the continuous function over the nonempty compact interval
is the real `sSup` of its image. -/
def vanMuGA (van : ℝ → ℝ) (s : ℕ) (μ α δ : ℝ) : ℝ :=
  (α / (α - 1)) * Real.logb 2 (sSup ((fun η : ℝ => (1 - η) ^ (1 / α) +
    (aMu μ s * s * (s - 1) / μ) ^ ((α - 1) / α) * η ^ (1 / α)) '' Set.Icc 0 (min 1 (van δ ^ 2))))

end FlexRigidity


