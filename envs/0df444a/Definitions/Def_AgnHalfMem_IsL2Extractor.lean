-- Prove2me | Definitions.Def_AgnHalfMem_IsL2Extractor
-- name    : AgnHalfMem_IsL2Extractor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:11:59.454302+00:00
-- url     : https://prove2.me/theorems/cc6af024-7285-4976-aff4-c25d298618a6
-- title:
--   $(k,\ell)$-$L_2$-extractor with error $2^{-r}$ (Definition 2.1)
-- statement:
--   Let $H$ be a finite set and $\mu$ a probability measure on $X$. A matrix $M:X\times H\to[-1,1]$ is a **$(k,\ell)$-$L_2$-extractor with error $2^{-r}$** for $\mu$ if for every nonnegative $f:H\to\mathbb R$ with $\|f\|_2/\|f\|_1\le 2^{\ell}$,
--   $$
--   \Pr_{x\sim\mu}\Big[\big|\mathbb E_{h\in_R H}M(x,h)f(h)\big|\ge 2^{-r}\|f\|_1\Big]\le 2^{-k}.
--   $$
--   Rows of an extractor are almost uncorrelated with every not-too-concentrated distribution on the columns; this is the property that forces a memory–sample tradeoff for the learning problem of $M$.
--
--   **Formalization Note** The ratio condition is written $\|f\|_2\le 2^\ell\|f\|_1$ with $f\ne0$ (the ratio is undefined at $f=0$). The parameters are real numbers. The range $[-1,1]$ of $M$ is a hypothesis of the theorems that use the definition.
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), Definition 2.1, p.7

import Mathlib
import Definitions.Def_AgnHalfMem_nrm1

open MeasureTheory

namespace AgnHalfMem

/-- **L2-extractor (Definition 2.1).** S. Garg, T. Jadhav, *Memory-Sample Tradeoffs for
Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript, PDF sha256
386bc9b3…43f84d5), Definition 2.1, p.7: "Let H be a finite set. A matrix M : X × H → [−1, 1] is a
(k, ℓ)-L2-Extractor with error 2^{−r}, for a given probability measure μ : X → [0, 1], if for
every non-negative f : H → ℝ with ‖f‖₂/‖f‖₁ ≤ 2^ℓ,
Pr_{x∼μ}[ |E_{h ∈_R H} M(x, h) f(h)| ≥ 2^{−r} ‖f‖₁ ] ≤ 2^{−k}."

`IsL2Extractor μ M k ℓ r`: for every nonnegative, nonzero `f : H → ℝ` with `‖f‖₂ ≤ 2^ℓ ‖f‖₁`,
the `μ`-measure of `{x | |⟨M_x, f⟩| ≥ 2^{−r} ‖f‖₁}` is at most `2^{−k}`.

**Formalization Note.** Norms and `⟨M_x, f⟩ = (Σ_h M(x,h) f(h))/|H|` are uniform-normalized (p.7).
The ratio `‖f‖₂/‖f‖₁` is undefined for `f = 0`, so `f ≠ 0` is required and the ratio is written
cross-multiplied (equivalent for `f ≠ 0`, where `‖f‖₁ > 0`); admitting `f = 0` would make the
condition fail for every matrix. The parameters `k, ℓ, r` are real numbers. The range
`M : X × H → [−1, 1]` is a hypothesis of each theorem that uses the definition. -/
def IsL2Extractor {X H : Type*} [MeasurableSpace X] [Fintype H] (μ : Measure X)
    (M : X → H → ℝ) (k ℓ r : ℝ) : Prop :=
  ∀ f : H → ℝ, (∀ h, 0 ≤ f h) → f ≠ 0 → nrm2 f ≤ (2 : ℝ) ^ ℓ * nrm1 f →
    μ {x | (2 : ℝ) ^ (-r) * nrm1 f ≤ |ip (fun h => M x h) f|} ≤ ENNReal.ofReal ((2 : ℝ) ^ (-k))

end AgnHalfMem


