-- Prove2me | Definitions.Def_UnionVolEst_IsAlmostLinftyClose
-- name    : UnionVolEst_IsAlmostLinftyClose
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:03:43.710047+00:00
-- url     : https://prove2.me/theorems/9b45294f-f20b-44cc-9378-3ee95467dc7a
-- title:
--   $(\eta,\beta)$-almost-$\ell_\infty$ closeness (Definition 2)
-- statement:
--   Let $\pi$ be a probability measure on $S$ and $D$ a distribution on $S$ that is absolutely continuous with respect to $\pi$. For $\eta,\beta\in(0,1)$, $D$ is **$(\eta,\beta)$-almost-$\ell_\infty$-close** to $\pi$ if
--   $$
--   \pi\big(\mathrm{Bad}_\eta(D,\pi)\big) \le \beta \qquad\text{and}\qquad D\big(\mathrm{Bad}_\eta(D,\pi)\big) \le 2\beta .
--   $$
--   The parameter $\eta$ bounds the multiplicative distortion of the density outside the exceptional region, and $\beta$ bounds the size of that region under both the target and the sampling distribution. It is the guarantee assumed of the sampling oracle GenerateSamples.
--
--   **Formalization Note** The absolute continuity $D \ll \pi$, a standing assumption of the paragraph that introduces $h$, is the first conjunct. The range $\eta,\beta\in(0,1)$ is not bundled; every use has $\eta=\varepsilon/32$, $\beta=\varepsilon/(32M)$ with $\varepsilon\in(0,1)$, $M \ge 1$.
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §3.1, Definition 2, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_UnionVolEst_badSet

open MeasureTheory

namespace UnionVolEst

/-- Definition 2, `(η, β)`-almost-ℓ∞ closeness (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §3.1, printed p.11, PDF p.13): a
distribution `D` on `S`, absolutely continuous with respect to the probability measure `π`, is
`(η, β)`-almost-ℓ∞-close to `π` if `π(Bad_η(D, π)) ≤ β` and `D(Bad_η(D, π)) ≤ 2β`.

**Formalization Note** The absolute continuity `D ≪ π` is the standing assumption of the
paragraph introducing `h = dD/dπ` and is bundled as the first conjunct. The page's range
`η, β ∈ (0, 1)` is not bundled: every use takes `η = ε/32`, `β = ε/(32M)` with `ε ∈ (0, 1)`,
`M ≥ 1`. `β` and `2β` enter as `ENNReal.ofReal`. -/
def IsAlmostLinftyClose {S : Type*} [MeasurableSpace S] (η β : ℝ) (D π : Measure S) : Prop :=
  D ≪ π ∧ π (badSet η D π) ≤ ENNReal.ofReal β ∧ D (badSet η D π) ≤ ENNReal.ofReal (2 * β)

end UnionVolEst


