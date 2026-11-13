-- Prove2me | Definitions.Def_TentNoise_refl
-- name    : TentNoise_refl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:39:55.187592+00:00
-- url     : https://prove2.me/theorems/62fbaab4-48c8-44b0-8757-92263c6147b5
-- title:
--   The folding reflection map $\mathfrak r(u)=1-|1-(u \bmod 2)|$
-- statement:
--   The **folding reflection map** $\mathfrak r:\mathbb R\to[0,1]$ is
--
--   $$
--   \mathfrak r(u):=1-\bigl|1-(u \bmod 2)\bigr|,
--   $$
--
--   where $u\bmod 2\in[0,2)$. It is the identity on $[0,1]$, even, $2$-periodic and $1$-Lipschitz: it folds the real line onto the unit interval by reflecting at the integers.
--
--   Reflecting a Gaussian increment through $\mathfrak r$ keeps a noised state in $[0,1]$ and preserves the uniform law, which is why the paper noises with reflected rather than plain Gaussians.
--
--   **Formalization Note** $u\bmod 2$ is written $2\,\mathrm{fract}(u/2)=u-2\lfloor u/2\rfloor$, which is the paper's $u \bmod 2$ for negative $u$ as well. The module also records that $\mathfrak r$ is Borel measurable.
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Definition 2.7, p.5 (PDF p.5), eq. (6)

import Mathlib

namespace TentNoise

/-- The folding reflection map `𝔯(u) := 1 − |1 − (u mod 2)|`, `ℝ → [0, 1]`
(Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Definition 2.7, p.5, eq. (6)).

**Formalization Note** `u mod 2 ∈ [0, 2)` is written `2 * Int.fract (u / 2)`
(`= u − 2⌊u/2⌋`), which is the paper's `u mod 2` for negative `u` as well. -/
noncomputable def refl (u : ℝ) : ℝ := 1 - |1 - 2 * Int.fract (u / 2)|

/-- `𝔯` is Borel measurable (a structural fact used to build the noising kernel). -/
theorem measurable_refl : Measurable refl := by
  unfold refl
  have : Measurable (fun u : ℝ => Int.fract (u / 2)) :=
    measurable_fract.comp (measurable_id.div_const 2)
  fun_prop

end TentNoise


