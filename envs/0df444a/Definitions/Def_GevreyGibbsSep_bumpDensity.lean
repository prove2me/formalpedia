-- Prove2me | Definitions.Def_GevreyGibbsSep_bumpDensity
-- name    : GevreyGibbsSep_bumpDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:38:52.57991+00:00
-- url     : https://prove2.me/theorems/751479c6-463b-41ba-87dc-9869733f01b7
-- title:
--   Definition 4 — bump density $p_{\nu,\ell,\alpha}$
-- statement:
--   For $\alpha>1$, $0<\ell<2\pi$ and $0<\nu\le\ell/4$, the **bump distribution** $p_{\nu,\ell,\alpha}$ has density
--   $$p_{\nu,\ell,\alpha}(x)=\frac{1+(\alpha-1)\,\chi_{\nu,\ell}(x)}{Z_{\nu,\ell,\alpha}},\qquad x\in[0,2\pi)^d:$$
--   a mesa of height ratio $\alpha$ over a flat background.
--
--   **Formalization Note** The density is extended $2\pi$-periodically to $\mathbb R^d$ by reducing each coordinate into $[0,2\pi)$.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Definition 4, Eq. (30), p.13

import Mathlib
import Definitions.Def_GevreyGibbsSep_chi
import Definitions.Def_GevreyGibbsSep_bumpZ

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Definition 4 (bump distribution `p_{ν,ℓ,α}` on `T^d`), arXiv:2608.24527 (sha256 d4fd40eb…),
Eq. (30), p.13: density `(1 + (α − 1) χ_{ν,ℓ}(x))/Z_{ν,ℓ,α}` for `x ∈ [0, 2π)^d`.

**Formalization Note** The density is extended `2π`-periodically to `ℝ^d` by reducing each
coordinate into `[0, 2π)`. -/
noncomputable def bumpDensity {d : ℕ} (s ν ℓ α : ℝ) (x : Fin d → ℝ) : ℝ :=
  (1 + (α - 1) * chi s ν ℓ (fun i => toIcoMod Real.two_pi_pos 0 (x i))) / bumpZ d ν ℓ α

end GevreyGibbsSep


