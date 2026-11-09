-- Prove2me | Definitions.Def_GevreyGibbsSep_InDotGevrey
-- name    : GevreyGibbsSep_InDotGevrey
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:37:19.338607+00:00
-- url     : https://prove2.me/theorems/ed86c7f2-141f-4642-a590-ffe07ab824d4
-- title:
--   Definition 1 — nonzero-order Gevrey class $\dot G^s(\xi,\rho)$
-- statement:
--   For $s\ge1$, $\rho>0$ and a $2\pi$-periodic smooth $f$, the **nonzero-order Gevrey seminorm** is
--   $$[f]_{s,\rho}=\sup_{a\in\mathbb N^d\setminus\{0\}}\ \sup_{x\in[0,2\pi)^d}\frac{|\partial^af(x)|\,\rho^{\|a\|_1}}{(a!)^s},$$
--   and $f\in\dot G^s(\xi,\rho)$ means $[f]_{s,\rho}\le\xi$, that is every derivative of positive order obeys $|\partial^af|\le\xi\,(a!)^s\rho^{-\|a\|_1}$. The order-zero term is ignored, matching the gauge freedom $E\mapsto E+\mathrm{const}$ of Gibbs potentials.
--
--   **Formalization Note** The bound is stated pointwise for every $a\ne0$ and every $x\in\mathbb R^d$ (for a periodic $f$ the same as $x\in[0,2\pi)^d$). $(a!)^s$ is a real power. Smoothness and periodicity are a separate item.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Definition 1, Eq. (3), p.5

import Mathlib
import Definitions.Def_GevreyGibbsSep_IsPeriodicSmooth
import Definitions.Def_GevreyGibbsSep_partialDeriv

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Definition 1 (nonzero-order Gevrey class), arXiv:2608.24527 (sha256 d4fd40eb…), Eq. (3),
p.5: `f ∈ Ġ^s(ξ, ρ)` iff `[f]_{s,ρ} = sup_{a ≠ 0} sup_x |∂^a f(x)| ρ^{‖a‖₁}/(a!)^s ≤ ξ`, where
`a! = ∏_j a_j!` and `‖a‖₁ = ∑_j a_j`.

**Formalization Note** "sup ≤ ξ" is written pointwise, `|∂^a f(x)| ρ^{‖a‖₁} ≤ ξ (a!)^s` for every
`a ≠ 0` and every `x`; `x` ranges over all of `ℝ^d`, which for the periodic functions of the paper
is the same as `x ∈ [0, 2π)^d`. The power `(a!)^s` is a real power (`s` is real). Smoothness and
periodicity are stated separately (`IsPeriodicSmooth`). -/
def InDotGevrey {d : ℕ} (s ξ ρ : ℝ) (f : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ a : Fin d → ℕ, a ≠ 0 → ∀ x : Fin d → ℝ,
    |partialDeriv a f x| * ρ ^ (∑ i, a i) ≤ ξ * ((∏ i, (a i).factorial : ℕ) : ℝ) ^ s

end GevreyGibbsSep


