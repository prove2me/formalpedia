-- Prove2me | Definitions.Def_MarketplaceLeakage_Communication_etaStar
-- name    : MarketplaceLeakage_Communication_etaStar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:00:12.742867+00:00
-- url     : https://prove2.me/theorems/201a0f32-4a33-423e-83b4-8f4facf1b3e1
-- title:
--   $\eta^*$: the crossing point of the two ban options
-- statement:
--   A marketplace $M$ intermediates the sales of a seller $S$ whose product buyers value at $v$; $S$ has marginal cost $c$ with $0<c<v$ and pays $M$ a per-transaction fee $f$. A priori a buyer values the product at $v$ with probability $q\in(0,1)$ and at zero otherwise. If $M$ bans buyer–seller communication, buyers can no longer buy directly from $S$ (no leakage), but each buyer learns their true valuation only with probability $\eta\in[0,1]$.
--
--   Define
--
--   $$
--   \eta^*=\frac{qv(2-q)-c-q\sqrt{(1-q)\,v\,(v-c)}}{qv\,(3(1-q)+q^2)-c}.
--   $$
--
--   When $qv>c$, $\eta^*$ is the unique point in $(0,1)$ at which $\Pi_H(\eta^*)=\Pi_L(\eta^*)$; the marketplace prefers option 1 above it and option 2 below it.
--
--   **Formalization Note** Written as printed. On $0<q<1$, $0<c<v$, $qv>c$ the radicand is positive and the denominator exceeds $qv-c>0$, so neither Lean's $\sqrt{\cdot}$ of a negative number nor $x/0=0$ is reached.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript (March 2023), doi:10.1287/mnsc.2023.4757, §8.4 (proof of Proposition 3), unnumbered display, p. 38

import Mathlib

namespace MarketplaceLeakage.Communication

/-- **`η*`, the crossing point of the two ban options.**
Hagiu, Wright, *Marketplace Leakage*, authors' manuscript (March 2023), §8.4 (proof of Proposition 3), unnumbered display, p. 38: "Thus, when qv > c, there
exists a unique η∗ ∈ (0, 1) such that M prefers option 1 (ΠH (η) ≥ ΠL (η)) when η ≥ η∗ and
option 2 (ΠH (η) ≤ ΠL (η)) when η ≤ η∗, where
η∗ = (qv (2 − q) − c − q √((1 − q) v (v − c)))/(qv (3 (1 − q) + q²) − c)."

**Formalization Note.** Written as printed. Lean's `Real.sqrt` is `0` on negative
arguments and `x / 0 = 0`; on the paper's range `0 < q < 1`, `0 < c < v`, `qv > c` the
radicand is positive and the denominator exceeds `qv − c > 0`
(since `3(1 − q) + q² − 1 = (1 − q)(2 − q) > 0`), so neither convention is reached. -/
noncomputable def etaStar (q v c : ℝ) : ℝ :=
  (q * v * (2 - q) - c - q * Real.sqrt ((1 - q) * v * (v - c))) /
    (q * v * (3 * (1 - q) + q ^ 2) - c)

end MarketplaceLeakage.Communication


