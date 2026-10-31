-- Prove2me | Definitions.Def_KallMayerSLP_Bonferroni_kStar
-- name    : KallMayerSLP_Bonferroni_kStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:01.941824+00:00
-- url     : https://prove2.me/theorems/9cbef4e3-673d-4357-ac0a-c7a3bd9b3bdf
-- title:
--   The index $k^*=\lfloor 2S_2/S_1\rfloor+1$
-- statement:
--   For real numbers $S_1,S_2$ with $S_1>0$, the index in the lower Boole–Bonferroni bound is
--   $$
--   k^*=\left\lfloor\frac{2S_2}{S_1}\right\rfloor+1.
--   $$
--
--   **Formalization Note** The value is a natural number computed with the natural floor, which agrees with the ordinary floor when $S_1>0$ and $S_2\ge0$. At $S_1=0$ Lean's division by zero gives the value $1$, while the book's $k^*$ is undefined, so every statement of this mission that uses it assumes $S_1>0$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, eq. (3.15), p.288 (PDF 297)

import Mathlib

namespace KallMayerSLP.Bonferroni

/-- The index `k* := ⌊2 S₂ / S₁⌋ + 1` of (3.15).

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, eq. (3.15), p.288 (PDF 297).

**Formalization Note.** The value is a natural number, computed with the natural floor `⌊·⌋₊`.
For `S₁, S₂ ≥ 0` and `S₁ > 0` it agrees with the integer floor of the book, because then
`2 S₂ / S₁ ≥ 0`. For `S₁ = 0` Lean's division gives `2 S₂ / 0 = 0` and `kStar = 1`, while the book's
`k*` is undefined; every statement of this mission that uses `kStar` assumes `0 < S₁`. -/
noncomputable def kStar (S₁ S₂ : ℝ) : ℕ :=
  ⌊2 * S₂ / S₁⌋₊ + 1

end KallMayerSLP.Bonferroni


