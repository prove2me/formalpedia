-- Prove2me | Definitions.Def_CompetingSellers_sl
-- name    : CompetingSellers_sl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:13.116433+00:00
-- url     : https://prove2.me/theorems/f85c531b-82e6-4a10-984e-91a421a1c53b
-- title:
--   Bob's test mechanisms $\mathrm{SL}_{x,p}$, $\mathrm{FP}(p)$, $\mathrm{DL}_{x,q}$ and the capped mechanism $\tilde A$
-- statement:
--   With $b|_a=\max(0,b-a)$:
--
--   1. **Single lottery** (Definition 3.2): $\mathrm{SL}_{x,p}(z)=zp$ for $0\le z\le x$ and $\infty$ for $x<z\le1$; the **fixed price** mechanism is $\mathrm{FP}(p)=\mathrm{SL}_{1,p}$.
--   2. **Double lottery** (Definition 3.6): for $x\in[0,1]$, $q\in[b|_a,\,b-x(b-b|_a)]$,
--   $$\mathrm{DL}_{x,q}(z)=\begin{cases} z\,b|_a,&0\le z\le x,\\ z\cdot\frac{q-x b|_a}{1-x}-x\cdot\frac{q-b|_a}{1-x},& x<z\le1.\end{cases}$$
--   3. **Capped mechanism** (eq. (6)): $\tilde A(z)=A(z)$ for $0\le z\le x$ and $\infty$ for $x<z\le1$.
--
--   $\mathrm{DL}_{0,q}=\mathrm{FP}(q)$. These menus are the responses against which the paper tests Alice's mechanisms.
--
--   **Formalization Note** Pricing functions $\mathbb R\to[0,\infty]$ read on $[0,1]$.
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Definition 3.2, p.20; Definition 3.6, p.22; eq. (6), p.28

import Mathlib

set_option autoImplicit false

open scoped ENNReal

namespace CompetingSellers

/-- **Single-lottery mechanism `SL_{x,p}`** (Definition 3.2, p.20).
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Definition 3.2, p.20 (PDF 23): "Let `x ∈ [0, 1]` and `p ≥ 0`.
We define the mechanism `SL_{x,p}` such that, for all `z ∈ [0, 1]`, we have: `SL_{x,p}(z) = zp`
if `0 ≤ z ≤ x`, `∞` if `x < z ≤ 1`. For all `p ≥ 0`, we also define `FP(p) = SL_{1,p}` to be the
fixed price mechanism with price `p`."

**Formalization Note.** A pricing function `ℝ → ℝ≥0∞` read on `[0, 1]`; it is used as Bob's
strategy through mechanisms realizing it (`IsPricingMech`). -/
noncomputable def sl (x p : ℝ) : ℝ → ℝ≥0∞ :=
  fun z => if z ≤ x then ENNReal.ofReal (z * p) else ⊤

/-- The fixed price mechanism `FP(p) = SL_{1,p}` (Definition 3.2, p.20). -/
noncomputable def fp (p : ℝ) : ℝ → ℝ≥0∞ := sl 1 p

/-- **Double-lottery mechanism `DL_{x,q}`** (Definition 3.6, p.22): for
`x ∈ [0, 1]`, `q ∈ [b|_a, b − x(b − b|_a)]` and `z ∈ [0, 1]`,
`DL_{x,q}(z) = z b|_a` if `0 ≤ z ≤ x`, and
`z (q − x b|_a)/(1 − x) − x (q − b|_a)/(1 − x)` if `x < z ≤ 1`, where
`b|_a = max(0, b − a)` (eq. (1), p.18). -/
noncomputable def dl (a b x q : ℝ) : ℝ → ℝ≥0∞ :=
  fun z => if z ≤ x then ENNReal.ofReal (z * max 0 (b - a))
    else ENNReal.ofReal (z * ((q - x * max 0 (b - a)) / (1 - x))
      - x * ((q - max 0 (b - a)) / (1 - x)))

/-- **Capped mechanism** `Ã` (eq. (6), p.28): `Ã(z) = A(z)` for `0 ≤ z ≤ x` and `∞` for
`x < z ≤ 1`, applied to a pricing function `P` (the paper applies it to `A ≡ P_A`). -/
noncomputable def cap (P : ℝ → ℝ≥0∞) (x : ℝ) : ℝ → ℝ≥0∞ :=
  fun z => if z ≤ x then P z else ⊤

end CompetingSellers


