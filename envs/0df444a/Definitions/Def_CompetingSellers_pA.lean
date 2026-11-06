-- Prove2me | Definitions.Def_CompetingSellers_pA
-- name    : CompetingSellers_pA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:55.777111+00:00
-- url     : https://prove2.me/theorems/a2c25e8d-3db1-4e1b-8b26-97f43e30ba8c
-- title:
--   Thresholds $v_A(x)$, $p_A(x)$ and $x_A(q)$
-- statement:
--   For Alice's mechanism $A$ (identified with $P_A$):
--
--   1. $v_A(x)$ is the largest $v\in[0,a]$ with $\mathrm{util}_A(v)\le\mathrm{util}_A(a)-x\,\mathrm{Aug}_A(b,a)$, and $p_A(x)=b-\frac{a-v_A(x)}{x}$ for $x>0$, $p_A(0)=b-\mathrm{Aug}_A(b,a)$ (Definition 3.3): the per-unit price at which the buyer is indifferent between visiting Bob's single lottery $\mathrm{SL}_{x,p}$ first or Alice first.
--   2. For $q\in[b|_a,b]$ (Definition 3.7),
--   $$x_A(q)=\begin{cases}\dfrac{b-q-\mathrm{Aug}_A(b-q,a)}{\min(a,b)-\mathrm{Aug}_A(\min(a,b),a)},&\mathrm{Aug}_A(b,a)<\min(a,b),\\[2mm] \dfrac{b-q}{b-b|_a},&\mathrm{Aug}_A(b,a)=\min(a,b),\end{cases}$$
--   the threshold above which the buyer visits Bob's double lottery $\mathrm{DL}_{x,q}$ first.
--
--   **Formalization Note** $v_A(x)$ is the supremum of the stated set. The second case of $x_A$ is taken whenever the first fails ($\mathrm{Aug}_A(b,a)\le\min(a,b)$ always).
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Definition 3.3, p.21 (PDF 24); Definition 3.7, p.22 (PDF 25)

import Mathlib
import Definitions.Def_CompetingSellers_priceRep

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

variable {S : Type} [MeasurableSpace S] {null : S}

/-- `v_A(x)` (Definition 3.3, p.21): "the largest value `v ∈ [0, a]` satisfying
`util_A(v) ≤ util_A(a) − x · Aug_A(b, a)`." -/
noncomputable def vA (a b : ℝ) (A : Mech S null) (x : ℝ) : ℝ :=
  sSup {v | v ∈ Set.Icc 0 a ∧ mUtil a A v ≤ mUtil a A a - x * mAug a A b a}

/-- **Bob-first threshold price `p_A(x)`** (Definition 3.3, p.21).
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Definition 3.3, p.21 (PDF 24): "Let `A` be a mechanism for Alice
and `x ∈ [0, 1]`. Define `v_A(x)` to be the largest value `v ∈ [0, a]` satisfying
`util_A(v) ≤ util_A(a) − x · Aug_A(b, a)`. … define `p_A(x) = b − (a − v_A(x))/x` if `x > 0`,
`b − Aug_A(b, a)` if `x = 0`."

**Formalization Note.** `util_A`, `Aug_A` are those of Alice's proper pricing representation
(`mUtil a A`, `mAug a A`); `v_A(x)` is the supremum of the stated set (nonempty: `v = 0`;
the paper notes the supremum is attained). -/
noncomputable def pA (a b : ℝ) (A : Mech S null) (x : ℝ) : ℝ :=
  if 0 < x then b - (a - vA a b A x) / x else b - mAug a A b a

/-- **Alice-first threshold `x_A(q)`** (Definition 3.7, p.22): for `q ∈ [b|_a, b]`,
`x_A(q) = (b − q − Aug_A(b − q, a))/(min(a, b) − Aug_A(min(a, b), a))` if
`Aug_A(b, a) < min(a, b)`, and `(b − q)/(b − b|_a)` if `Aug_A(b, a) = min(a, b)`.

**Formalization Note.** The second case is the `else` branch (`Aug_A(b, a) ≤ min(a, b)` always,
p.23). -/
noncomputable def xA (a b : ℝ) (A : Mech S null) (q : ℝ) : ℝ :=
  if mAug a A b a < min a b then
    (b - q - mAug a A (b - q) a) / (min a b - mAug a A (min a b) a)
  else (b - q) / (b - max 0 (b - a))

end CompetingSellers


