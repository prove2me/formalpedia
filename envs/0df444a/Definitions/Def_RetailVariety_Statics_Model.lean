-- Prove2me | Definitions.Def_RetailVariety_Statics_Model
-- name    : RetailVariety_Statics_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:08.560032+00:00
-- url     : https://prove2.me/theorems/863250dd-0ee6-426a-96c8-0eb4dd938ea4
-- title:
--   Comparative-statics names: prefix sets $A_i$, standard normal c.d.f. $\Phi$, critical fractile $z$ of (6)
-- statement:
--   This file gives the names under which the comparative statics of van Ryzin and Mahajan (1999), Theorem 2, refer to three objects of the shared assortment model `RetailVariety.Structure.Model`. The MNL shares $q_j(S)$ and the profits $\pi_I$ of (7) and $\pi_T$ of (8) are not redefined here; the statements use `RetailVariety.Structure.share`, `RetailVariety.Structure.profitI` and `RetailVariety.Structure.profitT` directly.
--
--   1. **Prefix sets.** The variants $N=\{1,\dots,n\}$ are ordered by decreasing preference, $v_1\ge v_2\ge\dots\ge v_n$ (§3.1). The set of the $i$ most popular variants is
--   $$A_i=\{1,\dots,i\},\qquad 0\le i\le n,$$
--   so $A_0=\emptyset$ and $A_n=N$. It is the same set as the most-popular set of the shared model.
--   2. **Standard normal distribution function.** $\Phi(x)=\mathbb P(Z\le x)$ for a standard normal random variable $Z$.
--   3. **Critical fractile (6).** For a selling price $p$ and a unit cost $c$,
--   $$z=\Phi^{-1}\!\left(1-\frac{c}{p}\right),$$
--   taken as the least $x$ with $\Phi(x)\ge 1-c/p$. This is the same $z$ that enters the profit $\pi_I$ of the shared model. For $0<c<p$ it is the unique real number with $\Phi(z)=1-c/p$.
--
--   Theorem 2 compares profits on consecutive prefix sets $A_i$ and $A_{i+1}$, and its proof follows how $z$ moves with the price $p$; that is why $z$ is a function of $(p,c)$ and not a free parameter.
--
--   **Formalization Note** Variants are indexed by `Fin n` (0-based): the paper's variant $j$ is `⟨j-1, _⟩`, and `A n i` is the set of indices with value `< i`; it is defined to be `RetailVariety.Structure.popularSet n i`. $\Phi$ is `ProbabilityTheory.cdf (gaussianReal 0 1)`. Mathlib has no normal quantile, so $z$ is an infimum; it is defined to be `RetailVariety.Structure.criticalFractile p c`, so the two names agree by definition. Outside $0<c<p$ the set $\{x:\Phi(x)\ge 1-c/p\}$ is all of $\mathbb R$ (for $c\ge p>0$) and the infimum takes Lean's junk value $0$; every theorem using $z$ assumes $0<c<p$.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1502, eq. (6); p. 1503, §3.1 (ordering v_1 ≥ … ≥ v_n and A_i)

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model

open MeasureTheory ProbabilityTheory

namespace RetailVariety.Statics

/-- The prefix assortment `A_i = {1, …, i}` of the paper (§3.1, p. 1503), 0-based: the variants
`j : Fin n` with `j.val < i`. So `A n 0 = ∅` and `A n n = Finset.univ`. It is the same set as
`RetailVariety.Structure.popularSet n i`, under the name the comparative statics use. -/
def A (n i : ℕ) : Finset (Fin n) :=
  RetailVariety.Structure.popularSet n i

/-- The standard normal c.d.f. `Φ`. -/
noncomputable def stdNormalCdf (x : ℝ) : ℝ :=
  cdf (gaussianReal 0 1) x

/-- The critical fractile (6), p. 1502: `z = Φ⁻¹(1 - c/p)`, the least `x` with
`Φ(x) ≥ 1 - c/p`. This is `RetailVariety.Structure.criticalFractile`, the `z` inside the profit
`RetailVariety.Structure.profitI`. For `0 < c < p` it is the unique `x` with `Φ(x) = 1 - c/p`. -/
noncomputable def criticalFractile (p c : ℝ) : ℝ :=
  RetailVariety.Structure.criticalFractile p c

end RetailVariety.Statics


