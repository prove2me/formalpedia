-- Prove2me | Definitions.Def_BoundedEntropyGames_ConvRate_Proof
-- name    : BoundedEntropyGames_ConvRate_Proof
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:45.32401+00:00
-- url     : https://prove2.me/theorems/9a3cfd87-4477-4e5c-b9c3-e7e2d162b3ea
-- title:
--   §2.3, §3.2–§3.3, pp. 10–21 — d₁, the random mapping law p_F, p_{f(X)Y}, block lengths (17), ideal block law (22), i.i.d. joint law
-- statement:
--   Objects used in the proof of Theorem 6. Logarithms are in base two.
--
--   1. For a pmf $p$, $d_1(p)=\frac{1}{2\log e}\big(\sum_x p(x)(\log p(x))^2-H(p)^2\big)$, the value of $-\frac{d}{d\alpha}H_\alpha(p)$ at $\alpha=1$ (p. 10).
--   2. For a joint pmf $p_{XY}$, with conditional pmfs $p_{X|Y=y}=p_{XY}(\cdot,y)/p_Y(y)$,
--   $$
--   d_1(X|Y)=\sum_y p_Y(y)\,d_1(p_{X|Y=y})+\frac{1}{2\log e}\Big(\sum_y p_Y(y)H(X|Y=y)^2-H(X|Y)^2\Big)\quad\text{(p. 11)}.
--   $$
--   3. The **random mapping** $F:\mathcal X\to\mathcal A$ of Definition 13 has i.i.d. values $F(x)\sim p_A$, so its law on the finite set of maps is $p_F(f)=\prod_x p_A(f(x))$.
--   4. For a map $f:\mathcal X\to\mathcal A$, $p_{f(X)Y}(a,y)=\sum_{x:f(x)=a}p_{XY}(x,y)$ is the joint pmf of $(f(X),Y)$.
--   5. **Block lengths** (17): dividing $n$ stages into $f$ blocks, block $i$ has $N_{n,i}=\lfloor n/f\rfloor+1$ stages if $i\le n\bmod f$ and $\lfloor n/f\rfloor$ otherwise.
--   6. **Ideal block law** (22): $q(a_1,\dots,a_N)=\prod_{t=1}^{m}p^{(1)}(a_t)\prod_{t=m+1}^{N}p^{(2)}(a_t)$.
--   7. The joint pmf of $N$ i.i.d. copies of $(X,Y)$: $p_{X^NY^N}(x^N,y^N)=\prod_{t=1}^Np_{XY}(x_t,y_t)$.
--
--   These objects state the Taylor bounds (3)–(6), the simulation lemma (Lemma 14) and its Appendix A estimates, and the block construction of §3.3.
--
--   **Formalization Note** "$\log e$" is $\log_2 e$. The conditional pmf at a $y$ with $p_Y(y)=0$ is the zero function, and every term in which it appears is multiplied by $p_Y(y)=0$. Block and stage indices are 0-based: block $i$ of the paper is index $i-1$, and in (22) stage $t\le m$ of the paper is index $t-1<m$.
-- source:
--   Valizadeh, Gohari, Playing Games with Bounded Entropy: Convergence Rate and Approximate Equilibria, arXiv:1902.03676v1, pp. 10–11 (d₁(X), d₁(X|Y)), p. 17 Definition 13, p. 18 Lemma 14 (p_{f(X)Y}), p. 19 (17), p. 21 (22), (25)

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting

namespace BoundedEntropyGames.ConvRate

/-! Objects used in the proof of Theorem 6 (§2.3, §3.2, §3.3 and Appendix A of
Valizadeh–Gohari, arXiv:1902.03676v1). -/

/-- `d_1(X) = -(d/dα) H_α(X)|_{α=1} = (1/(2 log e)) (∑ p(x) (log p(x))² - H(X)²)` (p. 10),
logarithms in base 2. -/
noncomputable def d1 {T : Type*} [Fintype T] (p : T → ℝ) : ℝ :=
  1 / (2 * Real.logb 2 (Real.exp 1)) * (∑ t, p t * Real.logb 2 (p t) ^ 2 - shannon p ^ 2)

/-- The conditional pmf `p_{X|Y=y}(x) = p_XY(x,y) / p_Y(y)` (the zero function when
`p_Y(y) = 0`). -/
noncomputable def condPMF {𝒳 𝒴 : Type*} [Fintype 𝒳] (pXY : 𝒳 × 𝒴 → ℝ) (y : 𝒴) : 𝒳 → ℝ :=
  fun x => pXY (x, y) / marginalY pXY y

/-- `d_1(X|Y) = -(d/dα) H_α(X|Y)|_{α=1}
  = ∑_y p_Y(y) d_1(p_{X|Y=y}) + (1/(2 log e)) (∑_y p_Y(y) H(X|Y=y)² - H(X|Y)²)` (p. 11). -/
noncomputable def condD1 {𝒳 𝒴 : Type*} [Fintype 𝒳] [Fintype 𝒴] (pXY : 𝒳 × 𝒴 → ℝ) : ℝ :=
  ∑ y, marginalY pXY y * d1 (condPMF pXY y) +
    1 / (2 * Real.logb 2 (Real.exp 1)) *
      (∑ y, marginalY pXY y * shannon (condPMF pXY y) ^ 2 - condEntropy pXY ^ 2)

/-- The law `p_F` of the random mapping `F : 𝒳 → 𝒜` of Definition 13 (p. 17), whose values
`F(x)` are i.i.d. with law `p_A`: `p_F(f) = ∏_x p_A(f(x))`. -/
noncomputable def pF {𝒳 𝒜 : Type*} [Fintype 𝒳] (pA : 𝒜 → ℝ) (f : 𝒳 → 𝒜) : ℝ :=
  ∏ x, pA (f x)

/-- The joint pmf `p_{f(X)Y}` of `(f(X), Y)` when `(X, Y) ∼ p_XY`. -/
noncomputable def pfXY {𝒳 𝒴 𝒜 : Type*} [Fintype 𝒳] [DecidableEq 𝒜] (pXY : 𝒳 × 𝒴 → ℝ)
    (f : 𝒳 → 𝒜) : 𝒜 × 𝒴 → ℝ :=
  fun z => ∑ x, if f x = z.1 then pXY (x, z.2) else 0

/-- The block lengths (17), p. 19, with 0-based block index `i` (block `i + 1` of the paper):
`N_{n,i} = ⌊n/f⌋ + 1` for the first `n mod f` blocks and `⌊n/f⌋` for the others. -/
def blockLen (n f i : ℕ) : ℕ :=
  n / f + if i < n % f then 1 else 0

/-- The ideal block law (22), p. 21: `m` i.i.d. draws from `p^(1)` followed by `N - m` i.i.d.
draws from `p^(2)` (0-based stage index: stage `t < m` uses `p^(1)`). -/
noncomputable def idealBlock {𝒜 : Type*} (p₁ p₂ : 𝒜 → ℝ) (m N : ℕ) (a : Fin N → 𝒜) : ℝ :=
  ∏ t : Fin N, if (t : ℕ) < m then p₁ (a t) else p₂ (a t)

/-- The pmf of `(X^N, Y^N)` for `N` i.i.d. draws from `p_XY`. -/
noncomputable def iidJoint {𝒳 𝒴 : Type*} (pXY : 𝒳 × 𝒴 → ℝ) (N : ℕ) :
    (Fin N → 𝒳) × (Fin N → 𝒴) → ℝ :=
  fun z => ∏ t, pXY (z.1 t, z.2 t)

end BoundedEntropyGames.ConvRate


