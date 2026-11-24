-- Prove2me | Definitions.Def_SurelyBetter_CLB_Supplement_SupportConfig
-- name    : SurelyBetter_CLB_Supplement_SupportConfig
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:48:49.402671+00:00
-- url     : https://prove2.me/theorems/42bb60b5-34c7-4d69-8607-c59a498a5bdd
-- title:
--   Definition 5 and §3, pp. 7624, 7633 — interior acts, lines and slopes, and support configurations (R, l_h, l_k)
-- statement:
--   The setting is that of Definitions 3–4 (the family $\mathcal F^{E,F,z,h}$, the set $H(z)$ and the better-than sets $G(\cdot)$). Points of the plane have horizontal coordinate the utility on $E\setminus F$ and vertical coordinate the utility on $F\setminus E$.
--
--   1. **Interior acts** (§3). An act $f$ is interior if for each state $s$ there are lotteries $\bar x(s),\underline x(s)$ with $\bar x(s)\succ f(s)\succ\underline x(s)$; in utility space, each value $u(f(s))$ lies strictly between two points of $U$.
--   2. **Lines and slopes.** A line is $\{p+t\,d: t\in\mathbb R\}$ with direction $d\neq0$; its slope is $d_2/d_1$.
--   3. **Rectangles.** $R=[a_0,a_1]\times[b_0,b_1]$, with left edge $\{a_0\}\times[b_0,b_1]$ and bottom edge $[a_0,a_1]\times\{b_0\}$, so that $\min_{r\in R}r(E\setminus F)=a_0$ and $\min_{r\in R}r(F\setminus E)=b_0$.
--   4. **Support configuration** (Definition 5). Let $h,k$ be acts of the family with $(u(h(E\setminus F)),u(h(F\setminus E)))=(h_a,h_b)$ and $(u(k(E\setminus F)),u(k(F\setminus E)))=(k_a,k_b)$. $(R,l_h,l_k)$ is a support configuration if $a_0<a_1$, $b_0<b_1$, $R\subseteq H(z)$, both $(h_a,h_b)$ and $(k_a,k_b)$ lie in the interior $(a_0,a_1)\times(b_0,b_1)$ of $R$, $l_h\neq l_k$ are lines, and
--      - (i) $l_h\cap G(h)\cap R=\{(h_a,h_b)\}$ and $l_h$ meets the left edge of $R$;
--      - (ii) $l_k\cap G(k)\cap R=\{(k_a,k_b)\}$ and $l_k$ meets the bottom edge of $R$;
--      - (iii) the line $l_3$ through $(k_a,h_b)$ and the intersection of $l_h$ with the left edge of $R$ meets the bottom edge of $R$.
--
--   Support configurations are the geometric objects over which Theorem 5 bounds the ratio of slopes $\mathrm{Slope}(l_h)/\mathrm{Slope}(l_k)$.
--
--   **Formalization Note** The printed definition says "a rectangle $R\subseteq H(z)\times H(z)$"; since the points of $R$ are pairs $(q(E\setminus F),q(F\setminus E))$ and $H(z)$ is already a set of such pairs, this is read as $R\subseteq H(z)$. The rectangle is axis-parallel and closed, as its left and bottom edges and the minima $\min_{r\in R}r(\cdot)$ in the definition presuppose (Figure 4), and it has nonempty interior because it contains two points in its interior. A line is given by a point and a nonzero direction; its slope depends only on the line. $l_h$ meets the left edge of $R$ in a single point because it passes through the interior point $(h_a,h_b)$, so "the intersection" in (iii) is unambiguous; it is written as an existential.
-- source:
--   Ghili & Klibanoff, If It Is Surely Better, Do It More? Implications for Preferences Under Ambiguity, Management Science 67(12) (2021), p. 7633, Definition 5; p. 7624, §3 (interior act)

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_SurelyBetter_CLB_Model
import Definitions.Def_SurelyBetter_CLB_Supplement_Family

namespace SurelyBetter.CLB.Supplement
open SurelyBetter.CLB

variable {S : Type*}

/-- §3, p. 7624: an act is interior if for each state `s` there are lotteries `x̄(s), x̲(s)` with
`x̄(s) ≻ f(s) ≻ x̲(s)`; in utility space, every value of the profile lies strictly between two
points of `U = u(X)`. -/
def IsInteriorProfile (U : Set ℝ) (v : S → ℝ) : Prop :=
  ∀ s, ∃ a ∈ U, ∃ b ∈ U, b < v s ∧ v s < a

/-- The line `{p + t d : t ∈ ℝ}` through `p` with direction `d` (a line when `d ≠ 0`). -/
def lineThrough (p d : ℝ × ℝ) : Set (ℝ × ℝ) := {x | ∃ t : ℝ, x = p + t • d}

/-- The slope `d₂ / d₁` of a line with direction `d` (vertical axis: utility on `F \ E`;
horizontal axis: utility on `E \ F`). -/
noncomputable def slope (d : ℝ × ℝ) : ℝ := d.2 / d.1

/-- The closed axis-parallel rectangle `R = [a₀, a₁] × [b₀, b₁]`. -/
def rect (a₀ a₁ b₀ b₁ : ℝ) : Set (ℝ × ℝ) := Set.Icc a₀ a₁ ×ˢ Set.Icc b₀ b₁

/-- The left edge `{q ∈ R : q(E \ F) = min_{r ∈ R} r(E \ F)}` of `R = [a₀, a₁] × [b₀, b₁]`. -/
def leftEdge (a₀ b₀ b₁ : ℝ) : Set (ℝ × ℝ) := {a₀} ×ˢ Set.Icc b₀ b₁

/-- The bottom edge `{q ∈ R : q(F \ E) = min_{r ∈ R} r(F \ E)}` of `R = [a₀, a₁] × [b₀, b₁]`. -/
def bottomEdge (a₀ a₁ b₀ : ℝ) : Set (ℝ × ℝ) := Set.Icc a₀ a₁ ×ˢ {b₀}

/-- Definition 5, p. 7633: `(R, l_h, l_k)` is a support configuration, where
`R = [a₀, a₁] × [b₀, b₁] ⊆ H(z)` contains `(ha, hb) = (u(h(E \ F)), u(h(F \ E)))` and
`(ka, kb) = (u(k(E \ F)), u(k(F \ E)))` in its interior, `l_h = lineThrough ph dh` and
`l_k = lineThrough pk dk` are distinct lines, and
(i) `l_h ∩ G(h) ∩ R = {(ha, hb)}` and `l_h` meets the left edge of `R`;
(ii) `l_k ∩ G(k) ∩ R = {(ka, kb)}` and `l_k` meets the bottom edge of `R`;
(iii) the line `l₃` through `(ka, hb)` and the intersection of `l_h` with the left edge of `R`
meets the bottom edge of `R`. -/
def IsSupportConfig (U : Set ℝ) (V : (S → ℝ) → ℝ) (E F : Set S) (uz : ℝ) (hp kp : S → ℝ)
    (ha hb ka kb a₀ a₁ b₀ b₁ : ℝ) (ph dh pk dk : ℝ × ℝ) : Prop :=
  a₀ < a₁ ∧ b₀ < b₁ ∧ rect a₀ a₁ b₀ b₁ ⊆ Hz U uz ∧
  (ha ∈ Set.Ioo a₀ a₁ ∧ hb ∈ Set.Ioo b₀ b₁) ∧ (ka ∈ Set.Ioo a₀ a₁ ∧ kb ∈ Set.Ioo b₀ b₁) ∧
  dh ≠ 0 ∧ dk ≠ 0 ∧ lineThrough ph dh ≠ lineThrough pk dk ∧
  (lineThrough ph dh ∩ betterSet U V E F uz hp hp ∩ rect a₀ a₁ b₀ b₁ = {(ha, hb)} ∧
    (lineThrough ph dh ∩ leftEdge a₀ b₀ b₁).Nonempty) ∧
  (lineThrough pk dk ∩ betterSet U V E F uz hp kp ∩ rect a₀ a₁ b₀ b₁ = {(ka, kb)} ∧
    (lineThrough pk dk ∩ bottomEdge a₀ a₁ b₀).Nonempty) ∧
  (∃ q ∈ lineThrough ph dh ∩ leftEdge a₀ b₀ b₁,
    (lineThrough (ka, hb) (q - (ka, hb)) ∩ bottomEdge a₀ a₁ b₀).Nonempty)

end SurelyBetter.CLB.Supplement


