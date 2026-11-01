-- Prove2me | Definitions.Def_LearnCollude_Assumption1
-- name    : LearnCollude_Assumption1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:03:19.036847+00:00
-- url     : https://prove2.me/theorems/948432e4-1aa3-4bc6-ab16-19150f0eacfc
-- title:
--   Assumption 1, hypothesis A1.3, the global optimal price $p^*$, the gap $\delta_i$
-- statement:
--   **Assumption 1** has two parts, for constants $K_1>K_0>0$ and $K_3>K_2>0$.
--
--   1. There is a unique maximizer $p^{col}\in(0,p_1^{\max})\times(0,p_2^{\max})$ of $r$ on $B$, and for all $p\in B$,
--   $$
--   (p-p^{col})^\top\nabla r(p)\le -K_0\|p-p^{col}\|^2,\qquad \|\nabla r(p)\|\le K_1\|p-p^{col}\|.
--   $$
--   2. There is a unique Nash equilibrium $p^{com}$. For each rival price $y$ in its range, firm $i$'s revenue has a unique maximizer $\phi_i(y)\in(0,p_i^{\max})$ in the firm's own price; $\phi_i$ is continuously differentiable; and for all $p\in B$,
--   $$
--   (p_i-\phi_i(p_{i'}))\,\partial_{p_i}r_i(p)\le -K_2|p_i-\phi_i(p_{i'})|^2,\qquad |\partial_{p_i}r_i(p)|\le K_3|p_i-\phi_i(p_{i'})|.
--   $$
--
--   **Hypothesis A1.3** is not in the paper. It asks for a $K_4>0$ with
--   $$
--   (p_1-p_1^{com})\,\partial_{p_1}r_1(p)+(p_2-p_2^{com})\,\partial_{p_2}r_2(p)\le -K_4\|p-p^{com}\|^2\qquad\text{for all }p\in B.
--   $$
--   It is the analogue for $p^{com}$ of the first inequality of part 1. It is needed because part 2 allows the mean dynamics of the competitive recursion to have a stable periodic orbit (numerical evidence), and because the printed proof of Theorem 2 does not close. Linear demand (9) satisfies it.
--
--   The **global optimal price** is
--   $$
--   p^*=\begin{cases}p^{col}&\text{if }r_i(p^{col})>r_i(p^{com})\text{ for both }i,\\ p^{com}&\text{otherwise.}\end{cases}
--   $$
--   This corrects the index of the printed (4). The **revenue gap** is $\delta_i=|r_i(p^{col})-r_i(p^{com})|$. There is **no one-sided tie** if no firm $i$ has $r_i(p^{col})=r_i(p^{com})$ while $r_{i'}(p^{col})>r_{i'}(p^{com})$.
--
--   **Formalization Note** The points $p^{col},p^{com}$ and the functions $\phi_i$ are fields of the structure, pinned down by its uniqueness clauses. A Nash equilibrium is the published definition `CrossLicensing.ExPost.IsNE`, on the two price intervals. The printed condition $\phi_2(p_1)\in(0,p_1^{\max})$ is a typo for $(0,p_2^{\max})$.
-- source:
--   Meylahn–den Boer, Learning to collude in a pricing duopoly, SSRN:3741385 (PDF of 2021-12-06), §2, pp. 9–11, eqs. (4), (15) p. 18, Assumption 1

import Mathlib
import Definitions.Def_CrossLicensing_ExPost_Game
import Definitions.Def_LearnCollude_Model

open Set

namespace LearnCollude

/-- `x` is the unique maximizer of `f` on `s`. -/
def IsUniqueMaximizerOn {α : Type*} (f : α → ℝ) (s : Set α) (x : α) : Prop :=
  x ∈ s ∧ ∀ y ∈ s, y ≠ x → f y < f x

/-- `q = (q₁, q₂)` is a **Nash equilibrium** of the pricing game, Meylahn–den Boer, SSRN:3741385
(PDF of 2021-12-06), §2, p. 9: `q` lies in the box, and neither firm gains by a unilateral deviation
within its own price interval. -/
def IsNash (M : Model) (q : ℝ × ℝ) : Prop :=
  CrossLicensing.ExPost.IsNE (Icc 0 (M.pmax 0)) (Icc 0 (M.pmax 1))
    (fun own rival => M.r 0 (profile 0 own rival))
    (fun own rival => M.r 1 (profile 1 own rival)) q

/-- **Assumption 1** (Assumptions on the demand functions), Meylahn–den Boer, SSRN:3741385
(PDF of 2021-12-06), pp. 10–11.

Part 1: `pcol ∈ (0, pmax₁) × (0, pmax₂)` is the unique maximizer of `r` on the box, and
`(p − pcol)ᵀ∇r(p) ≤ −K₀‖p − pcol‖²`, `‖∇r(p)‖ ≤ K₁‖p − pcol‖` on the box, for `K₁ > K₀ > 0`.

Part 2: `pcom` is the unique Nash equilibrium. For each rival price `y` there is a unique maximizer
`φᵢ(y)` of firm `i`'s revenue in its own price; it lies in `(0, pmaxᵢ)`, it is continuously
differentiable in `y`, and on the box `(pᵢ − φᵢ(p_{i'})) ∂_{pᵢ} rᵢ(p) ≤ −K₂|pᵢ − φᵢ(p_{i'})|²`,
`|∂_{pᵢ} rᵢ(p)| ≤ K₃|pᵢ − φᵢ(p_{i'})|`, for `K₃ > K₂ > 0`, the same constants for both firms.

**Formalization Note** The points `pcol`, `pcom` and the functions `φᵢ` are fields, and they are pinned
down by the uniqueness clauses; the constants `Kₖ` are any constants that work. The two firms' clauses of
part 2 are one `∀ i` clause. The printed condition `φ₂(p₁) ∈ (0, pmax₁)` (p. 11) is a typo for
`(0, pmax₂)`, as `φ₂` is a price of firm 2. -/
structure Assumption1 (M : Model) where
  /-- The constant `K₀`. -/
  K₀ : ℝ
  /-- The constant `K₁`. -/
  K₁ : ℝ
  /-- The constant `K₂`. -/
  K₂ : ℝ
  /-- The constant `K₃`. -/
  K₃ : ℝ
  /-- The joint-revenue maximizer `pcol`. -/
  pcol : Prices
  /-- The Nash equilibrium `pcom`. -/
  pcom : Prices
  /-- The best responses `φᵢ`, as functions of the rival's price. -/
  φ : Fin 2 → ℝ → ℝ
  K₀_pos : 0 < K₀
  K₀_lt_K₁ : K₀ < K₁
  pcol_mem : ∀ i, pcol i ∈ Ioo 0 (M.pmax i)
  pcol_max : IsUniqueMaximizerOn M.jointRevenue (box M.pmax) pcol
  pcol_inner : ∀ p ∈ box M.pmax,
    inner ℝ (p - pcol) (M.grad M.jointRevenue p) ≤ -K₀ * ‖p - pcol‖ ^ 2
  pcol_grad : ∀ p ∈ box M.pmax, ‖M.grad M.jointRevenue p‖ ≤ K₁ * ‖p - pcol‖
  K₂_pos : 0 < K₂
  K₂_lt_K₃ : K₂ < K₃
  pcom_nash : IsNash M (pcom 0, pcom 1)
  pcom_unique : ∀ q, IsNash M q → q = (pcom 0, pcom 1)
  φ_mem : ∀ i, ∀ y ∈ Icc 0 (M.pmax (other i)), φ i y ∈ Ioo 0 (M.pmax i)
  φ_max : ∀ i, ∀ y ∈ Icc 0 (M.pmax (other i)),
    IsUniqueMaximizerOn (fun x => M.r i (profile i x y)) (Icc 0 (M.pmax i)) (φ i y)
  φ_contDiffOn : ∀ i, ContDiffOn ℝ 1 (φ i) (Icc 0 (M.pmax (other i)))
  own_inner : ∀ i, ∀ p ∈ box M.pmax,
    (p i - φ i (p (other i))) * M.ownPartial i p ≤ -K₂ * |p i - φ i (p (other i))| ^ 2
  own_bound : ∀ i, ∀ p ∈ box M.pmax,
    |M.ownPartial i p| ≤ K₃ * |p i - φ i (p (other i))|

/-- **Stability of the competitive recursion** (hypothesis A1.3): for a `K₄ > 0` and every `p` in the
box, `(p₁ − pcom₁) ∂_{p₁} r₁(p) + (p₂ − pcom₂) ∂_{p₂} r₂(p) ≤ −K₄‖p − pcom‖²`.

**Formalization Note** This is a correction, not a condition of the paper. It is the analogue for
`pcom` of the first inequality of Assumption 1.1, and it is needed because Assumption 1.2 allows the
mean dynamics of the competitive recursion to have a stable periodic orbit (numerical evidence). The
printed proof of Theorem 2 (Meylahn–den Boer, SSRN:3741385, PDF of 2021-12-06, pp. 34–40) does not
close. Linear demand (9), p. 11, satisfies it. -/
structure A13 {M : Model} (A : Assumption1 M) where
  /-- The constant `K₄`. -/
  K₄ : ℝ
  K₄_pos : 0 < K₄
  inner_le : ∀ p ∈ box M.pmax,
    ∑ i, (p i - A.pcom i) * M.ownPartial i p ≤ -K₄ * ‖p - A.pcom‖ ^ 2

variable {M : Model}

open Classical in
/-- The **global optimal price** `p*`, Meylahn–den Boer, SSRN:3741385 (PDF of 2021-12-06), eq. (4),
p. 9, corrected: `pcol` if `rᵢ(pcol) > rᵢ(pcom)` for both `i`, and `pcom` otherwise.

**Formalization Note** The printed (4) compares `r₂(pcol)` with `r₁(pcom)`. The sentence before it
("`rᵢ(pcol) > rᵢ(pcom)` for both `i`") and the comparison in policy (10) use the same index on both
sides, and with the printed index Theorem 3 fails. -/
noncomputable def pStar (A : Assumption1 M) : Prices :=
  if ∀ i, M.r i A.pcom < M.r i A.pcol then A.pcol else A.pcom

/-- The revenue gap `δᵢ = |rᵢ(pcol) − rᵢ(pcom)|`, Meylahn–den Boer, SSRN:3741385
(PDF of 2021-12-06), eq. (15), p. 18. -/
noncomputable def revenueGap (A : Assumption1 M) (i : Fin 2) : ℝ :=
  |M.r i A.pcol - M.r i A.pcom|

/-- There is no **one-sided tie**: no firm `i` has `rᵢ(pcol) = rᵢ(pcom)` while the other firm strictly
prefers `pcol`. In such an instance the decision of phase 5 of policy (10) rests on noise that does
not vanish, and the time-average price need not converge to `p*`. -/
def NoOneSidedTie (A : Assumption1 M) : Prop :=
  ¬ ∃ i, M.r i A.pcol = M.r i A.pcom ∧ M.r (other i) A.pcom < M.r (other i) A.pcol

end LearnCollude


