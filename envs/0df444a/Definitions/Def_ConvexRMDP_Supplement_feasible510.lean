-- Prove2me | Definitions.Def_ConvexRMDP_Supplement_feasible510
-- name    : ConvexRMDP_Supplement_feasible510
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:52:36.931046+00:00
-- url     : https://prove2.me/theorems/ddbd493a-8bd2-5eff-94e9-671d1482ea99
-- title:
--   Feasible set of the conic program (5.10) (corrected: min over $s'$ inside each action term)
-- statement:
--   Let $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ be an sa-rectangular robust MDP, $b > 0$, $\omega_b(s,a) = \exp(b\,r_{sa})/|\mathcal A|$, and let $g_{sa,i}$ ($i = 1,\dots,m$) be the constraint functions of Assumption 5.1. The variables of (5.10) are $x \in \mathbb R^{\mathcal S}$ and, for each $(s,a)$, $\xi_{sa} \in \mathbb R^m$, $\alpha_{sa} \in \mathbb R$, $y_{sa}, y^i_{sa}, z_{sa} \in \mathbb R^{\mathcal S}$, $u_{sa} \in \mathbb R$ and an epigraph variable $w_{sa} \in \mathbb R$. A point is **feasible** when
--
--   1. $w_{sa} \le y_{sas'} + z_{sas'}$ for all $(s,a,s')$;
--   2. for all $s$,
--   $$
--   x_s \le \sum_{a \in \mathcal A} \omega_b(s,a)\left( w_{sa} + \frac{1-\gamma}{\gamma}\,u_{sa} + \frac{1+\log\gamma}{\gamma}\,\alpha_{sa} - \sum_{i=1}^m \xi_{sai}\, g^*_{sa,i}\!\left(\frac{y^i_{sa}}{\xi_{sai}}\right)\right);
--   $$
--   3. $(x_{s'}, \alpha_{sa}, z_{sas'}) \in \mathcal K_{\exp}$ for all $(s,a,s')$ and $(1, \alpha_{sa}, u_{sa}) \in \mathcal K_{\exp}$ for all $(s,a)$;
--   4. $\sum_i y^i_{sa} = y_{sa}$, $x_s \ge 1$, $\xi_{sa} \in \mathbb R^m_+$ and $\alpha_{sa} \ge 0$.
--
--   The program (5.10) maximizes $\sum_s x_s$ over this set (Theorem 5.1).
--
--   **Correction.** The paper prints the constraint $x_s \le \sum_a \omega_b(s,a)\big(y_{sas'} + z_{sas'} + \dots\big)$ for all $s, s'$, which takes the minimum over $s'$ outside the sum over actions, whereas Proposition 5.1 (5.3), from which (5.10) is assembled, has $\min_{s'}\{z_{s'} + y_{s'}\}$ inside each action term. The epigraph variable $w_{sa} \le \min_{s'}(y_{sas'} + z_{sas'})$ puts the minimum back inside.
--
--   **Formalization Note** The terms $\xi g^*(y/\xi)$ are perspectives of conjugates (with the paper's convention at $\xi = 0$) and may equal $+\infty$, so the right-hand side of item 2 is an extended real number; a $+\infty$ perspective makes it $-\infty$, and the constraint is then violated. The variables form a product of real vector spaces, so convexity and closedness of the feasible set are meaningful.
-- source:
--   Grand-Clément & Petrik, arXiv:2209.10187v2, Theorem 5.1, program (5.10), p.18; corrected with Proposition 5.1 (5.3), p.16

import Mathlib
import Definitions.Def_ConvexRMDP_RMDP_tOp
import Definitions.Def_ConvexRMDP_Supplement_persp
import Definitions.Def_ConvexRMDP_Supplement_Kexp

namespace ConvexRMDP

namespace Supplement

variable {S A : Type*} [Fintype S] [Fintype A]

/-- The variables of the conic program (5.10), in the order
`(x, ξ, α, y, yⁱ, u, z, w)`: `x ∈ ℝ^S`, and for each `(s,a)`: `ξ_{sa} ∈ ℝ^m`, `α_{sa} ∈ ℝ`,
`y_{sa} ∈ ℝ^S`, `yⁱ_{sa} ∈ ℝ^S` (`i ∈ [m]`), `u_{sa} ∈ ℝ`, `z_{sa} ∈ ℝ^S`, and the epigraph variable
`w_{sa} ∈ ℝ` of the corrected program. A product of real vector spaces, so convexity makes sense. -/
abbrev Vars510 (S A : Type*) (m : ℕ) :=
  (S → ℝ) × (S → A → Fin m → ℝ) × (S → A → ℝ) × (S → A → S → ℝ) ×
    (S → A → Fin m → S → ℝ) × (S → A → ℝ) × (S → A → S → ℝ) × (S → A → ℝ)

/-- **The feasible set of the conic program (5.10), corrected** (Grand-Clément & Petrik,
arXiv:2209.10187v2, Theorem 5.1, p.18). With `ω_b(s,a) = exp_b(r_{sa})/|A|`, a point
`(x, ξ, α, y, yⁱ, u, z, w)` is feasible when
* `w_{sa} ≤ y_{sas'} + z_{sas'}` for all `(s,a,s')`;
* `x_s ≤ ∑_a ω_b(s,a) (w_{sa} + ((1−γ)/γ) u_{sa} + ((1+log γ)/γ) α_{sa} − ∑_i ξ_{sai} g*_{sa,i}(yⁱ_{sa}/ξ_{sai}))`
  for all `s`;
* `(x_{s'}, α_{sa}, z_{sas'}) ∈ 𝒦_exp` for all `(s,a,s')` and `(1, α_{sa}, u_{sa}) ∈ 𝒦_exp` for all `(s,a)`;
* `∑_i yⁱ_{sa} = y_{sa}`, `x_s ≥ 1`, `ξ_{sa} ∈ ℝ^m_+`, `α_{sa} ∈ ℝ_+`.

**Correction.** The paper prints the constraint
`x_s ≤ ∑_a ω_b(s,a)(y_{sas'} + z_{sas'} + …), ∀ s, s'`, which places the minimum over `s'` outside the
sum over actions; Proposition 5.1 (5.3), which the program is built from, has it inside each action
term, `∑_a ω_b(s,a)(min_{s'}{z_{s'} + y_{s'}} + …)`. The epigraph variable `w_{sa} ≤ min_{s'}(y_{sas'} + z_{sas'})`
restores that placement.

**Formalization Note.** The terms `ξ g*(yⁱ/ξ)` are the perspective `persp (conj g) ξ yⁱ`, with the
paper's convention at `ξ = 0`; they take values in `ℝ ∪ {+∞}`, so the right-hand side of the `x_s`
constraint is `EReal`: a `+∞` perspective term makes it `−∞` (constraint infeasible). -/
def feasible510 (M : RMDP S A) (b : ℝ) (m : ℕ) (g : S → A → Fin m → (S → ℝ) → EReal) :
    Set (Vars510 S A m) :=
  fun ⟨x, ξ, α, y, yi, u, z, w⟩ =>
    (∀ s a s', w s a ≤ y s a s' + z s a s') ∧
    (∀ s, ((x s : ℝ) : EReal) ≤ ∑ a, ((M.omega b s a : ℝ) : EReal) *
        (((w s a + (1 - M.γ) / M.γ * u s a + (1 + Real.log M.γ) / M.γ * α s a : ℝ) : EReal) -
          ∑ i, persp (conj (g s a i)) (ξ s a i) (yi s a i))) ∧
    (∀ s a s', (x s', α s a, z s a s') ∈ Kexp) ∧
    (∀ s a, ((1 : ℝ), α s a, u s a) ∈ Kexp) ∧
    (∀ s a, ∑ i, yi s a i = y s a) ∧
    (∀ s, 1 ≤ x s) ∧
    (∀ s a i, 0 ≤ ξ s a i) ∧
    (∀ s a, 0 ≤ α s a)

end Supplement

end ConvexRMDP


