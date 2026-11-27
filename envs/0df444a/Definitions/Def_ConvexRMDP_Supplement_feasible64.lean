-- Prove2me | Definitions.Def_ConvexRMDP_Supplement_feasible64
-- name    : ConvexRMDP_Supplement_feasible64
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:55:05.356501+00:00
-- url     : https://prove2.me/theorems/7dd1b5b9-aa16-4f47-afad-b7fe4816f4b6
-- title:
--   Feasible set of the conic program (6.4) (corrected: min over $s'$ inside each action term)
-- statement:
--   Let $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ be an s-rectangular robust MDP, $b > 0$, $\omega_b(s,a) = \exp(b\,r_{sa})/|\mathcal A|$, and let $g_{s,i}$ ($i = 1,\dots,m$) be the constraint functions of Assumption 6.1. The variables of (6.4) are $x \in \mathbb R^{\mathcal S}$; for each $s$, $\xi_s \in \mathbb R^m$ and $y_s, y^i_s \in \mathbb R^{\mathcal A \times \mathcal S}$; for each $(s,a)$, $\alpha_{sa}, u_{sa} \in \mathbb R$, $z_{sa} \in \mathbb R^{\mathcal S}$ and an epigraph variable $w_{sa} \in \mathbb R$. A point is **feasible** when
--
--   1. $w_{sa} \le y_{sas'} + \omega_b(s,a)\, z_{sas'}$ for all $(s,a,s')$;
--   2. for all $s$,
--   $$
--   x_s \le -\sum_{i=1}^m \xi_{si}\, g^*_{s,i}\!\left(\frac{y^i_s}{\xi_{si}}\right) + \sum_{a \in \mathcal A}\left( w_{sa} + \omega_b(s,a)\left(\frac{1-\gamma}{\gamma}\,u_{sa} + \frac{1+\log\gamma}{\gamma}\,\alpha_{sa}\right)\right);
--   $$
--   3. $(x_{s'}, \alpha_{sa}, z_{sas'}) \in \mathcal K_{\exp}$ for all $(s,a,s')$ and $(1, \alpha_{sa}, u_{sa}) \in \mathcal K_{\exp}$ for all $(s,a)$;
--   4. $\sum_i y^i_s = y_s$, $x_s \ge 1$, $\xi_s \in \mathbb R^m_+$ and $\alpha_{sa} \ge 0$.
--
--   The program (6.4) maximizes $\sum_s x_s$ over this set (Theorem 6.2).
--
--   **Correction.** The paper prints $x_s \le -\sum_i \xi_{si} g^*_{s,i}(y^i_s/\xi_{si}) + \sum_a y_{sas'} + \omega_b(s,a)\big(z_{sas'} + \dots\big)$ for all $s, s'$, which takes the minimum over $s'$ outside the sum over actions; Lemma 6.1, from which (6.4) is assembled, has $\min_{s'}\{\dots\}$ inside each action term. The epigraph variable $w_{sa} \le \min_{s'}(y_{sas'} + \omega_b(s,a) z_{sas'})$ puts it back inside.
--
--   **Formalization Note** The conjugates $g^*_{s,i}$ are taken on $\mathbb R^{\mathcal A \times \mathcal S}$ with the pairing $\sum_{a,s'} y_{as'} P_{as'}$. The perspective terms may equal $+\infty$, so the right-hand side of item 2 is an extended real number; a $+\infty$ term violates the constraint.
-- source:
--   Grand-Clément & Petrik, arXiv:2209.10187v2, Theorem 6.2, program (6.4), p.21; corrected with Lemma 6.1, p.21

import Mathlib
import Definitions.Def_ConvexRMDP_Supplement_SRMDP_tOp
import Definitions.Def_ConvexRMDP_Supplement_persp
import Definitions.Def_ConvexRMDP_Supplement_Kexp

namespace ConvexRMDP

namespace Supplement

variable {S A : Type*} [Fintype S] [Fintype A]

/-- The variables of the conic program (6.4), in the order `(x, ξ, α, y, yⁱ, u, z, w)`:
`x ∈ ℝ^S`; for each `s`: `ξ_s ∈ ℝ^m`, `y_s ∈ ℝ^{A×S}`, `yⁱ_s ∈ ℝ^{A×S}` (`i ∈ [m]`); for each `(s,a)`:
`α_{sa} ∈ ℝ`, `u_{sa} ∈ ℝ`, `z_{sa} ∈ ℝ^S` and the epigraph variable `w_{sa} ∈ ℝ` of the corrected
program. A product of real vector spaces. -/
abbrev Vars64 (S A : Type*) (m : ℕ) :=
  (S → ℝ) × (S → Fin m → ℝ) × (S → A → ℝ) × (S → A → S → ℝ) ×
    (S → Fin m → A → S → ℝ) × (S → A → ℝ) × (S → A → S → ℝ) × (S → A → ℝ)

/-- **The feasible set of the conic program (6.4), corrected** (Grand-Clément & Petrik,
arXiv:2209.10187v2, Theorem 6.2, p.21). With `ω_b(s,a) = exp_b(r_{sa})/|A|`, a point
`(x, ξ, α, y, yⁱ, u, z, w)` is feasible when
* `w_{sa} ≤ y_{sas'} + ω_b(s,a) z_{sas'}` for all `(s,a,s')`;
* `x_s ≤ −∑_i ξ_{si} g*_{s,i}(yⁱ_s/ξ_{si}) + ∑_a (w_{sa} + ω_b(s,a)(((1−γ)/γ) u_{sa} + ((1+log γ)/γ) α_{sa}))`
  for all `s`;
* `(x_{s'}, α_{sa}, z_{sas'}) ∈ 𝒦_exp` for all `(s,a,s')` and `(1, α_{sa}, u_{sa}) ∈ 𝒦_exp` for all `(s,a)`;
* `∑_i yⁱ_s = y_s`, `x_s ≥ 1`, `ξ_s ∈ ℝ^m_+`, `α_{sa} ∈ ℝ_+`.

**Correction.** The paper prints
`x_s ≤ −∑_i ξ_{si} g*_{s,i}(yⁱ_s/ξ_{si}) + ∑_a y_{sas'} + ω_b(s,a)(z_{sas'} + …), ∀ s, s'`, which places
the minimum over `s'` outside the sum over actions; Lemma 6.1, which the program is built from, has it
inside each action term. The epigraph variable `w_{sa} ≤ min_{s'}(y_{sas'} + ω_b(s,a) z_{sas'})` restores
that placement.

**Formalization Note.** `ℝ^{A×S}` is `A → S → ℝ`; the conjugate `g*_{s,i}` is taken on the uncurried
space `A × S → ℝ` (`conj` pairs `yᵀp = ∑_{(a,s')} y_{as'} p_{as'}`). The perspective terms take values in
`ℝ ∪ {+∞}`, so the right-hand side of the `x_s` constraint is `EReal`: a `+∞` term makes it `−∞`
(constraint infeasible). -/
def feasible64 (M : SRMDP S A) (b : ℝ) (m : ℕ) (g : S → Fin m → (A → S → ℝ) → ℝ) :
    Set (Vars64 S A m) :=
  fun ⟨x, ξ, α, y, yi, u, z, w⟩ =>
    (∀ s a s', w s a ≤ y s a s' + M.omega b s a * z s a s') ∧
    (∀ s, ((x s : ℝ) : EReal) ≤
        -(∑ i, persp (conj (fun q : A × S → ℝ => ((g s i (Function.curry q) : ℝ) : EReal)))
            (ξ s i) (Function.uncurry (yi s i))) +
          ((∑ a, (w s a + M.omega b s a *
            ((1 - M.γ) / M.γ * u s a + (1 + Real.log M.γ) / M.γ * α s a)) : ℝ) : EReal)) ∧
    (∀ s a s', (x s', α s a, z s a s') ∈ Kexp) ∧
    (∀ s a, ((1 : ℝ), α s a, u s a) ∈ Kexp) ∧
    (∀ s, ∑ i, yi s i = y s) ∧
    (∀ s, 1 ≤ x s) ∧
    (∀ s i, 0 ≤ ξ s i) ∧
    (∀ s a, 0 ≤ α s a)

end Supplement

end ConvexRMDP


