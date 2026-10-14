-- Prove2me | Definitions.Def_IntMul_KappaFramework
-- name    : IntMul_KappaFramework
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-11T19:55:56.696507+00:00
-- url     : https://prove2.me/theorems/eff26f5d-3d1d-43b5-9768-7d4e9db37a54
-- title:
--   Moment inequality and crude-guard assembly for $\kappa$-improvement networks
-- statement:
--   Vocabulary for the community improvements of the exponent saving $\kappa$ in $T(n)=O(n(\lg n)^{1-\kappa})$, built on the OpenAI manuscript *Integer multiplication below $n\log n$* and on D. Colkitt's framework.
--
--   1. **Child-width histogram.** A finite linear interchange network of full width $m$ with $W$ roles is summarised by a list of pairs $(w,n_w)$: it makes $n_w$ recursive child calls of width $w$. Its moment at exponent $\tau$ is
--   $$\mathrm{histMoment}(h,m,\tau)=\sum_{(w,n_w)\in h} n_w\Big(\frac{w}{m}\Big)^{\tau}.$$
--   The network certifies the recursive saving $a$ (cost exponent $1-a$) when $\mathrm{histMoment}(h,m,1-a)<W$. Its rank sum is $s=\mathrm{histRankSum}(h)=\sum w\,n_w$.
--
--   2. **Crude-guard assembly.** For the bit saving $a_b$, complex saving $a_c$ and parameters $\beta,\varepsilon,x,C_1$, put $\tau=1-a_b$, $\sigma=1-a_c$, $\chi=\tau+(1-\beta)\max(\sigma-\tau,0)$, $\ell=\sigma+\beta(1-\sigma)$, $\lambda=\max(\tau,\sigma,\chi)+10^{-16}$, $\lambda'=\max(\lambda,\ell)+10^{-16}$, $\delta=10^{-22}/x$ and $\mathrm{poly}=(1+x)\delta$. Then $\mathrm{CrudeAssembly}(a_b,a_c,\beta,\varepsilon,x,C_1,\kappa,m_c,s_c)$ says that
--   $$0<\beta<1,\quad 2+m_c\ln s_c\le C_1,\quad \lambda'<1,\quad \varepsilon(2-\lambda')<1,\quad \varepsilon C_1<1+x,\quad 3\varepsilon<1+x,$$
--   $$0<\varepsilon<1,\quad 2\varepsilon-1<\lambda'\varepsilon,\quad 0<\delta<\tfrac18,$$
--   and that $\kappa$ is strictly below each cost margin
--   $$1-\varepsilon,\qquad \varepsilon(1-\lambda'),\qquad 1-\varepsilon-\mathrm{poly},\qquad \varepsilon,\qquad \max(\varepsilon,1-\varepsilon)(1-\tau).$$
--
--   These are the constraints and margins of `scripts/certificate_round3.py` with the crude depth guard (the complex recursion's dependency depth is bounded using its width $m_c$ and rank sum $s_c$), which Jain's rounds three to eight use to turn the two network savings into $\kappa$.
--
--   **Formalization Note** The $\lambda$ gaps $10^{-16}$, $\delta=10^{-22}/x$ and the sub-block parameter $y=\varepsilon$ are fixed exactly as in the script. The Lean checker `kappaOK` of the source replaces $C_1$ by any value with $C_1\ge 2+m_c\cdot\overline{\ln}(s_c)$; here the real logarithm is used.
-- source:
--   https://github.com/Swapnil-jain/integer-mult-kappa/tree/5868dc701a9bec375c9dc5391d992ab3b8c35f3f — scripts/certificate_round3.py (function evaluate, guard='crude': constraints `cons`, margins `margins`), lean/Round8.lean (momentOK, kappaOK); framework of D. Colkitt, https://github.com/CrocSwap/integer-mult-bounds/tree/56b66d58297deca1d7dd130247d720e960f77a37

import Mathlib

/-!
# Exponent bookkeeping of the community κ-improvements (Colkitt framework)

Shared vocabulary for the conditional κ-improvement witnesses built on the OpenAI manuscript
*Integer multiplication below n log n* and D. Colkitt's `integer-mult-bounds`.

* A finite linear network is summarised by its child-width histogram: `n_w` recursive child
  calls of width `w` (out of the full width `m`), on a network with `W` roles.  The recursive
  saving `a` of the network is certified by the moment inequality
  `∑_w n_w (w/m)^(1-a) < W` (`histMoment`).
* `CrudeAssembly` is the assembly of `scripts/certificate_round3.py` of
  S. Jain's `integer-mult-kappa` with the crude depth guard: from the bit saving `a_b`, the
  complex saving `a_c` and the parameters `β, ε, x, C₁`, every strict constraint holds and
  every cost margin exceeds `κ`.
-/

namespace IntMul.Kappa

/-- The moment `∑ n_w (w/m)^τ` of a child-width histogram, given as a list of pairs
`(w, n_w)`. -/
noncomputable def histMoment (h : List (ℕ × ℕ)) (m : ℕ) (τ : ℝ) : ℝ :=
  (h.map fun p => (p.2 : ℝ) * ((p.1 : ℝ) / m) ^ τ).sum

/-- The rank sum `s = ∑ w n_w` of a child-width histogram: the total width of all child
calls. -/
def histRankSum (h : List (ℕ × ℕ)) : ℕ :=
  (h.map fun p => p.1 * p.2).sum

/-- The crude-guard assembly of `certificate_round3.py` (with `y = ε`): with
`τ = 1 - a_b`, `σ = 1 - a_c`, `χ = τ + (1-β) max(σ-τ, 0)`, `leaf = σ + β(1-σ)`,
`λ = max(τ, σ, χ) + 10⁻¹⁶`, `λ' = max(λ, leaf) + 10⁻¹⁶`, `δ = 10⁻²²/x` and
`poly = (1+x)δ`, all constraints of the stack hold and `κ` lies strictly below each of
the cost margins `1-ε`, `ε(1-λ')`, `1-ε-poly`, `ε` and `max(ε,1-ε)(1-τ)`. Here `m_c` and
`s_c` are the width and rank sum of the complex network. -/
def CrudeAssembly (ab ac β ε x C₁ κ : ℝ) (mc sc : ℕ) : Prop :=
  let τ := 1 - ab
  let σ := 1 - ac
  let χ := τ + (1 - β) * max (σ - τ) 0
  let leaf := σ + β * (1 - σ)
  let lam := max (max τ σ) χ + 1 / 10 ^ 16
  let lamp := max lam leaf + 1 / 10 ^ 16
  let δ := 1 / 10 ^ 22 / x
  let poly := (1 + x) * δ
  (0 < β ∧ β < 1) ∧
  2 + (mc : ℝ) * Real.log sc ≤ C₁ ∧
  lamp < 1 ∧
  ε * (2 - lamp) < 1 ∧
  ε * C₁ < 1 + x ∧
  2 * ε + ε < 1 + x ∧
  0 < ε ∧ ε < 1 ∧
  2 * ε - 1 < lamp * ε ∧
  (0 < δ ∧ δ < 1 / 8) ∧
  κ < 1 - ε ∧
  κ < ε * (1 - lamp) ∧
  κ < 1 - ε - poly ∧
  κ < ε ∧
  κ < max ε (1 - ε) * (1 - τ)

end IntMul.Kappa


