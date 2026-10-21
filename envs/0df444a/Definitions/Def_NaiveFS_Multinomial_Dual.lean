-- Prove2me | Definitions.Def_NaiveFS_Multinomial_Dual
-- name    : NaiveFS_Multinomial_Dual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:14:50.095123+00:00
-- url     : https://prove2.me/theorems/507f1bb3-ee9a-4a8a-bbd0-a39fd9811ee9
-- title:
--   §3.4, p. 7 and Proposition 3.7, p. 11 — the Lagrangian dual of (SMNB), v(µ), w(µ), the objective of (17), and the corrected bidual (D)
-- statement:
--   The duality objects attached to sparse multinomial naive Bayes. Notation ($f^\pm>0$, $g$, $S$, $\phi$, $\psi$) is that of the model definition.
--
--   1. **Lagrangian.** For multipliers $\mu^+,\mu^-\in\mathbb R$, $\lambda\ge0$ and $\theta^\pm\in(0,\infty)^m$,
--   $$L=f^{+\top}\log\theta^++f^{-\top}\log\theta^-+\mu^+(1-\mathbf 1^\top\theta^+)+\mu^-(1-\mathbf 1^\top\theta^-)+\lambda\big(k-\|\theta^+-\theta^-\|_0\big).$$
--   2. **Dual value.** The dual function is $\sup_{\theta^\pm>0}L$, and the dual value is its infimum over $\mu^+,\mu^->0$, $\lambda\ge0$.
--   3. **The vectors of (17).** For $\mu=(\mu^+,\mu^-)>0$,
--   $$v_i(\mu)=(f^+_i+f^-_i)\log\frac{f^+_i+f^-_i}{\mu^++\mu^-},\qquad w_i(\mu)=f^+_i\log\frac{f^+_i}{\mu^+}+f^-_i\log\frac{f^-_i}{\mu^-},$$
--   and the objective of (17) is $\mu^++\mu^-+\lambda k+\sum_{i=1}^m\max\big(v_i(\mu),w_i(\mu)-\lambda\big)$.
--   4. **Bidual (D).** For $x\in[0,1]^m$ with $\mathbf 1^\top x\le k$ and $z=\mathbf 1-x$,
--   $$D(x)=z^\top(g\circ\log g)+x^\top(f^+\circ\log f^++f^-\circ\log f^-)+(x^\top g)\log(x^\top g)-(\mathbf 1^\top g)\log(\mathbf 1^\top g)-(x^\top f^+)\log(x^\top f^+)-(x^\top f^-)\log(x^\top f^-).$$
--
--   These objects carry the two routes to the quality estimate: the dual identity of §3.4 and the primalization of §3.7.
--
--   **Formalization Note** The inner maximization is over $\theta^\pm\in(0,\infty)^m$, not the box $[0,1]^m$ printed on p. 7: the paper's closed forms (15)–(16) ignore the upper bound, and with the box the dual value can be strictly smaller than $\psi(k)$ (for $f^+=(1000,1,1)$, $f^-=(1,1,3)$, $k=1$ the box dual is below $-29.994$ while $\psi(1)\approx-29.988$). The multipliers are restricted to $\mu^\pm>0$, as the page does after (15); for $\mu^\pm\le0$ the inner supremum is $+\infty$. **(D) is corrected**: the printed objective carries an extra term $-(x^\top g)$, which comes from dropping $\alpha(p^++p^-)=x^\top g$ in the last step of the proof on p. 12; with it the maximum of (D) is strictly below $\psi(k)$ and strong duality fails. The variable $z$ is eliminated as $z=\mathbf 1-x$, and $x\in\mathbb R^m$ (the page writes $\mathbb R^n$). At $x^\top f^\pm=0$, Lean's $0\cdot\log0=0$ is the convention $0\log0=0$.
-- source:
--   Askari, d'Aspremont & El Ghaoui, Naive Feature Selection, arXiv:1905.09884v4, p. 7 (§3.4, Lagrangian dual, (14)–(17), v(µ), w(µ)); p. 11, Proposition 3.7 (D)

import Mathlib
import Definitions.Def_NaiveFS_Multinomial_Model

namespace NaiveFS.Multinomial

open Finset

/-- The Lagrangian of (SMNB) (§3.4, p. 7):
`f⁺ᵀ log θ⁺ + f⁻ᵀ log θ⁻ + µ⁺(1 − 1ᵀθ⁺) + µ⁻(1 − 1ᵀθ⁻) + λ(k − ‖θ⁺ − θ⁻‖₀)`. -/
noncomputable def lagrangian {m : ℕ} (fp fm : Fin m → ℝ) (k : ℕ) (mup mum lam : ℝ)
    (θp θm : Fin m → ℝ) : ℝ :=
  objective fp fm θp θm + mup * (1 - ∑ i, θp i) + mum * (1 - ∑ i, θm i) +
    lam * ((k : ℝ) - ((univ.filter (fun i => θp i ≠ θm i)).card : ℝ))

/-- The dual function: the supremum of the Lagrangian over `θ⁺, θ⁻ ∈ (0,∞)ᵐ`.
For `µ± > 0` the set is nonempty and bounded above (`f log q − µ q ≤ f log(f/µ) − f`). -/
noncomputable def dualFn {m : ℕ} (fp fm : Fin m → ℝ) (k : ℕ) (mup mum lam : ℝ) : ℝ :=
  sSup {v | ∃ θp θm : Fin m → ℝ, (∀ i, 0 < θp i ∧ 0 < θm i) ∧
    v = lagrangian fp fm k mup mum lam θp θm}

/-- The Lagrangian dual value of (SMNB) (§3.4, p. 7): the infimum of the dual function over
`µ⁺, µ⁻ > 0` and `λ ≥ 0` (for `µ⁺ ≤ 0` or `µ⁻ ≤ 0` the inner supremum is `+∞`). -/
noncomputable def dualValue {m : ℕ} (fp fm : Fin m → ℝ) (k : ℕ) : ℝ :=
  sInf {v | ∃ mup mum lam : ℝ, 0 < mup ∧ 0 < mum ∧ 0 ≤ lam ∧
    v = dualFn fp fm k mup mum lam}

/-- `vᵢ(µ) := (f⁺ᵢ + f⁻ᵢ) log((f⁺ᵢ + f⁻ᵢ)/(µ⁺ + µ⁻))` (p. 7). -/
noncomputable def vmu {m : ℕ} (fp fm : Fin m → ℝ) (mup mum : ℝ) (i : Fin m) : ℝ :=
  (fp i + fm i) * Real.log ((fp i + fm i) / (mup + mum))

/-- `wᵢ(µ) := f⁺ᵢ log(f⁺ᵢ/µ⁺) + f⁻ᵢ log(f⁻ᵢ/µ⁻)` (p. 7). -/
noncomputable def wmu {m : ℕ} (fp fm : Fin m → ℝ) (mup mum : ℝ) (i : Fin m) : ℝ :=
  fp i * Real.log (fp i / mup) + fm i * Real.log (fm i / mum)

/-- The objective of (17), p. 7: `µ⁺ + µ⁻ + λk + Σᵢ max(vᵢ(µ), wᵢ(µ) − λ)`. -/
noncomputable def obj17 {m : ℕ} (fp fm : Fin m → ℝ) (k : ℕ) (mup mum lam : ℝ) : ℝ :=
  mup + mum + lam * k + ∑ i, max (vmu fp fm mup mum i) (wmu fp fm mup mum i - lam)

/-- Feasible set of the bidual (D) (Proposition 3.7, p. 11) after eliminating `z = 1 − x`:
`x ∈ [0,1]ᵐ`, `1ᵀx ≤ k`. -/
def DFeasible {m : ℕ} (k : ℕ) (x : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∑ i, x i ≤ k

/-- The objective of (D) (Proposition 3.7, p. 11), **corrected**: with `g = f⁺ + f⁻`, `z = 1 − x`,
`zᵀ(g ∘ log g) + xᵀ(f⁺ ∘ log f⁺ + f⁻ ∘ log f⁻) + (xᵀg) log(xᵀg) − (1ᵀg) log(1ᵀg)
 − (xᵀf⁺) log(xᵀf⁺) − (xᵀf⁻) log(xᵀf⁻)`.
The printed (D) carries an additional term `−(xᵀg)`; it comes from dropping
`α(p⁺ + p⁻) = xᵀg` in the last step of the proof (p. 12), and with it the strong-duality claim
is false. At `xᵀf± = 0` Lean's `0 * log 0 = 0` is the convention `0 log 0 = 0`. -/
noncomputable def Dobj {m : ℕ} (fp fm : Fin m → ℝ) (x : Fin m → ℝ) : ℝ :=
  let xg := ∑ i, x i * (fp i + fm i)
  let xp := ∑ i, x i * fp i
  let xm := ∑ i, x i * fm i
  ∑ i, (1 - x i) * ((fp i + fm i) * Real.log (fp i + fm i)) +
    ∑ i, x i * (fp i * Real.log (fp i) + fm i * Real.log (fm i)) +
    xg * Real.log xg - S fp fm * Real.log (S fp fm) - xp * Real.log xp - xm * Real.log xm

end NaiveFS.Multinomial


