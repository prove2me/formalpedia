-- Prove2me | Definitions.Def_GoldieRenewal_Implicit_RenewalMeasures
-- name    : GoldieRenewal_Implicit_RenewalMeasures
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:07.34937+00:00
-- url     : https://prove2.me/theorems/70ee2414-2268-420e-adfd-e1806b5317b8
-- title:
--   Convolution powers μ^{(n)}, renewal measures Σ η^{(n)}, the tilted law η, and p, q, η₊, η₋, η (9.11), η₀ of Case 2a
-- statement:
--   **Convolution powers and renewal measures** (pp. 128, 145). For a measure $\mu$ on $\mathbb R$, $\mu^{(0)} = \delta_0$ and $\mu^{(n+1)} = \mu*\mu^{(n)}$; the renewal measure of $\mu$ is $\sum_{n\ge0}\mu^{(n)}$. For a function $f$ and a measure $\rho$, $f*\rho(t) := \int_{\mathbb R} f(t-u)\,\rho(du)$.
--
--   Let $M$ be a real random variable with law $P(M\in\cdot)$ and $\kappa>0$.
--
--   **Case 1** (p. 145). $\eta(du) := e^{\kappa u}P(\log|M|\in du)$, a measure on $\mathbb R$ that places no mass at $-\infty$: only the event $\{M\neq0\}$ contributes.
--
--   **Case 2a** (pp. 146–148). Write $\tilde P(M\in dy) := |y|^\kappa P(M\in dy)$ and
--   $$
--   p := E\mathbf 1_{M>0}|M|^\kappa,\quad q := E\mathbf 1_{M<0}|M|^\kappa,\quad
--   \eta_+(dy) := \tilde P(M>0,\log|M|\in dy)/p,\quad \eta_-(dy) := \tilde P(M<0,\log|M|\in dy)/q .
--   $$
--   The law $\eta$ of Case 2a is given by (9.11),
--   $$
--   \eta = p\eta_+ + \sum_{n=2}^\infty q^2p^{n-2}\,\eta_-^{(2)}*\eta_+^{(n-2)},
--   $$
--   and $\eta_0 := \sum_{n=1}^\infty q\,p^{n-1}\,\eta_-*\eta_+^{(n-1)}$ (p. 148).
--
--   These measures carry the renewal structure behind the implicit renewal theorem: in Case 1 the renewal measure of $\eta$ is $\nu(dt) = \sum_k e^{\kappa t}P(V_k\in dt)$ of (9.7), and in Case 2a the renewal measure of the law (9.11) is the $\nu$ of p. 147.
--
--   **Formalization Note** All measures are built from the law of $M$ alone, so no sequence $M_1, M_2,\dots$ or Markov chain appears in a statement. $\tilde P(M>0,\log|M|\in dy)$ is written as $e^{\kappa y}P(M>0,\log|M|\in dy)$, since $|M|^\kappa = e^{\kappa\log|M|}$ on $M\neq0$. The paper defines the law $\eta$ of Case 2a as the law of $Y_1+\dots+Y_{N_1^{(+)}}$ and derives (9.11); here the right-hand side of (9.11) is the definition (sums reindexed from $0$). The scalars $p, q$ are in $[0,\infty]$; under the hypotheses of the statements they lie in $(0,1)$.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 128 (μ^{(n)}); p. 145 (η, (9.7)); p. 146 (P̃, p, q, η₊, η₋); p. 147, (9.11) and ν; p. 148 (η₀)

import Mathlib

namespace GoldieRenewal.Implicit

open MeasureTheory
open scoped ENNReal

/-- **Convolution powers** `μ^{(n)}` (Goldie 1991, §1, p. 128): `μ^{(0)} = δ₀` (unit mass at `0`)
and `μ^{(n+1)} = μ ∗ μ^{(n)}`, with `∗` the additive convolution of measures on `ℝ`. -/
noncomputable def convPow (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => μ ∗ convPow μ n

/-- **Renewal measure** `Σ_{n≥0} μ^{(n)}` of a law `μ` on `ℝ` (Goldie 1991, (9.7), p. 145, and
p. 147). -/
noncomputable def renewalMeasure (μ : Measure ℝ) : Measure ℝ :=
  Measure.sum (fun n : ℕ => convPow μ n)

/-- **Convolution of a function with a measure**, `f ∗ ρ(t) := ∫_ℝ f(t − u) ρ(du)` (Goldie 1991,
§9, pp. 144–148, e.g. `ğ₁ ∗ ν(t)`).

**Formalization Note** Bochner integral: every statement that uses it also asserts (or assumes)
integrability of `u ↦ f(t − u)` with respect to `ρ`. -/
noncomputable def convFun (f : ℝ → ℝ) (ρ : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ u, f (t - u) ∂ρ

/-- **The tilted law `η`** of Case 1 (Goldie 1991, p. 145): `η(du) := e^{κu} P(Y₁ ∈ du)` with
`Y₁ = log|M|`, a measure on `ℝ` placing no mass at `−∞`. For `M` with law `μ`, this is the
pushforward of `μ` restricted to `{x ≠ 0}` under `x ↦ log|x|`, with density `u ↦ e^{κu}`.

**Formalization Note** Restricting to `{x ≠ 0}` is how "no mass at `−∞`" is encoded; it also keeps
Lean's `Real.log 0 = 0` out. -/
noncomputable def tiltedLaw (κ : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  ((μ.restrict {x | x ≠ 0}).map (fun x => Real.log |x|)).withDensity
    (fun u => ENNReal.ofReal (Real.exp (κ * u)))

/-- `p := P̃(M > 0) = E 1_{M>0}|M|^κ` (Goldie 1991, Case 2a, p. 146), for `M` with law `μ`, as an
element of `[0, ∞]`. -/
noncomputable def pPlus (κ : ℝ) (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Set.Ioi 0, ENNReal.ofReal (|x| ^ κ) ∂μ

/-- `q := P̃(M < 0) = E 1_{M<0}|M|^κ` (Goldie 1991, Case 2a, p. 146), for `M` with law `μ`, as an
element of `[0, ∞]`. -/
noncomputable def qMinus (κ : ℝ) (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Set.Iio 0, ENNReal.ofReal (|x| ^ κ) ∂μ

/-- `η₊(dy) := P̃(M > 0, log|M| ∈ dy)/p` (Goldie 1991, Case 2a, p. 146), where
`P̃(M ∈ dy) := |y|^κ P(M ∈ dy)`. Since `|M|^κ = e^{κ log|M|}`, this is
`p⁻¹ e^{κy} P(M > 0, log|M| ∈ dy)`. -/
noncomputable def etaPlus (κ : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  (pPlus κ μ)⁻¹ •
    ((μ.restrict (Set.Ioi 0)).map (fun x => Real.log |x|)).withDensity
      (fun u => ENNReal.ofReal (Real.exp (κ * u)))

/-- `η₋(dy) := P̃(M < 0, log|M| ∈ dy)/q` (Goldie 1991, Case 2a, p. 146). -/
noncomputable def etaMinus (κ : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  (qMinus κ μ)⁻¹ •
    ((μ.restrict (Set.Iio 0)).map (fun x => Real.log |x|)).withDensity
      (fun u => ENNReal.ofReal (Real.exp (κ * u)))

/-- **The law `η` of Case 2a**, by the right-hand side of (9.11) (Goldie 1991, p. 147):
`η = p η₊ + Σ_{n=2}^∞ q² p^{n−2} η₋^{(2)} ∗ η₊^{(n−2)}`.

**Formalization Note** The paper defines `η` as the law of `Y₁ + ⋯ + Y_{N₁^{(+)}}` and proves (9.11);
here `η` is defined by the right-hand side of (9.11) (the sum is reindexed by `k = n − 2 ≥ 0`), so
no Markov chain needs to be built in a statement. -/
noncomputable def etaCase2 (κ : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  pPlus κ μ • etaPlus κ μ +
    Measure.sum (fun k : ℕ =>
      (qMinus κ μ ^ 2 * pPlus κ μ ^ k) • (convPow (etaMinus κ μ) 2 ∗ convPow (etaPlus κ μ) k))

/-- **The law `η₀`** of Case 2a (Goldie 1991, p. 148): `η₀ = Σ_{n=1}^∞ q p^{n−1} η₋ ∗ η₊^{(n−1)}`
(reindexed by `k = n − 1 ≥ 0`). -/
noncomputable def etaZero (κ : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  Measure.sum (fun k : ℕ =>
    (qMinus κ μ * pPlus κ μ ^ k) • (etaMinus κ μ ∗ convPow (etaPlus κ μ) k))

end GoldieRenewal.Implicit


