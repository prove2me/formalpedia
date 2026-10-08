-- Prove2me | Definitions.Def_FracPackCover_General_Improve
-- name    : FracPackCover_General_Improve
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:19.84105+00:00
-- url     : https://prove2.me/theorems/d4584bdf-62f0-45eb-9c0d-2327a59b49c3
-- title:
--   Procedure IMPROVE-GENERAL (Figure 4) with λ₀/2-corrected parameters and its oracle-call count
-- statement:
--   **Procedure IMPROVE-GENERAL** (Figure 4, p. 25) takes a point $x_0 \in P$ and sets $\lambda_0 = \lambda(x_0)$. It then fixes the parameters
--   $$\alpha = 4\lambda_0^{-1}\ln\!\big(12 m \rho \lambda_0^{-1}\big), \qquad \sigma = \frac{\lambda_0}{48\,\alpha\,\rho^2},$$
--   and repeats the following while $\lambda(x) \ge \lambda_0/2$ and $x$ and its dual solution $y$ do not satisfy $(\mathcal G2)$: set $y_i = \frac{1}{d_i} e^{\alpha(a_i x - b_i)/d_i}$; find, with subroutine (10), a minimum-cost point $\tilde x \in P$ for costs $c = y^t A$; update $x \leftarrow (1-\sigma)x + \sigma \tilde x$. It returns $x$.
--
--   **Correction of Figure 4.** Figure 4 prints $\alpha = 4\lambda_0^{-1}\ln(6m\rho\lambda_0^{-1})$ and $\sigma = \lambda_0/(24\alpha\rho^2)$. Lemma 4.2 needs $\alpha \ge 2\lambda^{-1}\ln(6m\rho\lambda^{-1})$ and Lemma 4.3 needs $\sigma \le \lambda/(24\alpha\rho^2)$ for the *current* $\lambda$, and the loop runs for every $\lambda \ge \lambda_0/2$; the printed values do not meet these hypotheses when $\lambda_0/2 \le \lambda < \lambda_0$. The mission uses the printed formulas with $\lambda_0/2$ in place of $\lambda_0$, which meet both hypotheses for every $\lambda \in [\lambda_0/2, \rho]$ and leave the paper's $O(\cdot)$ bounds unchanged.
--
--   **Cost model.** Each evaluation of the loop test that reaches the $(\mathcal G2)$ test needs $C_{\mathcal G}(y)$ and therefore makes one oracle call; when the test holds, the loop body reuses that $\tilde x$. A test that fails because $\lambda(x) < \lambda_0/2$ makes no call. The run reports its final point, the number of oracle calls, and which exit it took: $\lambda(x) < \lambda_0/2$, $(\mathcal G2)$ satisfied, or out of fuel.
--
--   **Formalization Note.** Lean functions must terminate, so the loop is run with a fuel bound on the number of loop tests; the theorems assert that the loop test fails before the fuel runs out, they do not assume it. The oracle is an arbitrary function; the theorems assume it is a minimizing oracle for $P$ and $A$. For $\lambda_0 \le 0$ the parameters are meaningless and no theorem uses them in that case.
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Tech. Rep. 999 (1992), p. 25, Figure 4 (parameters corrected from λ₀ to λ₀/2, see pp. 26–27, Lemmas 4.2–4.3)

import Mathlib
import Definitions.Def_FracPackCover_General_Basic

namespace FracPackCover.General

/-!
# Procedure IMPROVE-GENERAL (Figure 4, p. 25), with corrected step parameters

Figure 4 prints `α = 4λ₀⁻¹ ln(6mρλ₀⁻¹)` and `σ = λ₀/(24αρ²)`. These do not meet the hypotheses
of Lemmas 4.2 and 4.3 (which need `α ≥ 2λ⁻¹ ln(6mρλ⁻¹)` and `σ ≤ λ/(24αρ²)` for the *current* `λ`)
when `λ₀/2 ≤ λ < λ₀`, although the loop runs for all `λ ≥ λ₀/2`. This development uses the
paper's formulas with `λ₀/2` in place of `λ₀`:
`α = 4λ₀⁻¹ ln(12mρλ₀⁻¹)` and `σ = λ₀/(48αρ²)`.
-/

/-- Corrected step parameter `α = 4λ₀⁻¹ ln(12 m ρ λ₀⁻¹)` (Figure 4 prints `6` for `12`). -/
noncomputable def alphaGen (m : ℕ) (ρ lam0 : ℝ) : ℝ :=
  4 / lam0 * Real.log (12 * m * ρ / lam0)

/-- Corrected step size `σ = λ₀/(48 α ρ²)` (Figure 4 prints `24` for `48`). -/
noncomputable def sigmaGen (m : ℕ) (ρ lam0 : ℝ) : ℝ :=
  lam0 / (48 * alphaGen m ρ lam0 * ρ ^ 2)

/-- How a run of IMPROVE-GENERAL ended. -/
inductive ImproveExit
  /-- the loop test failed because `max_i (a_i x − b_i)/d_i < λ₀/2` -/
  | lambdaHalved
  /-- the loop test failed because `x` and `y` satisfy (𝒢2) (while `λ ≥ λ₀/2`) -/
  | relaxedOpt
  /-- the fuel bound was reached with the loop test still true -/
  | outOfFuel
  deriving DecidableEq

/-- Output of a (fuelled) run: the returned point, the number of oracle calls made, how it ended. -/
structure ImproveResult (n : ℕ) where
  point : Fin n → ℝ
  calls : ℕ
  exit : ImproveExit

open Classical in
/-- The while-loop of Figure 4 with fixed `λ₀, α, σ`, run for at most `fuel` evaluations of the
loop test. An evaluation of the test that reaches the (𝒢2) conjunct computes `y` and calls the
oracle once (`x̃ = orc y`, which gives `C_𝒢(y) = y^t(Ax̃ − b)`); if the test holds, the body reuses
that `x̃` for the update `x ← (1 − σ)x + σx̃`. A test that fails at `λ(x) < λ₀/2` makes no call. -/
noncomputable def improveLoop {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b d : Fin m → ℝ) (orc : (Fin m → ℝ) → (Fin n → ℝ)) (lam0 α σ : ℝ) :
    ℕ → (Fin n → ℝ) → ImproveResult n
  | 0, x => ⟨x, 0, .outOfFuel⟩
  | k + 1, x =>
    if lam A b d x < lam0 / 2 then ⟨x, 0, .lambdaHalved⟩
    else
      let y := dualVec A b d α x
      let xt := orc y
      if G2 A b d x (lam A b d x) y (lagr A b y xt) then ⟨x, 1, .relaxedOpt⟩
      else
        let r := improveLoop A b d orc lam0 α σ k ((1 - σ) • x + σ • xt)
        ⟨r.point, r.calls + 1, r.exit⟩

/-- IMPROVE-GENERAL(x₀) with fuel: `λ₀ = λ(x₀)`, `α = alphaGen m ρ λ₀`, `σ = sigmaGen m ρ λ₀`
(the corrected parameters), then the loop of Figure 4. -/
noncomputable def improveGeneral {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b d : Fin m → ℝ) (ρ : ℝ) (orc : (Fin m → ℝ) → (Fin n → ℝ)) (fuel : ℕ)
    (x0 : Fin n → ℝ) : ImproveResult n :=
  improveLoop A b d orc (lam A b d x0) (alphaGen m ρ (lam A b d x0))
    (sigmaGen m ρ (lam A b d x0)) fuel x0

end FracPackCover.General


