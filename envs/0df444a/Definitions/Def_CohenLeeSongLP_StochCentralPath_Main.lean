-- Prove2me | Definitions.Def_CohenLeeSongLP_StochCentralPath_Main
-- name    : CohenLeeSongLP_StochCentralPath_Main
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:26:26.828599+00:00
-- url     : https://prove2.me/theorems/d17d8b5e-5dba-42c8-b9ef-6cc9f5037b76
-- title:
--   Main (Algorithm 2): parameters, the direction δ_μ of line 11, and the law of one iteration
-- statement:
--   This module formalizes the iteration of the main algorithm Main (Algorithm 2, p. 3:10) on a program with $n$ variables and constraint matrix $A\in\mathbb R^{d\times n}$.
--
--   1. **Parameters (lines 2–3).** $\epsilon=\frac{1}{40000\log n}$, $\epsilon_{\mathrm{mp}}=\frac1{40000}$, $k=\frac{1000\epsilon\sqrt n\log^2 n}{\epsilon_{\mathrm{mp}}}$ and $\lambda=40\log n$.
--   2. **Path parameter (lines 7, 9).** $t_0=1$ and $t^{\mathrm{new}}=(1-\frac{\epsilon}{3\sqrt n})t$, so after $j$ iterations $t_j=(1-\frac{\epsilon}{3\sqrt n})^j$.
--   3. **Direction (line 11).** With $\mu=xs$,
--   $$\delta_\mu=\Big(\frac{t^{\mathrm{new}}}{t}-1\Big)xs-\frac{\epsilon}{2}\,t^{\mathrm{new}}\,\frac{\nabla\Phi_\lambda(\mu/t-1)}{\|\nabla\Phi_\lambda(\mu/t-1)\|_2},$$
--   where the second term is $0$ when $\nabla\Phi_\lambda(\mu/t-1)=0$.
--   4. **One iteration (lines 9–17).** The state after an iteration is $(x,s,\mathrm{flag})$, the flag recording whether ClassicalStep was used. Given the history $h=(\text{state}_0,\dots,\text{state}_j)$ with current iterate $(x,s)$, let $\widetilde v=U_j(h)$ (the data structure's output) and draw $\widetilde\delta_\mu$ from the law of StochasticStep (the product law conditioned on the success event of the resampling loop) with direction $\delta_\mu$ of line 11 at $t=t_j$, $t^{\mathrm{new}}=t_{j+1}$. Set $(x^{\mathrm{new}},s^{\mathrm{new}})=(x+\widetilde\delta_x,s+\widetilde\delta_s)$. If $\Phi_\lambda(\mu^{\mathrm{new}}/t^{\mathrm{new}}-1)>n^3$ (line 13), the new state is $(C_j(h),\mathrm{true})$, where $C_j(h)$ is the output of $\mathrm{ClassicalStep}(x,s,t^{\mathrm{new}})$ (line 14); otherwise it is $(x^{\mathrm{new}},s^{\mathrm{new}},\mathrm{false})$. If the success event has probability $0$ the law is the Dirac mass at $(x,s,\mathrm{false})$; Lemma 4.14 shows that this fallback is almost surely never used.
--
--   The data structure mp (Algorithm 3) is deterministic given the sequence of its inputs, and ClassicalStep is called on the *old* iterate, so both are modelled as arbitrary functions $U_j$, $C_j$ of the history; their properties are hypotheses of the theorems.
--
--   **Formalization Note** The while-guard $t>\delta^2/(32n^3)$ (line 8) only fixes how many iterations run, and the data-structure restart (line 15) is covered by letting $U_j$ depend on the whole history; neither is modelled. $n$ is the number of variables of the program the loop runs on (the modified program of Lemma A.6), and the parameters are computed from that same $n$. $\log$ is the natural logarithm.
-- source:
--   Cohen, Lee and Song, Solving Linear Programs in the Current Matrix Multiplication Time, J. ACM 68(1), Article 3 (2021), p. 3:10, Algorithm 2 (lines 2–3, 7–17)

import Mathlib
import Definitions.Def_CohenLeeSongLP_StochCentralPath_Basic
import Definitions.Def_CohenLeeSongLP_StochCentralPath_StochasticStep

open MeasureTheory ProbabilityTheory

namespace CohenLeeSongLP.StochCentralPath

/-- Line 2 of Algorithm 2: `ε = 1/(40000 log n)` (natural logarithm). -/
noncomputable def eps (n : ℕ) : ℝ := 1 / (40000 * Real.log n)

/-- Line 2 of Algorithm 2: `ε_mp = 1/40000`. -/
noncomputable def epsMp : ℝ := 1 / 40000

/-- Line 2 of Algorithm 2: the sampling parameter `k = 1000 ε √n log² n / ε_mp`. -/
noncomputable def kSampMain (n : ℕ) : ℝ :=
  1000 * eps n * Real.sqrt n * Real.log n ^ 2 / epsMp

/-- Line 3 of Algorithm 2: `λ = 40 log n`. -/
noncomputable def lam (n : ℕ) : ℝ := 40 * Real.log n

/-- The path parameter after `j` iterations of Main: `t_0 = 1` (line 7) and
`t^new = (1 − ε/(3√n)) t` (line 9), so `t_j = (1 − ε/(3√n))^j`. -/
noncomputable def tSeq (n j : ℕ) : ℝ := (1 - eps n / (3 * Real.sqrt n)) ^ j

/-- Line 11 of Algorithm 2: with `μ = xs`,
`δ_μ = (t^new/t − 1) xs − (ε/2) t^new ∇Φ_λ(μ/t − 1)/‖∇Φ_λ(μ/t − 1)‖₂`.
When `∇Φ_λ(μ/t − 1) = 0` the second term is `0` (Lean's `a / 0 = 0`). -/
noncomputable def direction {n : ℕ} (lam ε t tnew : ℝ) (x s : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (tnew / t - 1) * (x i * s i) -
    ε / 2 * tnew * (potentialGrad lam (fun l => x l * s l / t - 1) i /
      norm2 (potentialGrad lam (fun l => x l * s l / t - 1)))

/-- The state of Main after an iteration: `(x, s, flag)`, where `flag` records whether
ClassicalStep replaced the stochastic step in the iteration that produced this state. -/
abbrev State (n : ℕ) := (Fin n → ℝ) × (Fin n → ℝ) × Bool

/-- The current (last) state of a history `(state_0, …, state_j)`. -/
def current {n j : ℕ} (h : (i : Finset.Iic j) → State n) : State n :=
  h ⟨j, Finset.mem_Iic.2 le_rfl⟩

open Classical in
/-- The law of the state after iteration `j` of Main (lines 9–17 of Algorithm 2), given the
history `h = (state_0, …, state_j)`, with Main's parameters `ε, ε_mp, k, λ`.
`U j h` is the output `ṽ` of `mp.Update(x/s)` and `C j h` the output of
`ClassicalStep(x, s, t^new)`, both functions of the history only.
StochasticStep draws `δ̃_μ` from `stepLaw` (the product law conditioned on the success event of
the resampling loop) and returns `(x + δ̃_x, s + δ̃_s)`; if `Φ_λ(μ^new/t^new − 1) > n³`, the
output is replaced by `C j h` and the flag set. If the success event has probability `0`
(the loop would never stop), the law falls back to the Dirac mass at `(x, s, false)`. -/
noncomputable def mainStepLaw {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ)
    (U : (j : ℕ) → ((i : Finset.Iic j) → State n) → (Fin n → ℝ))
    (C : (j : ℕ) → ((i : Finset.Iic j) → State n) → (Fin n → ℝ) × (Fin n → ℝ))
    (j : ℕ) (h : (i : Finset.Iic j) → State n) : Measure (State n) :=
  let x := (current h).1
  let s := (current h).2.1
  let tnew := tSeq n (j + 1)
  let δμ := direction (lam n) (eps n) (tSeq n j) tnew x s
  let v := U j h
  if sampleLaw (kSampMain n) δμ (successEvent A x s v) = 0 then
    Measure.dirac (x, s, false)
  else
    (stepLaw A x s v (kSampMain n) δμ).map (fun δ =>
      if (n : ℝ) ^ 3 < potential (lam n) (fun i => muNew A x s v δ i / tnew - 1) then
        ((C j h).1, (C j h).2, true)
      else
        ((fun i => x i + stepX A x s v δ i), (fun i => s i + stepS A x s v δ i), false))

end CohenLeeSongLP.StochCentralPath


