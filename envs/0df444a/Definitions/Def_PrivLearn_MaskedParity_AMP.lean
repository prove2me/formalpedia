-- Prove2me | Definitions.Def_PrivLearn_MaskedParity_AMP
-- name    : PrivLearn_MaskedParity_AMP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:56.310887+00:00
-- url     : https://prove2.me/theorems/834ce707-979a-4f61-89d3-9ce288a46274
-- title:
--   The adaptive SQ learner A_MP for MASKED-PARITY over the uniform distribution
-- statement:
--   The **adaptive SQ learner $\mathcal A_{\mathrm{MP}}$** (p. 28) learns MASKED-PARITY in two rounds over the uniform distribution on $D=\{0,1\}^d\times\{0,1\}^{\log d}\times\{0,1\}$.
--
--   1. For $j=1,\dots,d$ (in parallel) it asks the query $g_j(x,i,b,y)=(i=j)\wedge(b=1)\wedge(y=-1)$, with values in $\{0,1\}$, with tolerance $\tau=\frac1{4d+1}$, and sets $\hat r_j=1$ if $\mathit{answer}_j>\frac1{4d}$ and $\hat r_j=0$ otherwise.
--   2. With $\hat r=\hat r_1\dots\hat r_d$ it asks the query $g_{d+1}(x,i,b,y)=(b=0)\wedge\bigl(y\neq(-1)^{\hat r\odot x}\bigr)$ with tolerance $\frac15$, sets $\hat a=1$ if $\mathit{answer}_{d+1}>\frac14$ and $\hat a=0$ otherwise, and outputs $c_{\hat r,\hat a}$.
--
--   It is the witness for part (1) of Theorem 5.16: the second-round query depends on the first-round answers, which is what a nonadaptive learner cannot do.
--
--   **Formalization Note.** $\mathcal A_{\mathrm{MP}}$ is a two-round learner with $d$ first-round queries and one second-round query. Indices $j$ run over `Fin d` (0-based). The thresholds are strict (`>`), as printed. Queries take the value $1$ when the printed condition holds and $0$ otherwise.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 28, Adaptive SQ Learner A_MP for MASKED-PARITY over the Uniform Distribution

import Mathlib
import Definitions.Def_PrivLearn_MaskedParity_Model

namespace PrivLearn.MaskedParity

/-- p. 28, step 1(a) of `A_MP`: the first-round query `g_j(x, i, b, y) = (i = j) ∧ (b = 1) ∧ (y = −1)`,
with values in `{0, 1}`. -/
noncomputable def gRound1 {d : ℕ} (j : Fin d) : Dom d → ℝ → ℝ := fun u y =>
  if u.2.1 = j ∧ u.2.2 = 1 ∧ y = -1 then 1 else 0

/-- p. 28, step 1(b) of `A_MP`: `r̂_j = 1` if `answer_j > 1/(4d)` and `0` otherwise. -/
noncomputable def rhat {d : ℕ} (ans : Fin d → ℝ) : Fin d → ZMod 2 := fun j =>
  if ans j > 1 / (4 * (d : ℝ)) then 1 else 0

/-- p. 28, step 2(b) of `A_MP`: the second-round query
`g_{d+1}(x, i, b, y) = (b = 0) ∧ (y ≠ (−1)^{r̂⊙x})`, with values in `{0, 1}`. -/
noncomputable def gRound2 {d : ℕ} (rh : Fin d → ZMod 2) : Dom d → ℝ → ℝ := fun u y =>
  if u.2.2 = 0 ∧ y ≠ (-1 : ℝ) ^ ((rh ⬝ᵥ u.1).val) then 1 else 0

/-- p. 28, step 2(c) of `A_MP`: `â = 1` if `answer_{d+1} > 1/4` and `0` otherwise. -/
noncomputable def ahat (v : ℝ) : ZMod 2 :=
  if v > 1 / 4 then 1 else 0

/-- p. 28: the adaptive SQ learner `A_MP` for MASKED-PARITY over the uniform distribution, as a
two-round learner: `d` first-round queries `g_j` with tolerance `1/(4d+1)`, one second-round query
`g_{d+1}` (built from `r̂`) with tolerance `1/5`, and output `c_{r̂,â}`. -/
noncomputable def AMP (d : ℕ) : TwoRoundSQLearner (Dom d) d 1 where
  q₁ := fun j => gRound1 j
  τ₁ := fun _ => 1 / (4 * (d : ℝ) + 1)
  q₂ := fun ans _ => gRound2 (rhat ans)
  τ₂ := fun _ _ => 1 / 5
  out := fun ans₁ ans₂ => cMP (rhat ans₁) (ahat (ans₂ 0))

end PrivLearn.MaskedParity


