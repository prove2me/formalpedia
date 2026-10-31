-- Prove2me | Definitions.Def_EllsbergLearning_CriticalValues
-- name    : EllsbergLearning_CriticalValues
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:49.347856+00:00
-- url     : https://prove2.me/theorems/044b660d-7d9a-4770-8bd1-90165c69fa5f
-- title:
--   The functions $l,\tilde l$, the critical-value equations (30)–(32) and the cut-off $u_2^{**}$ of (34) (corrected)
-- statement:
--   For $r\in(0,1)$ let
--   $$l(r)=2\log\frac{r}{1-r}-\frac1r+\frac{1}{1-r},\qquad \tilde l(r)=\log\frac{r}{1-r}+\frac{r}{1-r}.$$
--   With $\hat c$ the normalized cost and $(\underline\pi,\overline\pi)$ the indifference probabilities, the critical values are solutions in $(0,1)^2$ of
--   $$\text{(30)}\quad l(r^R_2)-l(r^R_1)=\frac{u_{11}-u_{10}}{\hat c},\quad \tilde l(r^R_2)-\tilde l(r^R_1)=\frac{u_2-u_{10}}{\hat c},$$
--   $$\text{(31)}\quad l(r^l_2)-l(r^l_1)=-\frac{u_{00}-u_{01}}{\hat c},\quad \tilde l(r^l_2)-\tilde l(r^l_1)=\frac{u_2-u_{00}}{\hat c},$$
--   $$\text{(32)}\quad l(r^R)-l(\underline\pi)=\frac{u_{11}-u_{10}}{\hat c},\quad l(r^l)-l(\overline\pi)=-\frac{u_{00}-u_{01}}{\hat c},$$
--   and the cut-off is
--   $$u_2^{**}=\frac{\hat c}{2}\Big[\frac{1}{r^l(1-r^l)}-\frac{1}{\overline\pi(1-\overline\pi)}\Big]+\frac{u_{00}+u_{01}}{2}.$$
--
--   They describe the stopping boundaries of the optimal policy (Theorem 4.2(a)) and the cut-off between its two cases.
--
--   **Formalization Note** (34) is printed with $\frac{u_{00}-u_{01}}{2}$; the corrected $\frac{u_{00}+u_{01}}{2}$ is the value $g_1(\overline\pi;C_1,C_2)=v(t,\tilde z_t)$ that the paper states $u_2^{**}$ equals (p.26). With the printed value, (37) fails: in the Ellsberg instance $\alpha=1/8$, $c=0.01$, $\sigma=1$, $\epsilon=0.04$ the printed $u_2^{**}\approx0.126<u_2=\tfrac12$ while $r_1^l=\hat r\approx0.5244>\overline\pi=0.52$. Each solution predicate requires its unknowns in $(0,1)$.
-- source:
--   Epstein & Ji, Optimal Learning under Robustness and Time-Consistency, arXiv:1708.01890v2, §4, (30)–(32), (34), p.20; (21), p.13

import Definitions.Def_EllsbergLearning_Params

open Set

noncomputable section

namespace EllsbergLearning

/-- `l(r) = 2 log(r/(1 − r)) − 1/r + 1/(1 − r)` for `r ∈ (0, 1)` (arXiv:1708.01890v2, (21),
p.13, and §4, p.20). Every statement using it restricts `r` to `(0, 1)`. -/
def ell (r : ℝ) : ℝ := 2 * Real.log (r / (1 - r)) - 1 / r + 1 / (1 - r)

/-- `l̃(r) = log(r/(1 − r)) + r/(1 − r)` for `r ∈ (0, 1)` (§4, p.20). -/
def ellTilde (r : ℝ) : ℝ := Real.log (r / (1 - r)) + r / (1 - r)

namespace Params

variable (p : Params)

/-- `(r₁ᴿ, r₂ᴿ)` solves (30) (arXiv:1708.01890v2, p.20) in `(0, 1)²`:
`l(r₂ᴿ) − l(r₁ᴿ) = (u₁₁ − u₁₀)/ĉ` and `l̃(r₂ᴿ) − l̃(r₁ᴿ) = (u₂ − u₁₀)/ĉ`. -/
def Solves30 (r1 r2 : ℝ) : Prop :=
  r1 ∈ Ioo (0 : ℝ) 1 ∧ r2 ∈ Ioo (0 : ℝ) 1 ∧
    ell r2 - ell r1 = (p.u 1 1 - p.u 1 0) / p.chat ∧
    ellTilde r2 - ellTilde r1 = (p.u₂ - p.u 1 0) / p.chat

/-- `(r₁ˡ, r₂ˡ)` solves (31) (p.20) in `(0, 1)²`: `l(r₂ˡ) − l(r₁ˡ) = −(u₀₀ − u₀₁)/ĉ` and
`l̃(r₂ˡ) − l̃(r₁ˡ) = (u₂ − u₀₀)/ĉ`. -/
def Solves31 (r1 r2 : ℝ) : Prop :=
  r1 ∈ Ioo (0 : ℝ) 1 ∧ r2 ∈ Ioo (0 : ℝ) 1 ∧
    ell r2 - ell r1 = -(p.u 0 0 - p.u 0 1) / p.chat ∧
    ellTilde r2 - ellTilde r1 = (p.u₂ - p.u 0 0) / p.chat

/-- `(rᴿ, rˡ)` solves (32) (p.20) in `(0, 1)²`, for the indifference probabilities `π̲` (`πL`)
and `π̄` (`πU`): `l(rᴿ) − l(π̲) = (u₁₁ − u₁₀)/ĉ` and `l(rˡ) − l(π̄) = −(u₀₀ − u₀₁)/ĉ`. -/
def Solves32 (πL πU rR rl : ℝ) : Prop :=
  rR ∈ Ioo (0 : ℝ) 1 ∧ rl ∈ Ioo (0 : ℝ) 1 ∧
    ell rR - ell πL = (p.u 1 1 - p.u 1 0) / p.chat ∧
    ell rl - ell πU = -(p.u 0 0 - p.u 0 1) / p.chat

/-- The cut-off `u₂**` of (34), arXiv:1708.01890v2, p.20, **corrected**:
`u₂** = (ĉ/2)[1/(rˡ(1 − rˡ)) − 1/(π̄(1 − π̄))] + (u₀₀ + u₀₁)/2`.

**Formalization Note (correction).** The page prints the last term as `(u₀₀ − u₀₁)/2`. The paper
itself requires `u₂** = g₁(π̄; C₁, C₂) = v(t, z̃_t)` (p.26), and `g₁(π̄; C₁, C₂)` computed from (43)
and (32) equals the expression above; the printed one is smaller by `u₀₁`. With the printed value,
(37) fails: in the Ellsberg instance `α = 1/8`, `c = 0.01`, `σ = 1`, `ϵ = 0.04` (u₀₁ = 3/8) the
printed `u₂**` is `0.126 < u₂ = 1/2`, while `r₁ˡ = r̂ ≈ 0.5244 > π̄ = 0.52`. The corrected value
`≈ 0.5011` agrees with `v₀` of (26). -/
def u2StarStar (πU rl : ℝ) : ℝ :=
  p.chat / 2 * (1 / (rl * (1 - rl)) - 1 / (πU * (1 - πU))) + (p.u 0 0 + p.u 0 1) / 2

end Params

end EllsbergLearning


