-- Prove2me | Definitions.Def_ParallelLpSCO_EpochDA_NextLambda
-- name    : ParallelLpSCO_EpochDA_NextLambda
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T07:05:32.12227+00:00
-- url     : https://prove2.me/theorems/c0078365-46fc-4de4-8b00-aedae32ddf95
-- title:
--   Algorithm 7 (NextLambda) and its number of BROO calls
-- statement:
--   **Algorithm 7 (NextLambda, p. 32)**, input $x,v\in\mathbb R^d$, $A\ge0$, $\lambda_{\min}$, $\lambda_{\max}$, $G$, $R$, $r$ and a BROO $O$ (Definition 5).
--   - For $\lambda'>0$, $a_{\lambda'}>0$ solves $(A+a)^{p-1}=2^{p-1}\lambda'a^p$, and $y_{\lambda'}=\frac{A}{A+a_{\lambda'}}x+\frac{a_{\lambda'}}{A+a_{\lambda'}}v$ (`yLam`).
--   - $\Delta(\lambda)=\|O_{\lambda,r/17}(y_\lambda)-y_\lambda\|_p$ (`nlDelta`).
--   - Starting from $\lambda=\lambda_{\max}$, halve $\lambda$ while $\lambda\ge\lambda_{\min}$ and $\Delta(\lambda)\le13r/16$.
--   - If $\lambda<\lambda_{\min}$, return $2\lambda$.
--   - Otherwise set $\lambda_u=2\lambda$, $\lambda_\ell=\lambda$, $\lambda_m=\sqrt{\lambda_u\lambda_\ell}$; return $\lambda_\ell$ if $\Delta(\lambda_\ell)\le15r/16$.
--   - Otherwise, while $\Delta(\lambda_m)\notin[13r/16,15r/16]$ and $\log\frac{\lambda_u}{\lambda_\ell}>\frac{r}{8(R+\frac1{p-1}(G/\lambda_\ell)^{1/(p-1)})}$: set $\lambda_u=\lambda_m$ if $\Delta(\lambda_m)<13r/16$, else $\lambda_\ell=\lambda_m$; then $\lambda_m=\sqrt{\lambda_u\lambda_\ell}$.
--   - Return $\lambda_m$.
--
--   `nextLambda` is the returned value. `nextLambdaCalls` counts one BROO call per evaluation of $\Delta$ in the pseudocode: every check of line 5 that reaches $\Delta$, line 10, and every check of line 12 and pass of line 13.
--
--   **Formalization Note.** The numbers of halvings and bisections are `sInf`s of the stopping sets; both loops terminate, so the sets are nonempty. The root $a_\lambda$ is the machine's `posRoot` (unique for $\lambda>0$, $A\ge0$).
-- source:
--   Nie, Shyam, Bullins, Bias-Reduced and Parallel Heavy-Tailed Stochastic Convex Optimization in ℓp Geometries, STOC 2027 submission (manuscript, sha256 fe68639b…), p. 32 (Algorithm 7)

import Mathlib
import Definitions.Def_ParallelLpSCO_EpochDA_Basics
import Definitions.Def_ParallelLpSCO_EpochDA_Machine

/-!
# Algorithm 7 (NextLambda)

Nie, Shyam, Bullins, *Bias-Reduced and Parallel Heavy-Tailed Stochastic Convex Optimization in
ℓp Geometries*, STOC 2027 submission (manuscript, sha256 fe68639b…), Algorithm 7 p. 32.

Input `x, v ∈ ℝ^d`, `A ≥ 0`, `λ_min`, `λ_max`, `G`, `R`, `r`, and a BROO `O` (`O λ ρ y`,
Definition 5). For `λ′ > 0`, `a_{λ′} > 0` solves `(A + a)^{p−1} = 2^{p−1} λ′ a^p` and
`y_{λ′} = (A/(A + a_{λ′})) x + (a_{λ′}/(A + a_{λ′})) v`; `∆(λ) = ‖O_{λ,r/17}(y_λ) − y_λ‖_p`.
Lines 4–6 halve `λ` from `λ_max` while `λ ≥ λ_min` and `∆(λ) ≤ 13r/16`; line 7 returns `2λ` if
`λ < λ_min`; lines 9–11 set `λ_u = 2λ`, `λ_ℓ = λ`, `λ_m = √(λ_u λ_ℓ)` and return `λ_ℓ` if
`∆(λ_ℓ) ≤ 15r/16`; lines 12–17 bisect geometrically while `∆(λ_m) ∉ [13r/16, 15r/16]` and
`log(λ_u/λ_ℓ) > r / (8(R + (1/(p−1))(G/λ_ℓ)^{1/(p−1)}))`; line 18 returns `λ_m`.
-/

namespace ParallelLpSCO.EpochDA

/-- `y_λ = (A/(A + a_λ)) x + (a_λ/(A + a_λ)) v` with `a_λ > 0` solving
`(A + a)^{p−1} = 2^{p−1} λ a^p` (line 2). -/
noncomputable def yLam {d : ℕ} (p A lam : ℝ) (x v : Vec d) : Vec d :=
  let a := posRoot p A ((2 : ℝ) ^ (p - 1) * lam)
  (A / (A + a)) • x + (a / (A + a)) • v

/-- `∆(λ) = ‖O_{λ,r/17}(y_λ) − y_λ‖_p` (line 3). -/
noncomputable def nlDelta {d : ℕ} (p r A : ℝ) (x v : Vec d) (O : ℝ → ℝ → Vec d → Vec d)
    (lam : ℝ) : ℝ :=
  lpNorm p (O lam (r / 17) (yLam p A lam x v) - yLam p A lam x v)

/-- The number of halvings performed by lines 5–6. -/
noncomputable def nlHalvings {d : ℕ} (p r A lamMin lamMax : ℝ) (x v : Vec d)
    (O : ℝ → ℝ → Vec d → Vec d) : ℕ :=
  sInf {n : ℕ | ¬ (lamMin ≤ lamMax / 2 ^ n ∧ nlDelta p r A x v O (lamMax / 2 ^ n) ≤ 13 * r / 16)}

/-- The bracket `(λ_u, λ_ℓ)` after `n` passes of lines 13–16, started from `(lu, ll)`. -/
noncomputable def nlBracket {d : ℕ} (p r A : ℝ) (x v : Vec d) (O : ℝ → ℝ → Vec d → Vec d)
    (lu ll : ℝ) : ℕ → ℝ × ℝ
  | 0 => (lu, ll)
  | n + 1 =>
      let b := nlBracket p r A x v O lu ll n
      let m := Real.sqrt (b.1 * b.2)
      if nlDelta p r A x v O m < 13 * r / 16 then (m, b.2) else (b.1, m)

/-- The loop condition of line 12 at the bracket `b = (λ_u, λ_ℓ)`. -/
def nlContinue {d : ℕ} (p r A G R : ℝ) (x v : Vec d) (O : ℝ → ℝ → Vec d → Vec d)
    (b : ℝ × ℝ) : Prop :=
  ¬ (13 * r / 16 ≤ nlDelta p r A x v O (Real.sqrt (b.1 * b.2)) ∧
      nlDelta p r A x v O (Real.sqrt (b.1 * b.2)) ≤ 15 * r / 16) ∧
    r / (8 * (R + 1 / (p - 1) * (G / b.2) ^ (1 / (p - 1)))) < Real.log (b.1 / b.2)

/-- The number of passes of the loop of lines 12–17, started from `(lu, ll)`. -/
noncomputable def nlBisections {d : ℕ} (p r A G R : ℝ) (x v : Vec d)
    (O : ℝ → ℝ → Vec d → Vec d) (lu ll : ℝ) : ℕ :=
  sInf {n : ℕ | ¬ nlContinue p r A G R x v O (nlBracket p r A x v O lu ll n)}

/-- The value returned by Algorithm 7. -/
noncomputable def nextLambda {d : ℕ} (p r A G R lamMin lamMax : ℝ) (x v : Vec d)
    (O : ℝ → ℝ → Vec d → Vec d) : ℝ :=
  let lh := lamMax / 2 ^ nlHalvings p r A lamMin lamMax x v O
  if lh < lamMin then 2 * lh
  else if nlDelta p r A x v O lh ≤ 15 * r / 16 then lh
  else
    let b := nlBracket p r A x v O (2 * lh) lh (nlBisections p r A G R x v O (2 * lh) lh)
    Real.sqrt (b.1 * b.2)

/-- The number of BROO calls of Algorithm 7, one per evaluation of `∆` in its pseudocode: one per
check of line 5 that reaches `∆` (all checks with `λ ≥ λ_min`), one in line 10, and in the
bisection one per check of line 12 and one per pass of line 13. -/
noncomputable def nextLambdaCalls {d : ℕ} (p r A G R lamMin lamMax : ℝ) (x v : Vec d)
    (O : ℝ → ℝ → Vec d → Vec d) : ℕ :=
  let H := nlHalvings p r A lamMin lamMax x v O
  let lh := lamMax / 2 ^ H
  let N := nlBisections p r A G R x v O (2 * lh) lh
  H + (if lamMin ≤ lh then 1 else 0) +
    (if lh < lamMin then 0
     else 1 + (if nlDelta p r A x v O lh ≤ 15 * r / 16 then 0 else (N + 1) + N))

end ParallelLpSCO.EpochDA


