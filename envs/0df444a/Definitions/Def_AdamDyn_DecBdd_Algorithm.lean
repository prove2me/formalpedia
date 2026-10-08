-- Prove2me | Definitions.Def_AdamDyn_DecBdd_Algorithm
-- name    : AdamDyn_DecBdd_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:42.389123+00:00
-- url     : https://prove2.me/theorems/e33d2bad-d9b0-4e59-9b6e-ab8ac7dd8d33
-- title:
--   Algorithm 5.1 — Adam with decreasing stepsizes (γ_n, α_n, β_n) and bias correction r_n, r̄_n
-- statement:
--   Fix a dimension $d$, a measurable space $\Xi$, a constant $\varepsilon$ and three real sequences $(\gamma_n)$, $(\alpha_n)$, $(\beta_n)$. Write $\nabla f(x,\xi)\in\mathbb R^d$ for the gradient in $x$ of a function $f:\mathbb R^d\times\Xi\to\mathbb R$; here it is any map $g_f:\mathbb R^d\times\Xi\to\mathbb R^d$ (the gradient oracle). All products, squares, quotients and square roots of vectors below are coordinatewise, and $\nabla f^{\odot 2}$ is the coordinatewise square.
--
--   The **bias-correction weights** are $r_0=0$, $r_n=\alpha_n r_{n-1}+(1-\alpha_n)$ for $n\ge1$, and likewise $\bar r_0=0$, $\bar r_n=\beta_n\bar r_{n-1}+(1-\beta_n)$.
--
--   **Algorithm 5.1** (Adam with decreasing stepsize). Start from $x_0\in\mathbb R^d$, $m_0=0$, $v_0=0$. For $n\ge1$, with the sample $\xi_n$,
--   $$
--   \begin{aligned}
--   m_n &= \alpha_n m_{n-1}+(1-\alpha_n)\nabla f(x_{n-1},\xi_n),\\
--   v_n &= \beta_n v_{n-1}+(1-\beta_n)\nabla f(x_{n-1},\xi_n)^{\odot2},\\
--   \hat m_n &= m_n/r_n,\qquad \hat v_n=v_n/\bar r_n,\\
--   x_n &= x_{n-1}-\gamma_n\,\hat m_n/(\varepsilon+\sqrt{\hat v_n}).
--   \end{aligned}
--   $$
--   The run is defined along a fixed sample path $(\xi_n)_{n\ge1}$ and, for a random sequence $\xi_n(\omega)$, pathwise in $\omega$. The definitions $\hat m_n$, $\hat v_n$ and the preconditioned direction $\hat m_n/(\varepsilon+\sqrt{\hat v_n})$ are also given as functions of the index $n$ and of a state $(x,m,v)$, which is how the proof quantities of §9.2 use them.
--
--   Every statement of the mission refers to these iterates.
--
--   **Formalization Note** The state is a triple in $E\times E\times E$ with $E$ = `EuclideanSpace ℝ (Fin d)`. The run is `adamRun gf γ α β ε x0 ξs : ℕ → E × E × E` (index $0$ is the initialization; `ξs 0` is unused) and the random iterates are `adamIter … ξ n ω := adamRun … (fun k => ξ k ω) n`. Lean's division by $0$ returns $0$; the algorithm divides by $r_n$ and $\bar r_n$, which are positive for all $n\ge1$ exactly when $\alpha_1<1$ and $\beta_1<1$ (with $\alpha_n,\beta_n\in[0,1]$): every theorem of the mission carries these two hypotheses.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 8, Algorithm 5.1

import Mathlib
import Definitions.Def_AdamDyn_ConstStep_adamField
import Definitions.Def_AdamDyn_DecConv_Algorithm

namespace AdamDyn.DecBdd

/-- Bias-corrected first moment `m̂_n = m_n / r_n` (coordinatewise) of the state `z = (x, m, v)`
at index `n`. -/
noncomputable def mHat {d : ℕ} (α : ℕ → ℝ) (n : ℕ) (z : AdamDyn.ConstStep.E d × AdamDyn.ConstStep.E d × AdamDyn.ConstStep.E d) : AdamDyn.ConstStep.E d :=
  WithLp.toLp 2 (fun i => z.2.1 i / AdamDyn.DecConv.biasWeight α n)

/-- Bias-corrected second moment `v̂_n = v_n / r̄_n` (coordinatewise) of the state `z = (x, m, v)`
at index `n`. -/
noncomputable def vHat {d : ℕ} (β : ℕ → ℝ) (n : ℕ) (z : AdamDyn.ConstStep.E d × AdamDyn.ConstStep.E d × AdamDyn.ConstStep.E d) : AdamDyn.ConstStep.E d :=
  WithLp.toLp 2 (fun i => z.2.2 i / AdamDyn.DecConv.biasWeight β n)

/-- The preconditioned direction `m̂_n / (ε + √v̂_n)` (coordinatewise) of the state `z` at
index `n`. -/
noncomputable def adamDir {d : ℕ} (α β : ℕ → ℝ) (ε : ℝ) (n : ℕ) (z : AdamDyn.ConstStep.E d × AdamDyn.ConstStep.E d × AdamDyn.ConstStep.E d) : AdamDyn.ConstStep.E d :=
  WithLp.toLp 2 (fun i => mHat α n z i / (ε + Real.sqrt (vHat β n z i)))

/-- Iteration `n ≥ 1` of Algorithm 5.1 (p. 8), from the state `z = (x_{n-1}, m_{n-1}, v_{n-1})`
with the stochastic gradient `g = ∇f(x_{n-1}, ξ_n)`:
`m_n = α_n m_{n-1} + (1 - α_n) g`, `v_n = β_n v_{n-1} + (1 - β_n) g^{⊙2}`,
`x_n = x_{n-1} - γ_n m̂_n / (ε + √v̂_n)` with `m̂_n = m_n / r_n`, `v̂_n = v_n / r̄_n`. -/
noncomputable def adamStep {d : ℕ} (γ α β : ℕ → ℝ) (ε : ℝ) (n : ℕ) (z : AdamDyn.ConstStep.E d × AdamDyn.ConstStep.E d × AdamDyn.ConstStep.E d)
    (g : AdamDyn.ConstStep.E d) : AdamDyn.ConstStep.E d × AdamDyn.ConstStep.E d × AdamDyn.ConstStep.E d :=
  let m' : AdamDyn.ConstStep.E d := WithLp.toLp 2 (fun i => α n * z.2.1 i + (1 - α n) * g i)
  let v' : AdamDyn.ConstStep.E d := WithLp.toLp 2 (fun i => β n * z.2.2 i + (1 - β n) * g i ^ 2)
  (z.1 - γ n • adamDir α β ε n (z.1, m', v'), m', v')

/-- The run of Algorithm 5.1 along a sample path `ξs : ℕ → Ξ` (`ξs 0` is unused), with the
gradient oracle `gf x ξ = ∇f(x, ξ)`: `z_0 = (x0, 0, 0)` and
`z_n = adamStep n z_{n-1} (gf x_{n-1} ξ_n)`. -/
noncomputable def adamRun {d : ℕ} {Ξ : Type*} (gf : AdamDyn.ConstStep.E d → Ξ → AdamDyn.ConstStep.E d) (γ α β : ℕ → ℝ) (ε : ℝ)
    (x0 : AdamDyn.ConstStep.E d) (ξs : ℕ → Ξ) : ℕ → AdamDyn.ConstStep.E d × AdamDyn.ConstStep.E d × AdamDyn.ConstStep.E d
  | 0 => (x0, 0, 0)
  | n + 1 =>
      adamStep γ α β ε (n + 1) (adamRun gf γ α β ε x0 ξs n)
        (gf (adamRun gf γ α β ε x0 ξs n).1 (ξs (n + 1)))

/-- The random iterates `(x_n, m_n, v_n)(ω)` of Algorithm 5.1 driven by the random sequence
`ξ : ℕ → Ω → Ξ` (`ξ 0` is unused). -/
noncomputable def adamIter {d : ℕ} {Ω Ξ : Type*} (gf : AdamDyn.ConstStep.E d → Ξ → AdamDyn.ConstStep.E d) (γ α β : ℕ → ℝ) (ε : ℝ)
    (x0 : AdamDyn.ConstStep.E d) (ξ : ℕ → Ω → Ξ) (n : ℕ) (ω : Ω) : AdamDyn.ConstStep.E d × AdamDyn.ConstStep.E d × AdamDyn.ConstStep.E d :=
  adamRun gf γ α β ε x0 (fun k => ξ k ω) n

end AdamDyn.DecBdd


