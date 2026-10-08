-- Prove2me | Definitions.Def_AdamDyn_DecBdd_ProofQuantities
-- name    : AdamDyn_DecBdd_ProofQuantities
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:32.18724+00:00
-- url     : https://prove2.me/theorems/d1ab569c-8d01-403f-9045-bd14ca1695f4
-- title:
--   The quantities a_n, u_n, P_n, c_{n+1}, V_n of §9.2 and the one-step conditional expectation
-- statement:
--   These are the auxiliary sequences of the proof of Theorem 5.4 (§9.2, pp. 26–27), for the iterates of Algorithm 5.1 with bias-correction weights $r_n,\bar r_n$:
--   $$a_n:=\frac{1-\alpha_{n+1}}{\gamma_n},\qquad u_n:=1-\frac{a_{n+1}}{a_n},\qquad P_n:=\frac1{2a_nr_n}\Big\langle m_n^{\odot2},\frac1{\varepsilon+\sqrt{\hat v_n}}\Big\rangle,$$
--   $$c_{n+1}:=\frac{1-\beta_{n+1}}{\sqrt{\beta_{n+1}}}\Big(\frac1{1+\sqrt{\beta_{n+1}}}+\frac{1-\bar r_n}{2\bar r_n}\Big),$$
--   and, for a constant $C$, the Lyapunov sequence
--   $$V_{n+1}:=(1-C\gamma_n^2)\,F(x_n)+(1-u_n)\,P_{n+1}.$$
--   $P_n$ is a function of the index $n$ and the state $z_n=(x_n,m_n,v_n)$; $V_{n+1}$ is a function of $n$, $x_n$ and $z_{n+1}$.
--
--   The **one-step conditional expectation** of a function $G$ of the next state is
--   $$\mathbb E\big[G(z_{n+1})\,\big|\,z_n=z\big]:=\int_\Xi G\big(T_{n+1}(z,\xi)\big)\,\mu(d\xi),$$
--   where $T_{n+1}(z,\xi)$ is iteration $n+1$ of Algorithm 5.1 from the state $z$ with the gradient $\nabla f(x,\xi)$. Under Assumption 4.1, $z_n$ is $\mathcal F_n=\sigma(\xi_1,\dots,\xi_n)$-measurable and $\xi_{n+1}$ is independent of $\mathcal F_n$ with law $\mu$, so this integral evaluated at $z=z_n$ is a version of the conditional expectation $\mathbb E_n G(z_{n+1})=\mathbb E(G(z_{n+1})\mid\mathcal F_n)$ used on pp. 26–27.
--
--   **Formalization Note** The vector $D_n=r_n^{-1}/(\varepsilon+\sqrt{\hat v_n})$ of p. 26 is not defined separately: $P_n=\frac1{2a_n}\langle D_n,m_n^{\odot2}\rangle$ is written out. $c_{n+1}$ is `cCoef β n`, $V_{n+1}$ is `lyapV γ α β ε F C n x_n z_{n+1}`, so that no natural-number subtraction $n-1$ appears. Division by $a_n$, $r_n$, $\bar r_n$ or $\sqrt{\beta_{n+1}}$ returns $0$ in Lean when the divisor vanishes; the theorems using these quantities state the positivity they need ($\alpha_1,\beta_1<1$; $\alpha_{n+2}<1$ or "for $n$ large"; $\beta_{n+1}>0$).
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, §9 intro p. 25; §9.2 pp. 26–27 (definitions of a_n, P_n, u_n, D_n, c_{n+1}, V_n)

import Mathlib
import Definitions.Def_AdamDyn_DecBdd_Algorithm

open MeasureTheory

namespace AdamDyn.DecBdd

/-- `a_n := (1 - α_{n+1}) / γ_n` (§9.2, p. 26). -/
noncomputable def aSeq (γ α : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 - α (n + 1)) / γ n

/-- `u_n := 1 - a_{n+1} / a_n` (§9.2, p. 26). -/
noncomputable def uSeq (γ α : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 - aSeq γ α (n + 1) / aSeq γ α n

/-- `P_n := (1 / (2 a_n r_n)) ⟨m_n^{⊙2}, 1 / (ε + √v̂_n)⟩` (§9.2, p. 26), as a function of the
index `n` and the state `z = (x_n, m_n, v_n)`. -/
noncomputable def potP {d : ℕ} (γ α β : ℕ → ℝ) (ε : ℝ) (n : ℕ) (z : AdamDyn.ConstStep.E d × AdamDyn.ConstStep.E d × AdamDyn.ConstStep.E d) : ℝ :=
  (1 / (2 * aSeq γ α n * AdamDyn.DecConv.biasWeight α n)) *
    ∑ i, z.2.1 i ^ 2 / (ε + Real.sqrt (vHat β n z i))

/-- The coefficient `c_{n+1} := ((1 - β_{n+1}) / √β_{n+1}) (1/(1 + √β_{n+1}) + (1 - r̄_n)/(2 r̄_n))`
of (9.3), p. 26 (indexed by `n`). -/
noncomputable def cCoef (β : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((1 - β (n + 1)) / Real.sqrt (β (n + 1))) *
    (1 / (1 + Real.sqrt (β (n + 1))) + (1 - AdamDyn.DecConv.biasWeight β n) / (2 * AdamDyn.DecConv.biasWeight β n))

/-- One-step conditional expectation: `E[G(z_{n+1}) | z_n = z] = ∫ G(T_{n+1}(z, ξ)) dμ(ξ)`, where
`T_{n+1}(z, ξ)` is iteration `n + 1` of Algorithm 5.1 with gradient `∇f(x, ξ)`. Under
Assumption 4.1 this is a version of `E_n G(z_{n+1}) = AdamDyn.ConstStep.E(G(z_{n+1}) | ℱ_n)`. -/
noncomputable def stepExpect {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (gf : AdamDyn.ConstStep.E d → Ξ → AdamDyn.ConstStep.E d) (γ α β : ℕ → ℝ) (ε : ℝ) (n : ℕ) (z : AdamDyn.ConstStep.E d × AdamDyn.ConstStep.E d × AdamDyn.ConstStep.E d)
    (G : AdamDyn.ConstStep.E d × AdamDyn.ConstStep.E d × AdamDyn.ConstStep.E d → ℝ) : ℝ :=
  ∫ ξ, G (adamStep γ α β ε (n + 1) z (gf z.1 ξ)) ∂μ

/-- The Lyapunov sequence of §9.2, p. 27, `V_{n+1} := (1 - C γ_n²) F(x_n) + (1 - u_n) P_{n+1}`,
as a function of `n`, the point `x = x_n` and the state `z = z_{n+1}`. -/
noncomputable def lyapV {d : ℕ} (γ α β : ℕ → ℝ) (ε : ℝ) (F : AdamDyn.ConstStep.E d → ℝ) (C : ℝ) (n : ℕ) (x : AdamDyn.ConstStep.E d)
    (z : AdamDyn.ConstStep.E d × AdamDyn.ConstStep.E d × AdamDyn.ConstStep.E d) : ℝ :=
  (1 - C * γ n ^ 2) * F x + (1 - uSeq γ α n) * potP γ α β ε (n + 1) z

end AdamDyn.DecBdd


