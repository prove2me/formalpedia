-- Prove2me | Definitions.Def_MFGPlanning_Penalized_Duality
-- name    : MFGPlanning_Penalized_Duality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:38:57.554836+00:00
-- url     : https://prove2.me/theorems/60c8a024-f481-4265-9223-940bccce1a3e
-- title:
--   $(W+\chi)^*$, the functional $\Theta$ and its Legendre–Fenchel transform $\Theta^*$ (25)
-- statement:
--   Let $\chi$ be the indicator function of $\{m \ge 0\}$ ($0$ there, $+\infty$ elsewhere). The Legendre–Fenchel transform of $W + \chi$ is
--   $$
--   (W+\chi)^*(a) = \sup_{m \ge 0}\big[a m - W(m)\big] \in (-\infty, +\infty].
--   $$
--   For $\alpha = (\alpha^n_{i,j})$ and $\beta = ([\beta^n]_{i,j})$, $1 \le n \le N_T$, with $[\beta^n]_{i,j} \in \mathbb R^4$,
--   $$
--   \Theta(\alpha, \beta) = \sum_{n=1}^{N_T}\sum_{i,j} (W+\chi)^*\big(\alpha^n_{i,j} + g(x_{i,j}, [\beta^n]_{i,j})\big),
--   $$
--   and for $M = (M^n_{i,j})$, $Z = ([Z^n]_{i,j})$, $0 \le n < N_T$,
--   $$
--   \Theta^*(M, Z) = \sup_{\alpha, \beta}\Big(\sum_{n=1}^{N_T}\sum_{i,j} M^{n-1}_{i,j}\alpha^n_{i,j} + \langle [Z^{n-1}]_{i,j}, [\beta^n]_{i,j}\rangle - (W+\chi)^*\big(\alpha^n_{i,j} + g(x_{i,j}, [\beta^n]_{i,j})\big)\Big).
--   $$
--   As Remark 2 of the paper notes, the variable dual to $\alpha^n$ is $M^{n-1}$: the time index lags by one.
--
--   $\Theta^*$ is the cost of the optimal control problem whose optimality conditions are the discrete schemes; in this mission it enters the penalized minimization problem (50).
--
--   **Formalization Note** All three functionals take values in `EReal`, so an unbounded supremum is $+\infty$ rather than a default value. In Lean `α k`, `β k` for `k : Fin NT` stand for $\alpha^{k+1}$, $\beta^{k+1}$, and `M k`, `Z k` for $M^k$, $Z^k$.
-- source:
--   Achdou, Camilli, Capuzzo-Dolcetta, Mean field games: numerical methods for the planning problem, hal-00465404v1 (2010), §3.1, (W+χ)*, Θ and (25), Remark 2, p. 7

import Mathlib
import Definitions.Def_MFGPlanning_Penalized_Grid

namespace MFGPlanning.Penalized

/-- (W + χ)*(a) = sup_{m ≥ 0} (a m − W(m)), the Legendre–Fenchel transform of W + χ with χ the
indicator of {m ≥ 0} (p. 7). Formalization Note: valued in `EReal`, so an unbounded supremum
is +∞ and not a junk value. -/
noncomputable def conjWchi (d : Data) (a : ℝ) : EReal :=
  ⨆ (m : ℝ) (_ : 0 ≤ m), ((a * m - d.W m : ℝ) : EReal)

/-- Θ(α, β) = Σ_{n=1}^{N_T} Σ_{i,j} (W + χ)*(α^n_{i,j} + g(x_{i,j}, [β^n]_{i,j})) (p. 7).
Formalization Note: `α k`, `β k` (k : Fin N_T) are α^{k+1}, [β^{k+1}] (Remark 2). -/
noncomputable def Θ (d : Data) (α : Fin d.NT → Pt d → ℝ) (β : Fin d.NT → Pt d → Fin 4 → ℝ) :
    EReal :=
  ∑ k, ∑ p, conjWchi d (α k p + d.g p (β k p))

/-- The duality pairing Σ_{n=1}^{N_T} Σ_{i,j} (M^{n−1}_{i,j} α^n_{i,j} + ⟨[Z^{n−1}]_{i,j}, [β^n]_{i,j}⟩)
of (25), p. 7. Formalization Note: `M k`, `Z k` are M^k, Z^k (k = 0, …, N_T − 1) and pair with
`α k`, `β k` = α^{k+1}, β^{k+1}: the lag of Remark 2. -/
def pair (d : Data) (M : Fin d.NT → Pt d → ℝ) (Z : Fin d.NT → Pt d → Fin 4 → ℝ)
    (α : Fin d.NT → Pt d → ℝ) (β : Fin d.NT → Pt d → Fin 4 → ℝ) : ℝ :=
  ∑ k, ∑ p, (M k p * α k p + ∑ l, Z k p l * β k p l)

/-- Θ*(M, Z) = sup_{α, β} (pairing − Θ(α, β)), the Legendre–Fenchel transform of Θ ((25), p. 7),
valued in `EReal`. -/
noncomputable def ΘStar (d : Data) (M : Fin d.NT → Pt d → ℝ) (Z : Fin d.NT → Pt d → Fin 4 → ℝ) :
    EReal :=
  ⨆ (α : Fin d.NT → Pt d → ℝ) (β : Fin d.NT → Pt d → Fin 4 → ℝ),
    (pair d M Z α β : EReal) - Θ d α β

end MFGPlanning.Penalized


