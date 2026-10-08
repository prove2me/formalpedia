-- Prove2me | Definitions.Def_PolymerEndpoint_GeoLoc_Model
-- name    : PolymerEndpoint_GeoLoc_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T04:30:10.697872+00:00
-- url     : https://prove2.me/theorems/b2bf93fd-0592-465d-b2d5-e499ecebbc03
-- title:
--   §1.1, pp. 4–5; (3.1) — the directed polymer in ℤ^d: environment, paths, Z_n, endpoint pmf f_n, free energy, λ(β), the two phases
-- statement:
--   This module fixes the **directed polymer in random environment** in dimension $d+1$, $d\ge 1$.
--
--   1. **Environment.** A family $(X_u)_{u\in\mathbb N\times\mathbb Z^d}$ of independent real random variables on a probability space $(\Omega,\mathcal F,\mathbf P)$, each with law $\mathfrak L$ (the *disorder distribution*).
--   2. **Paths.** A nearest-neighbour path of length $n$ from the origin is a sequence of $n$ steps $\pm e_j$; $\gamma(i)$ is its position after $i$ steps, $\gamma(0)=0$, and $\|x\|_1=\sum_j|x_j|$ is the $\ell^1$ norm on $\mathbb Z^d$.
--   3. **Partition function and endpoint distribution.** For $\beta\ge 0$,
--   $$Z_n=\frac1{(2d)^n}\sum_{\gamma}\exp\Big(\beta\sum_{i=1}^n X_{i,\gamma(i)}\Big),\qquad f_n(x)=\rho_n(\omega_n=x)=\frac{\sum_{\gamma:\gamma(n)=x}\exp\big(\beta\sum_{i=1}^n X_{i,\gamma(i)}\big)}{\sum_{\gamma}\exp\big(\beta\sum_{i=1}^n X_{i,\gamma(i)}\big)},$$
--   the sums running over the $(2d)^n$ paths of length $n$. $f_n$ is the probability mass function of the endpoint under the quenched polymer measure $\rho_n$.
--   4. **Free energy.** $F_n=\frac1n\log Z_n$ ($F_0=0$), and $\lambda(\alpha)=\log\mathbf E\,e^{\alpha X_u}$ is the logarithmic moment generating function of $\mathfrak L$.
--   5. **Phases.** $\mathbf E(F_n)$ is computed under the canonical environment (the product of copies of $\mathfrak L$ over $\mathbb N\times\mathbb Z^d$). The **low-temperature phase** $\beta>\beta_c$ is the statement that $\mathbf E(F_n)$ converges to a limit $p(\beta)<\lambda(\beta)$; the **high-temperature phase** $0\le\beta\le\beta_c$ is the statement that $\mathbf E(F_n)\to\lambda(\beta)$.
--
--   These are the objects all statements of the mission are about.
--
--   **Formalization Note.** The critical temperature $\beta_c$ is defined in the paper only through the cited Theorem A (Comets–Yoshida): $0\le\beta\le\beta_c\Rightarrow p(\beta)=\lambda(\beta)$ and $\beta>\beta_c\Rightarrow p(\beta)<\lambda(\beta)$, where $p(\beta)=\lim\mathbf E(F_n)$ exists by (1.5). The phases are therefore encoded by these free-energy conditions. The environment is indexed by $\mathbb N\times\mathbb Z^d$ with $\mathbb N$ including $0$; only time indices $\ge1$ are ever read. Paths are encoded as sequences of steps (coordinate, sign). Cells, paths, the environment predicate, $Z_n$, $f_n$, $F_n$, $\lambda$ and the canonical environment law are imported from the shared module `PolymerEndpoint.Atomic.Model`; this module adds the path weight, $\mathbf E(F_n)$ and the two phases.
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, pp. 4–5, §1.1; p. 5, §1.2.1 and Theorem A; p. 26, (3.1)

import Mathlib
import Definitions.Def_PolymerEndpoint_Atomic_Model

namespace PolymerEndpoint.GeoLoc

open MeasureTheory ProbabilityTheory Filter Topology

/-- The Boltzmann weight `exp(β ∑_{i=1}^n X_{i, γ(i)})` of a path `γ` of length `n`. -/
noncomputable def weight {d : ℕ} {Ω : Type*} (X : PolymerEndpoint.Atomic.Cell d → Ω → ℝ) (β : ℝ) {n : ℕ}
    (s : Fin n → PolymerEndpoint.Atomic.Step d) (a : Ω) : ℝ :=
  Real.exp (β * ∑ m : Fin n, X ((m : ℕ) + 1, PolymerEndpoint.Atomic.pos s ((m : ℕ) + 1)) a)

/-- The averaged quenched free energy `E(F_n)` computed on the canonical environment. -/
noncomputable def meanF (d : ℕ) (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏] (β : ℝ) (n : ℕ) : ℝ :=
  ∫ Y, PolymerEndpoint.Atomic.F (fun (u : PolymerEndpoint.Atomic.Cell d) (Y : PolymerEndpoint.Atomic.Cell d → ℝ) => Y u) β n Y ∂(PolymerEndpoint.Atomic.envLaw (d := d) 𝔏)

/-- Low-temperature phase `β > β_c`, encoded through Theorem A: `p(β) = lim E(F_n) < λ(β)`. -/
def LowTemp (d : ℕ) (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏] (β : ℝ) : Prop :=
  ∃ p < PolymerEndpoint.Atomic.logMGF 𝔏 β, Tendsto (meanF d 𝔏 β) atTop (𝓝 p)

/-- High-temperature phase `0 ≤ β ≤ β_c`, encoded through Theorem A: `lim E(F_n) = λ(β)`. -/
def HighTemp (d : ℕ) (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏] (β : ℝ) : Prop :=
  Tendsto (meanF d 𝔏 β) atTop (𝓝 (PolymerEndpoint.Atomic.logMGF 𝔏 β))

end PolymerEndpoint.GeoLoc


