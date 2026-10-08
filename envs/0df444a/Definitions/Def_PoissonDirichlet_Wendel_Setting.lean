-- Prove2me | Definitions.Def_PoissonDirichlet_Wendel_Setting
-- name    : PoissonDirichlet_Wendel_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:33:27.05008+00:00
-- url     : https://prove2.me/theorems/001a958e-058b-4807-b2ae-3e3c696de13e
-- title:
--   Equations (27)–(28), (31)–(34), and Lemma 24: auxiliary Poisson–Dirichlet objects
-- statement:
--   This definition file extends the shared Poisson–Dirichlet stick and ranked-value setting with the quantities used for the Laplace-transform calculations. The paper indexes sequences from $1$; Lean indexes them from $0$.
--
--   1. For ranked frequencies $V_1,V_2,\ldots$, define $A_0=0$ and
--      $$A_n=\frac{V_1+\cdots+V_n}{V_{n+1}},\qquad \Sigma_n=\frac{V_{n+1}+V_{n+2}+\cdots}{V_n}.$$
--   2. For $0<\alpha<1$ and $\lambda\ge0$, define
--      $$\phi_\alpha(\lambda)=\alpha\int_1^\infty e^{-\lambda x}x^{-\alpha-1}\,dx,\qquad
--      \psi_\alpha(\lambda)=1+\alpha\int_0^1(1-e^{-\lambda x})x^{-\alpha-1}\,dx.$$
--   3. The $k$-fold convolution power $\mu^{*k}$ is the law of a sum of $k$ independent variables with law $\mu$; the zeroth power is the point mass at zero. The probability law on $(1,\infty)$ used in Lemma 24 has density $\alpha x^{-\alpha-1}$ there.
--   4. Given interarrival variables $\varepsilon_1,\varepsilon_2,\ldots$, put $X_n=\varepsilon_1+\cdots+\varepsilon_n$. For $C>0$ and $\alpha>0$, the ranked Poisson points of (27)–(28) are represented by $\Delta_n=(C/X_n)^{1/\alpha}$.
--
--   These definitions are the notation used in Proposition 11 and Lemma 24. Their distributional claims remain theorem items.
--
--   **Formalization Note** This file imports `PoissonDirichlet.Ratio.Setting` for stick lengths, ranked values, the PD law, and ratios; it defines only the additional quantities above. The integral formulas are used in the stated parameter range, where their integrands are integrable. The arrival-time representation follows the paper's (27)–(28), avoiding a separate general Poisson random measure object. For inputs outside the intended ranges, the Lean functions are total but do not assert a probabilistic interpretation.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 862, (27)–(28); p. 863, (31)–(34); p. 870, Lemma 24; p. 871, (66)

import Mathlib
import Definitions.Def_PoissonDirichlet_Ratio_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Wendel

/-- (31), first expression, 0-based: `Aseq v k = (v 0 + ⋯ + v (k-1)) / v k` is
`A_k = (V_1 + ⋯ + V_k) / V_{k+1}`; in particular `Aseq v 0 = 0 = A_0`. -/
noncomputable def Aseq (v : ℕ → ℝ) (k : ℕ) : ℝ := (∑ i ∈ Finset.range k, v i) / v k

/-- (32), first expression, 0-based: `Sigseq v k = (v (k+1) + v (k+2) + ⋯) / v k` is
`Σ_{k+1} = (V_{k+2} + V_{k+3} + ⋯) / V_{k+1}`. -/
noncomputable def Sigseq (v : ℕ → ℝ) (k : ℕ) : ℝ := (∑' j, v (k + 1 + j)) / v k

/-- (33): `φ_α(λ) = α ∫_1^∞ e^{-λx} x^{-α-1} dx`. -/
noncomputable def phi (α l : ℝ) : ℝ :=
  α * ∫ x in Set.Ioi (1 : ℝ), Real.exp (-l * x) * x ^ (-α - 1)

/-- (34), first expression: `ψ_α(λ) = 1 + α ∫_0^1 (1 - e^{-λx}) x^{-α-1} dx`. -/
noncomputable def psi (α l : ℝ) : ℝ :=
  1 + α * ∫ x in Set.Ioc (0 : ℝ) 1, (1 - Real.exp (-l * x)) * x ^ (-α - 1)

/-- The `k`-fold additive convolution power of a measure on `ℝ`: the law of the sum of `k`
independent random variables with law `μ` (the Dirac mass at `0` for `k = 0`). -/
noncomputable def convPow (μ : Measure ℝ) (k : ℕ) : Measure ℝ :=
  (fun ν => ν ∗ μ)^[k] (Measure.dirac 0)

/-- `C⁻¹ Λ_α(dx) 1(x > 1) = α x^{-α-1} dx 1(x > 1)`, the law in Lemma 24 (ii) and (66). -/
noncomputable def tailLaw (α : ℝ) : Measure ℝ :=
  volume.withDensity ((Set.Ioi (1 : ℝ)).indicator fun x => ENNReal.ofReal (α * x ^ (-α - 1)))

/-- Arrival times of a unit-rate Poisson process from its interarrival times, 0-based:
`arrival ε k ω = ε 0 ω + ⋯ + ε k ω` is `X_{k+1} = ε_1 + ⋯ + ε_{k+1}` of (28). -/
def arrival {Ω : Type*} (ε : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), ε i ω

/-- The ranked points of a PRM `Λ_α` on `(0, ∞)` with `Λ_α(x, ∞) = C x^{-α}`, represented
through arrival times as in (27)–(28): `prmPoint α C ε k = (C / X_{k+1})^{1/α}` is `Δ_{k+1}`. -/
noncomputable def prmPoint {Ω : Type*} (α C : ℝ) (ε : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  (C / arrival ε k ω) ^ (1 / α)

end PoissonDirichlet.Wendel


