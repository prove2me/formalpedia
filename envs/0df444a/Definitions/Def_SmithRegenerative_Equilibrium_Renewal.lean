-- Prove2me | Definitions.Def_SmithRegenerative_Equilibrium_Renewal
-- name    : SmithRegenerative_Equilibrium_Renewal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:26:01.118907+00:00
-- url     : https://prove2.me/theorems/0b90333b-00a6-487d-b68a-7b2bcf97fb78
-- title:
--   General renewal process (§2·1–2·2): cycle law F, delay law K, mean μ₁, renewal measure H_K, aperiodicity ϖ = 0 and the class 𝔖
-- statement:
--   This file fixes the renewal-theoretic objects of §2 of Smith (1955).
--
--   1. **Cycle law.** The renewal intervals $t_1, t_2, \dots$ are independent, identically distributed, non-negative and "not zero with probability one". Their common law $F$ is a probability measure on $\mathbb R$ carried by $[0,\infty)$ with $F \neq \delta_0$. The paper's distribution function is $F(t) = F((-\infty,t])$, so $1 - F(t) = F((t,\infty))$.
--   2. **Delay law.** The initial delay $t_0 \ge 0$ has law $K$, a measure on $[0,\infty)$ of total mass $K(+\infty) \le 1$; Theorem A allows $K(+\infty) < 1$ (an improper delay).
--   3. **Mean.** $\mu_1 = \mathbb E\, t_i = \int x\, dF(x) \in (0, \infty]$; the value $\mu_1 = \infty$ is allowed.
--   4. **Renewal measure.** With $F_K^{(0)} = K$ and $F_K^{(n)} = F_K^{(n-1)} * F$ (2·1·4), the renewal function is (2·1·5)
--   $$
--   H_K(t) = \sum_{n=0}^{\infty} F_K^{(n)}(t),
--   $$
--   the expected number of regenerations in $[0,t]$. At the level of measures $H_K = \sum_{n \ge 0} K * F^{*n}$ with $F^{*0} = \delta_0$, and a Stieltjes integral $\int_0^t \Psi(t-t')\, dH_K(t')$ is an integral over the closed interval $[0,t]$.
--   5. **Aperiodicity.** $F$ is *periodic* with period $\varpi > 0$ if it is a step function whose jumps all lie on $\{n\varpi : n = 0, 1, 2, \dots\}$, $\varpi$ being the greatest such number; otherwise $\varpi = 0$. Thus $\varpi = 0$ means that no $\varpi > 0$ has $F(\{n\varpi : n \in \mathbb N\}) = 1$.
--   6. **The class $\mathfrak S$.** $F \in \mathfrak S$ if for some $k \ge 1$ the $k$-fold convolution $F^{*k}$ has a non-zero absolutely continuous component, i.e. is not mutually singular with Lebesgue measure.
--
--   These objects are shared by every statement of the mission: the key renewal theorems (Theorem A, Theorem 1) and the limit theorem for equilibrium processes (Theorem 2) are all statements about $H_K$.
--
--   **Formalization Note** Distributions are measures on $\mathbb R$. $\mu_1$ is an extended non-negative real (`ENNReal`), so $\mu_1 = \infty$ is a genuine value. The renewal measure uses the convolution power `convPow` of the referenced definition `QueueingFundamentals.MG1.transforms` ($F^{*0} = \delta_0$, $F^{*(n+1)} = F^{*n} * F$).
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, pp. 9–10, §2·1 (2·1·1)–(2·1·5), §2·2 (periodicity, the class 𝔖)

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_transforms

namespace SmithRegenerative.Equilibrium

open MeasureTheory QueueingFundamentals.MG1

/-- **Cycle law** (Smith 1955, §2·1, p. 9). `F` is the law of a renewal interval `tᵢ` (`i ≥ 1`):
a probability measure on `ℝ` concentrated on `[0, ∞)` ("non-negative") which is not the unit mass
at `0` ("not zero with probability one", i.e. `P{tᵢ = 0} < 1`).

Formalization Note: distributions are measures on `ℝ`; the paper's distribution function is
`F(t) = F (Set.Iic t)` and `1 − F(t) = F (Set.Ioi t)`. The renewal intervals are proper (finite
almost surely), as in §2·1 and Theorem A. -/
def IsCycleLaw (F : Measure ℝ) : Prop :=
  IsProbabilityMeasure F ∧ F (Set.Iio 0) = 0 ∧ F ≠ Measure.dirac 0

/-- **Delay law** (Smith 1955, §2·1 and §2·2, pp. 9–10). `K` is the law of the initial delay `t₀`:
a measure on `ℝ` concentrated on `[0, ∞)` with total mass `K(+∞) = K ℝ ≤ 1` (Theorem A allows an
improper delay, `K(+∞) < 1`). -/
def IsDelayLaw (K : Measure ℝ) : Prop :=
  K (Set.Iio 0) = 0 ∧ K Set.univ ≤ 1

/-- **Mean** `μ₁ = E tᵢ = ∫ x dF(x)` (Smith 1955, (2·1·1), p. 9), as an extended non-negative real:
`μ₁ = ∞` is a value, not a junk default.

Formalization Note: the integrand is `ENNReal.ofReal x`; for a law on `[0, ∞)` this is `∫ x dF`. -/
noncomputable def mean (F : Measure ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal x ∂F

/-- **Renewal measure** `H_K` (Smith 1955, (2·1·4)–(2·1·5), p. 9): `F_K^{(0)} = K`,
`F_K^{(n)} = F_K^{(n−1)} ∗ F`, `H_K = Σ_{n ≥ 0} F_K^{(n)}`, as a measure on `ℝ`:
`H_K = Σ_{n ≥ 0} K ∗ F^{∗n}`, with `F^{∗0} = δ₀` (`convPow` of the referenced
`QueueingFundamentals.MG1.transforms`). The paper's renewal function is `H_K(t) = H_K (Set.Iic t)`,
and a Stieltjes integral `∫₀^t Ψ(t − t′) dH_K(t′)` is `∫ s in Set.Icc 0 t, Ψ (t - s) ∂H_K`
(closed at both ends, so atoms of `H_K` at `0` and at `t` are included). -/
noncomputable def renewalMeasure (K F : Measure ℝ) : Measure ℝ :=
  Measure.sum (fun n : ℕ => K.conv (convPow F n))

/-- **Aperiodicity** `ϖ = 0` (Smith 1955, §2·2, p. 10). The paper calls `F` *periodic* with period
`ϖ > 0` when `F` is a step function all of whose jumps lie on `{nϖ : n = 0, 1, 2, …}` (and `ϖ` is the
greatest such number), and sets `ϖ = 0` when `F` is not periodic. A step function with all jumps on
`{nϖ}` is exactly a law giving mass one to `{nϖ : n ∈ ℕ}`, so `ϖ = 0` holds iff no `ϖ > 0` has
`F {nϖ : n ∈ ℕ} = 1`. (For a cycle law `F ≠ δ₀` a greatest such `ϖ` exists whenever one exists.) -/
def IsAperiodic (F : Measure ℝ) : Prop :=
  ¬ ∃ ϖ : ℝ, 0 < ϖ ∧ F {x : ℝ | ∃ n : ℕ, x = (n : ℝ) * ϖ} = 1

/-- **The class 𝔖** (Smith 1955, §2·2, p. 10): "If for some k the k-th iterated convolution of F(t)
with itself possesses an absolutely continuous component we write F(t) ∈ 𝔖." The `k`-th iterated
convolution `F^{∗k}` (`k ≥ 1`) has a non-zero absolutely continuous part in its Lebesgue
decomposition with respect to Lebesgue measure iff it is not mutually singular with Lebesgue
measure. `k = 0` (the unit mass `δ₀`) is excluded. -/
def InClassS (F : Measure ℝ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ ¬ (convPow F k).MutuallySingular volume

end SmithRegenerative.Equilibrium


