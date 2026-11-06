-- Prove2me | Definitions.Def_LiuZhangBRW_Concentration_BRWModel
-- name    : LiuZhangBRW_Concentration_BRWModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:18:37.295196+00:00
-- url     : https://prove2.me/theorems/79714800-ced2-4b6c-b125-f8bd53b79c76
-- title:
--   Branching random walk $(a_i(u_{i-1}),p_i(\cdot\mid u_{i-1}))_{i\ge1}$, positions $u_i$ and the random-walk path law $P$
-- statement:
--   A **branching random walk** (BRW) on $\mathbb R$ is given by a starting point $u_0\in\mathbb R$, a scaling integer $N$, and for each generation $i\ge1$ a pair
--   $$
--   \bigl(a_i(u_{i-1}),\,p_i(\cdot\mid u_{i-1})\bigr):
--   $$
--   a particle born at $u_{i-1}$ has on average $a_i(u_{i-1})\ge0$ children (the **branching factor** or birth rate), and each child is displaced by $X_i$ with law $p_i(\cdot\mid u_{i-1})$. Along a lineage (spine) the positions are
--   $$
--   u_i=u_0+\frac{X_1}{N}+\dots+\frac{X_i}{N}.
--   $$
--   The **random-walk path law** $P$ is the law of $(X_1,X_2,\dots)$ when $X_i$ is drawn from $p_i(\cdot\mid u_{i-1})$ given the past, i.e. $P(dX_1\cdots dX_n)=p_1(X_1\mid u_0)\cdots p_n(X_n\mid u_{n-1})$.
--
--   This is the model of §6 on which the BRW concentration inequality is stated.
--
--   **Formalization Note** The paths live in $\mathbb R^{\mathbb N}$ and $X_i$ is the coordinate $\omega_i$ (`coord i`); coordinate $0$ is the constant $0$ and unused. The displacement laws are Markov kernels, which generalize the paper's densities. The path law is built by the Ionescu-Tulcea theorem (`Kernel.trajMeasure`). Birth rates are measurable and nonnegative. $N\ge1$ is not a field; the theorems assume it.
-- source:
--   Liu, Zhang, Concentration Inequalities for Branching Random Walks with Applications to Phase Transitions in CSPs, arXiv:1601.04794 (artifact sha256 7499631b9d550f66e791c0b3df0879f26102f111fee3052e363ebbff0c72bdcb; no version stamp), §6.2, p. 21 (the pairs (a_i(u_{i−1}), p(x_i | u_{i−1}))), p. 22 (P(dX_1 ⋯ dX_n)), p. 23 (u_i = u_0 + X_1/N + ⋯ + X_i/N)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace LiuZhangBRW.Concentration

/-- A branching random walk on `ℝ` in the sense of §6.2 (Liu, Zhang, *Concentration
Inequalities for Branching Random Walks with Applications to Phase Transitions in CSPs*,
arXiv:1601.04794, artifact sha256 7499631b…bdcb, §6.2, p. 21: "a BRW be defined by a sequence
of pairs `(a_i(u_{i−1}), p(x_i | u_{i−1}))_{i=1,2,…}` where the branching factor `a_i` (also
called birth-rate) is the expectation of offsprings which depends on the birthplace `u_{i−1}`,
and `p(x_i | u_{i−1})dx := Pr(X_i ∈ dx | σ(u_{i−1}))` is the probability density function (pdf)
of children's displacements"). The fields are
* `u₀`, the deterministic starting position;
* `N`, the scaling integer of §4.2, p. 6 (positions are `u_i = u_0 + X_1/N + ⋯ + X_i/N`, p. 23);
* `step i`, the law `p_i(· | u)` of the displacement `X_i` of a child born at `u` (used for
  `i ≥ 1`);
* `rate i`, the birth rate `a_i(u) ≥ 0` at birthplace `u` (used for `i ≥ 1`).

**Formalization Note** The paper's displacement densities are generalized to Markov kernels
(every density is a kernel). `N ≥ 1` is not a field: the statements that need it take it as a
hypothesis. Birth rates are measurable and nonnegative, which (6.5) presupposes. -/
structure BRWModel where
  /-- The starting position `u_0`. -/
  u₀ : ℝ
  /-- The scaling integer `N` (positions are scaled by `1/N`). -/
  N : ℕ
  /-- `step i u` is the law `p_i(· | u)` of the displacement `X_i` of a child born at `u`. -/
  step : ℕ → Kernel ℝ ℝ
  /-- Each displacement law is a probability measure. -/
  step_markov : ∀ i, IsMarkovKernel (step i)
  /-- `rate i u` is the birth rate (branching factor) `a_i(u)` at birthplace `u`. -/
  rate : ℕ → ℝ → ℝ
  /-- Birth rates are measurable. -/
  rate_measurable : ∀ i, Measurable (rate i)
  /-- Birth rates are nonnegative. -/
  rate_nonneg : ∀ i u, 0 ≤ rate i u

namespace BRWModel

instance (B : BRWModel) (i : ℕ) : IsMarkovKernel (B.step i) := B.step_markov i

/-- The coordinate `X_i` on the path space `ℕ → ℝ`: `X_i(ω) = ω i`, the displacement at
generation `i` of a lineage (spine) (p. 21). Coordinate `0` is unused. -/
def coord (i : ℕ) (ω : ℕ → ℝ) : ℝ := ω i

/-- The position `u_i = u_0 + X_1/N + ⋯ + X_i/N` of the `i`-th ancestor of a lineage (Liu,
Zhang, arXiv:1601.04794, p. 23, "where `u_i = u_0 + X_1/N + ⋯ + X_i/N`"). -/
noncomputable def pos (B : BRWModel) (i : ℕ) (ω : ℕ → ℝ) : ℝ :=
  B.u₀ + (∑ j ∈ Finset.Icc 1 i, ω j) / B.N

/-- The position `u_n` computed from a history `(x_0, x_1, …, x_n)`; the entry `x_0` is ignored. -/
noncomputable def histPos (B : BRWModel) (n : ℕ) (h : (i : Finset.Iic n) → ℝ) : ℝ :=
  B.u₀ + (∑ j : Finset.Iic n, (if (j : ℕ) = 0 then 0 else 1) * h j) / B.N

lemma measurable_histPos (B : BRWModel) (n : ℕ) : Measurable (B.histPos n) := by
  unfold histPos
  fun_prop

/-- The transition kernel of the underlying random walk: given the history up to generation
`n`, the displacement `X_{n+1}` has law `p_{n+1}(· | u_n)`. -/
noncomputable def stepKernel (B : BRWModel) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → ℝ) ℝ :=
  (B.step (n + 1)).comap (B.histPos n) (B.measurable_histPos n)

instance (B : BRWModel) (n : ℕ) : IsMarkovKernel (B.stepKernel n) := by
  unfold stepKernel; infer_instance

/-- The path law of the underlying random walk (Liu, Zhang, arXiv:1601.04794, §6.2, p. 22,
"`P(dX_1 ⋯ dX_n) = p_1(X_1) ⋯ p_n(X_n) dX_1 ⋯ dX_n`", with `p_i(X_i) = p_i(X_i | u_{i−1})`,
p. 21): the law on `ℕ → ℝ` of `(X_0, X_1, X_2, …)` with `X_0 = 0` and `X_{i}` drawn from
`p_i(· | u_{i−1})` given the past, built by the Ionescu-Tulcea theorem (`Kernel.trajMeasure`).

**Formalization Note** The coordinate `0` is the constant `0` and plays no role. -/
noncomputable def rwLaw (B : BRWModel) : Measure (ℕ → ℝ) :=
  Kernel.trajMeasure (X := fun _ => ℝ) (Measure.dirac 0) B.stepKernel

end BRWModel

end LiuZhangBRW.Concentration


