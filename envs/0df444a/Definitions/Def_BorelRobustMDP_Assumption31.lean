-- Prove2me | Definitions.Def_BorelRobustMDP_Assumption31
-- name    : BorelRobustMDP_Assumption31
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:14:09.700204+00:00
-- url     : https://prove2.me/theorems/6d70b7c7-28b7-4f8c-8222-a6188e5f061f
-- title:
--   Assumption 3.1: bounding functions and integrability
-- statement:
--   The data are $\alpha,\underline\epsilon,\overline\epsilon\ge0$ with $\underline\epsilon+\overline\epsilon=1$, $\alpha\ne1$, measurable $\underline b:E\to(-\infty,-\underline\epsilon]$, $\overline b:E\to[\overline\epsilon,\infty)$ and $K\in[1,\infty)$; the **bounding function** is $b=\overline b-\underline b\ge1$. Assumption 3.1 asks for:
--
--   1. for all $n<N$, $Q\in\mathcal Q_{n+1}$, $(x,a)\in D_n$: $\mathbb E^Q[-c_n^-(x,a,T_n(x,a,Z_{n+1}))]\ge\underline b(x)$, $\mathbb E^Q[\underline b(T_n(x,a,Z_{n+1}))]\ge\alpha\underline b(x)$, $\mathbb E^Q[c_n^+(x,a,T_n(x,a,Z_{n+1}))]\le\overline b(x)$, $\mathbb E^Q[\overline b(T_n(x,a,Z_{n+1}))]\le\alpha\overline b(x)$, and $\underline b\le c_N\le\overline b$;
--   2. every $(\bar x,\bar a)\in D_n$ has a neighbourhood $U$ and nonnegative measurable $\Theta_1,\Theta_2\in L^p(P_{n+1})$ with $|c_n(x,a,T_n(x,a,z))|\le\Theta_1(z)$ and $b(T_n(x,a,z))\le\Theta_2(z)$ for all $z$ and $(x,a)\in U\cap D_n$;
--   3. the sets $\mathcal Q_n$, $n=1,\dots,N$, are norm bounded by $K$.
--
--   These conditions make the cost integrable under every law of motion, and allow unbounded cost.
--
--   **Formalization Note.** The data are explicit so that theorems hold for every choice and can name $b$. The four expectation inequalities are stated as lower Lebesgue integrals of the nonnegative functions $c_n^-$, $-\underline b\circ T_n$, $c_n^+$, $\overline b\circ T_n$, so that they carry integrability. The neighbourhood $U$ replaces the closed ball $B_\epsilon(\bar x,\bar a)$ of an arbitrary product metric.
-- source:
--   Bäuerle & Glauner, arXiv:2007.13103v1, Assumption 3.1, p.6

import Mathlib
import Definitions.Def_BorelRobustMDP_RobustModel

open MeasureTheory Topology

namespace BorelRobustMDP

universe u v

/-- The constants and functions of Assumption 3.1 (Bäuerle & Glauner, arXiv:2007.13103v1, p.6): `α`,
`ϵ̲ = ϵlo`, `ϵ̄ = ϵhi`, the lower and upper bounding functions `b̲ = blo`, `b̄ = bhi`, and the norm
bound `K`.

**Formalization Note.** The assumption says "there exist" these; they are taken as data so that each
theorem holds for every such choice, and so that the bounding function `b` can be named in the
statements. -/
structure BoundingData (E : Type u) where
  α : ℝ
  ϵlo : ℝ
  ϵhi : ℝ
  blo : E → ℝ
  bhi : E → ℝ
  K : ℝ

/-- The bounding function `b(x) := b̄(x) − b̲(x)` (Bäuerle & Glauner, arXiv:2007.13103v1, Assumption
3.1 (ii), p.6). -/
def BoundingData.b {E : Type u} (B : BoundingData E) (x : E) : ℝ := B.bhi x - B.blo x

variable {E A : Type u} {Z : Type v} [MeasurableSpace E] [MeasurableSpace A] [MeasurableSpace Z]
  {N : ℕ}

/-- Assumption 3.1 (i) (Bäuerle & Glauner, arXiv:2007.13103v1, p.6).

**Formalization Note.** The four expectation inequalities are stated with lower Lebesgue integrals
of the nonnegative functions `c⁻`, `−b̲ ∘ T`, `c⁺`, `b̄ ∘ T`, after moving signs, so that they carry
integrability: a Bochner integral would be `0` for a non-integrable integrand. Thus
`E^Q[−c⁻] ≥ b̲(x)` is `∫⁻ (−c)⁺ dQ ≤ −b̲(x)` and `E^Q[b̲(T)] ≥ α b̲(x)` is
`∫⁻ −b̲(T) dQ ≤ −α b̲(x)`. -/
structure Assumption31_i (R : RobustModel E A Z N) (B : BoundingData E) : Prop where
  α_nonneg : 0 ≤ B.α
  ϵlo_nonneg : 0 ≤ B.ϵlo
  ϵhi_nonneg : 0 ≤ B.ϵhi
  ϵ_sum : B.ϵlo + B.ϵhi = 1
  α_ne_one : B.α ≠ 1
  measurable_blo : Measurable B.blo
  measurable_bhi : Measurable B.bhi
  blo_le : ∀ x, B.blo x ≤ -B.ϵlo
  le_bhi : ∀ x, B.ϵhi ≤ B.bhi x
  negPart_cost : ∀ n < N, ∀ Q ∈ R.𝒬 (n + 1), ∀ y ∈ R.D n,
    ∫⁻ z, ENNReal.ofReal (-(R.c n y (R.T n y z))) ∂Q ≤ ENNReal.ofReal (-(B.blo y.1))
  lower_drift : ∀ n < N, ∀ Q ∈ R.𝒬 (n + 1), ∀ y ∈ R.D n,
    ∫⁻ z, ENNReal.ofReal (-(B.blo (R.T n y z))) ∂Q ≤ ENNReal.ofReal (-(B.α * B.blo y.1))
  posPart_cost : ∀ n < N, ∀ Q ∈ R.𝒬 (n + 1), ∀ y ∈ R.D n,
    ∫⁻ z, ENNReal.ofReal (R.c n y (R.T n y z)) ∂Q ≤ ENNReal.ofReal (B.bhi y.1)
  upper_drift : ∀ n < N, ∀ Q ∈ R.𝒬 (n + 1), ∀ y ∈ R.D n,
    ∫⁻ z, ENNReal.ofReal (B.bhi (R.T n y z)) ∂Q ≤ ENNReal.ofReal (B.α * B.bhi y.1)
  terminal : ∀ x, B.blo x ≤ R.cN x ∧ R.cN x ≤ B.bhi x

/-- Assumption 3.1 (ii) (Bäuerle & Glauner, arXiv:2007.13103v1, p.6): every `(x̄, ā) ∈ D_n` has a
neighbourhood on which `|c_n(x, a, T_n(x, a, z))|` and `b(T_n(x, a, z))` are dominated by nonnegative
measurable functions of `z` lying in `L^p(P_{n+1})`.

**Formalization Note.** The closed ball `B_ϵ(x̄, ā)` of the paper is a neighbourhood `U` of `(x̄, ā)`:
closed balls of a compatible metric form a neighbourhood base, and `E`, `A` carry no chosen metric. -/
def Assumption31_ii [TopologicalSpace E] [TopologicalSpace A] (R : RobustModel E A Z N)
    (B : BoundingData E) : Prop :=
  ∀ n < N, ∀ y₀ ∈ R.D n, ∃ U ∈ 𝓝 y₀, ∃ Θ₁ Θ₂ : Z → ℝ,
    Measurable Θ₁ ∧ Measurable Θ₂ ∧ (∀ z, 0 ≤ Θ₁ z) ∧ (∀ z, 0 ≤ Θ₂ z) ∧
    MemLp Θ₁ R.p (R.P (n + 1)) ∧ MemLp Θ₂ R.p (R.P (n + 1)) ∧
    ∀ z, ∀ y ∈ U ∩ R.D n, |R.c n y (R.T n y z)| ≤ Θ₁ z ∧ B.b (R.T n y z) ≤ Θ₂ z

/-- Assumption 3.1 (iii) (Bäuerle & Glauner, arXiv:2007.13103v1, p.6): `K ∈ [1, ∞)` bounds the
ambiguity sets `𝒬_n`, `n = 1, …, N`, in norm. -/
def Assumption31_iii (R : RobustModel E A Z N) (B : BoundingData E) : Prop :=
  1 ≤ B.K ∧ ∀ n, 1 ≤ n → n ≤ N → R.NormBounded n B.K

/-- Assumption 3.1 (Bäuerle & Glauner, arXiv:2007.13103v1, p.6), for the data `B`. -/
structure Assumption31 [TopologicalSpace E] [TopologicalSpace A] (R : RobustModel E A Z N)
    (B : BoundingData E) : Prop where
  i : Assumption31_i R B
  ii : Assumption31_ii R B
  iii : Assumption31_iii R B

end BorelRobustMDP


