-- Prove2me | Definitions.Def_BarvinokCount_ShortFormula_sigma
-- name    : BarvinokCount_ShortFormula_sigma
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T06:11:16.503314+00:00
-- url     : https://prove2.me/theorems/3a7e1112-7672-4a2e-9e7b-ad299892d2aa
-- title:
--   The closed form of σ(K; c), regular points, and the constant term of a Laurent expansion
-- statement:
--   Let $u_1,\dots,u_k\in\mathbb{Z}^d$ be integral vectors, $K=\operatorname{co}\{u_1,\dots,u_k\}$, and $\Pi$ the semi-open parallelepiped of the generators.
--
--   1. **The function $\sigma$** (Proposition 2.4 with Remark 2.5). For $c\in\mathbb{R}^d$,
--   $$\sigma(K;c)=\Bigl(\sum_{x\in\Pi\cap\mathbb{Z}^d}\exp\{\langle c,x\rangle\}\Bigr)\cdot\prod_{i=1}^k\frac{1}{1-\exp\{\langle c,u_i\rangle\}} .$$
--   For linearly independent generators this is the closed form of the meromorphic function defined, where it converges, by the series $\sum_{x\in K\cap\mathbb{Z}^d}\exp\{\langle c,x\rangle\}$.
--   2. **Regular points.** $c$ is a regular point of $\sigma(K;\cdot)$ if $\langle c,u_i\rangle\ne 0$ for every $i$, i.e. $c$ lies off the singular hyperplanes $H_j=\{c:\langle c,u_j\rangle=0\}$ of Proposition 2.4.
--   3. **Constant term of a Laurent expansion** (§3, p. 772). A real number $a$ is the constant term of the Laurent expansion of $f$ at $t=0$ if for some $N\in\mathbb{N}$ the function $t\mapsto t^N f(t)$ agrees, on a punctured neighbourhood of $0$, with a function $\varphi$ that is real-analytic at $0$, and $a$ is the coefficient of $t^N$ in the Taylor series of $\varphi$ at $0$:
--   $$a=\frac{\varphi^{(N)}(0)}{N!}.$$
--   When such $N,\varphi$ exist, $a$ is uniquely determined by $f$.
--
--   The constant terms $R(K,v,c)$ of $t\mapsto\exp\{t\langle c,v\rangle\}\,\sigma(K;t\cdot c)$ are the quantities Barvinok's algorithm computes and sums.
--
--   **Formalization Note** $\sigma$ is defined by its closed form, never as the sum of the series (an infinite sum would take a junk value outside its convergence region). The milestone *Proposition 2.4 with Remark 2.5* ties the closed form to the series. The closed form depends on the generator list, as in the paper ("given by linearly independent generators"). The sum over $\Pi\cap\mathbb{Z}^d$ is a finite sum (`finsum`; the set is always finite). The paper speaks of $c\in\mathbb{C}^d$ only to describe meromorphic functions; every statement it uses is over $\mathbb{R}^d$, so $c$ is real here.
-- source:
--   Barvinok, A polynomial time algorithm for counting integral points in polyhedra when the dimension is fixed, Math. Oper. Res. 19 (1994), pp. 770–771, Proposition 2.4 and Remark 2.5 (closed form of σ, singular hyperplanes); p. 772, §3 (constant terms R(K_v, v, c) of Laurent expansions)

import Mathlib
import Definitions.Def_BarvinokCount_ShortFormula_coneIndex

open scoped Topology

namespace BarvinokCount.ShortFormula

/-- The closed form of `σ(K; c)` for the cone given by linearly independent generators `u`
(Proposition 2.4 with Remark 2.5):
`σ(K; c) = (∑_{x ∈ Π ∩ ℤ^d} exp⟨c, x⟩) · ∏_i 1 / (1 − exp⟨c, u_i⟩)`.
The sum is a finite sum (`finsum`; `Π ∩ ℤ^d` is finite). -/
noncomputable def sigma {d k : ℕ} (u : Fin k → Fin d → ℤ) (c : Fin d → ℝ) : ℝ :=
  (∑ᶠ z ∈ {z : Fin d → ℤ | castVec z ∈ halfOpenBox u}, Real.exp (c ⬝ᵥ castVec z)) *
    ∏ i, 1 / (1 - Real.exp (c ⬝ᵥ castVec (u i)))

/-- `c` is a regular point of `σ(K; ·)`: it is orthogonal to no generator, i.e. it lies off the
singular hyperplanes `H_j = {c : ⟨c, u_j⟩ = 0}` (Proposition 2.4). -/
def IsRegular {d k : ℕ} (u : Fin k → Fin d → ℤ) (c : Fin d → ℝ) : Prop :=
  ∀ i, c ⬝ᵥ castVec (u i) ≠ 0

/-- `a` is the constant term of the Laurent expansion of `f` at `t = 0` (§3, p. 772): for some
`N`, the function `t ↦ t^N f(t)` agrees on a punctured neighbourhood of `0` with a function `φ`
analytic at `0`, and `a` is the coefficient of `t^N` in the Taylor series of `φ`.
This determines `a` uniquely when it exists. -/
def IsLaurentConstTerm (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ (N : ℕ) (φ : ℝ → ℝ), AnalyticAt ℝ φ 0 ∧ (∀ᶠ t in 𝓝[≠] (0 : ℝ), φ t = t ^ N * f t) ∧
    a = iteratedDeriv N φ 0 / (N.factorial : ℝ)

end BarvinokCount.ShortFormula


