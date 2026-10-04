-- Prove2me | Definitions.Def_RegretBandits_Linear_Potential
-- name    : RegretBandits_Linear_Potential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:51:08.410861+00:00
-- url     : https://prove2.me/theorems/a8f6ec89-d24e-4551-9bcf-5f2e13a11ef2
-- title:
--   $\omega$-potentials and the Legendre function $F_\psi$ (Definition 5.4); negative entropy
-- statement:
--   Let $\omega\ge0$ and $a\in\mathbb R\cup\{+\infty\}$. A function $\psi:(-\infty,a)\to(0,+\infty)$ is an **$\omega$-potential** (Definition 5.4) if it is convex and continuously differentiable and
--   $$\lim_{x\to-\infty}\psi(x)=\omega,\qquad \lim_{x\to a}\psi(x)=+\infty,\qquad \psi'>0,\qquad \int_\omega^{\omega+1}|\psi^{-1}(s)|\,ds<+\infty .$$
--   Such a $\psi$ is an increasing bijection of $(-\infty,a)$ onto $(\omega,+\infty)$ with inverse $\psi^{-1}$. The associated function on $\bar D=[\omega,+\infty)^d$ is
--   $$F_\psi(x)=\sum_{i=1}^d\int_\omega^{x_i}\psi^{-1}(s)\,ds .$$
--
--   The file also defines the open orthant $(0,+\infty)^d$, the negative entropy $F(x)=\sum_i x_i\ln x_i-\sum_i x_i$, and the $0$-potential $\psi(x)=(-x)^{-q}$ on $(-\infty,0)$ used in Theorem 5.7.
--
--   With $\psi(x)=e^x$ the function $F_\psi$ reduces to the negative entropy. Other $0$-potentials, such as $(-x)^{-q}$, give the sharper semi-bandit bound of Theorem 5.7.
--
--   **Formalization Note** The endpoint $a$ is an `EReal` different from $-\infty$. "$\lim_{x\to a}\psi(x)=+\infty$" is the left limit at $a$ when $a$ is finite and the limit at $+\infty$ when $a=+\infty$. $\psi^{-1}$ is `Function.invFunOn ψ (-∞, a)`, the true inverse on $(\omega,+\infty)$. The integrability condition is a finite lower Lebesgue integral. $F_\psi$ is defined on all of $[\omega,+\infty)^d$ (the integral is $0$ at $x_i=\omega$), which is the continuous extension of the book's formula on $D=(\omega,+\infty)^d$. In the negative entropy, Lean's `Real.log 0 = 0` gives the convention $0\ln0=0$.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 79, Definition 5.4; p. 78, Theorem 5.6 (negative entropy); p. 80, Theorem 5.7 (ψ(x) = (−x)^{−q})

import Mathlib

open Filter Topology

namespace RegretBandits.Linear

/-- The domain `(-∞, a)` of a potential, for `a ∈ ℝ ∪ {+∞}` (encoded as `a : EReal`, `a ≠ ⊥`). -/
def potDom (a : EReal) : Set ℝ := {x | (x : EReal) < a}

/-- The inverse `ψ⁻¹` of a potential `ψ : (-∞, a) → ℝ`. For an `ω`-potential, `ψ` is a continuous
increasing bijection of `(-∞, a)` onto `(ω, +∞)`, so on `(ω, +∞)` this is the genuine inverse
function; outside `(ω, +∞)` its value is an arbitrary junk value and is never used. -/
noncomputable def potInv (ψ : ℝ → ℝ) (a : EReal) (s : ℝ) : ℝ :=
  Function.invFunOn ψ (potDom a) s

/-- Definition 5.4 (Bubeck, Cesa-Bianchi, arXiv:1204.5721v2, p. 79): for `ω ≥ 0`, a function
`ψ : (-∞, a) → ℝ*₊`, `a ∈ ℝ ∪ {+∞}`, is an **`ω`-potential** if it is convex, continuously
differentiable, `lim_{x → -∞} ψ(x) = ω`, `lim_{x → a} ψ(x) = +∞`, `ψ' > 0`, and
`∫_ω^{ω+1} |ψ⁻¹(s)| ds < +∞`. Values of `ψ` outside `(-∞, a)` are irrelevant. -/
structure IsPotential (ω : ℝ) (a : EReal) (ψ : ℝ → ℝ) : Prop where
  nonneg : 0 ≤ ω
  a_ne_bot : a ≠ ⊥
  pos : ∀ x ∈ potDom a, 0 < ψ x
  convexOn : ConvexOn ℝ (potDom a) ψ
  contDiffOn : ContDiffOn ℝ 1 ψ (potDom a)
  tendsto_atBot : Tendsto ψ atBot (𝓝 ω)
  tendsto_left_of_real : ∀ b : ℝ, a = (b : EReal) → Tendsto ψ (𝓝[<] b) atTop
  tendsto_atTop_of_top : a = ⊤ → Tendsto ψ atTop atTop
  deriv_pos : ∀ x ∈ potDom a, 0 < deriv ψ x
  integral_abs_inv_lt_top :
    ∫⁻ s in Set.Ioc ω (ω + 1), ENNReal.ofReal |potInv ψ a s| < ⊤

/-- The function associated with a potential (Definition 5.4, p. 79):
`F_ψ(x) = ∑_{i=1}^d ∫_ω^{x_i} ψ⁻¹(s) ds` on `D̄ = [ω, +∞)^d` (the book defines it on
`D = (ω, +∞)^d`; at `x_i = ω` the integral is `0`, the continuous extension). -/
noncomputable def potentialFn {d : ℕ} (ψ : ℝ → ℝ) (a : EReal) (ω : ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i, ∫ s in ω..x i, potInv ψ a s

/-- The open positive orthant `(0, +∞)^d`, the set `D` of both the negative entropy and of `F_ψ`
for a `0`-potential (pp. 78–79). -/
def posOrthant (d : ℕ) : Set (Fin d → ℝ) := {x | ∀ i, 0 < x i}

/-- The negative entropy `F(x) = ∑ x_i ln x_i - ∑ x_i` (p. 78, Theorem 5.6), on `[0, +∞)^d`;
Lean's `Real.log 0 = 0` gives the convention `0 ln 0 = 0` at the boundary. -/
noncomputable def negEntropy {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  ∑ i, x i * Real.log (x i) - ∑ i, x i

/-- The `0`-potential `ψ(x) = (-x)^{-q}` on `(-∞, 0)` (p. 80, Theorem 5.7), for `q > 1`. -/
noncomputable def powPotential (q : ℝ) (x : ℝ) : ℝ := (-x) ^ (-q)

end RegretBandits.Linear


