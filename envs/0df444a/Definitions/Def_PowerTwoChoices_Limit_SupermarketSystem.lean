-- Prove2me | Definitions.Def_PowerTwoChoices_Limit_SupermarketSystem
-- name    : PowerTwoChoices_Limit_SupermarketSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:25.995863+00:00
-- url     : https://prove2.me/theorems/ce791c17-af3b-4749-8074-7e659fe7e846
-- title:
--   The limiting supermarket system: states, system (1), trajectories, the fixed point $\pi$, Definitions 1–2, the potentials $\Phi$ and $L_1$, the expected time and $T_d(\lambda)$
-- statement:
--   In the supermarket model, customers arrive as a Poisson stream of rate $\lambda n$, $\lambda<1$, at $n$ FIFO servers; each customer samples $d$ servers uniformly at random with replacement and joins the one with the fewest customers; service times are exponential with mean $1$. Write $s_i$ for the fraction of queues with at least $i$ customers.
--
--   1. A **state** is a sequence $x=(x_0,x_1,x_2,\dots)$ of reals with $x_0=1$, $x_i\ge 0$ and $x_0\ge x_1\ge x_2\ge\cdots$ (the tails of a distribution of queue lengths; in particular $0\le x_i\le 1$). The **empty state** has $x_0=1$ and $x_i=0$ for $i\ge1$.
--   2. The **limiting system** (1) is
--   $$\frac{ds_i}{dt}=\lambda\,(s_{i-1}^d-s_i^d)-(s_i-s_{i+1})\quad (i\ge 1),\qquad s_0=1 .$$
--   Its right-hand side at a state $x$ is the **drift** $F_i(x)=\lambda(x_{i-1}^d-x_i^d)-(x_i-x_{i+1})$, $i\ge1$.
--   3. A **trajectory** is a map $t\mapsto s(t)$ such that $s(t)$ is a state for every $t\ge0$ and every coordinate $s_i$, $i\ge1$, is differentiable on $[0,\infty)$ (from the right at $t=0$) with $ds_i/dt=F_i(s(t))$.
--   4. The **fixed point** is $\pi_i=\lambda^{(d^i-1)/(d-1)}$, $i\ge0$ (so $\pi_0=1$).
--   5. **Definition 1.** A sequence $(x_i)_{i\ge0}$ decreases doubly exponentially if there are positive constants $N$, $\alpha<1$, $\beta>1$, $\gamma$ with $x_i\le\gamma\,\alpha^{\beta^i}$ for all $i\ge N$.
--   6. **Definition 2.** A potential $\Phi(t)$ converges exponentially (to $0$) if $\Phi(t)\le c_0e^{-\delta t}$ for all $t\ge0$, for some constant $\delta>0$ and a constant $c_0$ which may depend on the state at $t=0$.
--   7. For weights $w_i$, the **potential** $\Phi_w(x)=\sum_{i\ge1}w_i|x_i-\pi_i|$, and the **$L_1$ distance** from the fixed point $\sum_{i\ge1}|x_i-\pi_i|$.
--   8. The **expected time** a customer arriving in state $x$ spends in the system is
--   $$E(x)=\sum_{i\ge1} i\,(x_{i-1}^d-x_i^d),$$
--   since it becomes the $i$-th customer in its queue with probability $x_{i-1}^d-x_i^d$ and then waits for $i$ exponential services.
--   9. The constant
--   $$T_d(\lambda)=\sum_{i=1}^\infty\lambda^{\frac{d^i-d}{d-1}} .$$
--
--   These are the objects of Section 2 of the paper; every theorem of this mission is stated in terms of them.
--
--   **Formalization Note.** $\lambda$ is written `lam`. Exponents are natural numbers: $(d^i-1)/(d-1)=\sum_{k<i}d^k$ and $(d^i-d)/(d-1)=\sum_{1\le k<i}d^k$. In Definition 1, $N$ is a natural number and $\alpha^{\beta^i}$ is the real power. Every infinite series ($\Phi_w$, the $L_1$ distance, $E$, $T_d$) is computed in $[0,\infty]$, so it equals $\infty$ when it diverges; the terms of $E$ are nonnegative at a state. In Definition 2 the constant $c_0$ is real, so the bound also says $\Phi(t)<\infty$. Time is real; values of a trajectory at negative times play no role.
-- source:
--   Mitzenmacher, The Power of Two Choices in Randomized Load Balancing, IEEE Trans. Parallel Distrib. Syst. 12(10), 2001, pp. 1096–1099 and 1103: §2.1 (model, system (1)), §2.2 (fixed point, Definition 1), §2.3 (Definition 2, potentials Φ and D), §2.4 (proof of Corollary 2, T_d), Appendix (F of Lemma 4)

import Mathlib

open scoped ENNReal

namespace PowerTwoChoices.Limit

/-- A **state** of the limiting supermarket system (Mitzenmacher 2001, §2.1, p. 1096):
the vector `x = (x₀, x₁, x₂, …)` of tails `x i = s_i`, the fraction of queues with at least `i`
customers. So `x 0 = 1`, every `x i ≥ 0`, and `x` is nonincreasing in `i` (hence `x i ≤ 1`). -/
def IsState (x : ℕ → ℝ) : Prop :=
  x 0 = 1 ∧ (∀ i, 0 ≤ x i) ∧ Antitone x

/-- The right-hand side of coordinate `i` of the limiting system (1) (p. 1096):
`λ (x_{i-1}^d - x_i^d) - (x_i - x_{i+1})`. It is used only for `i ≥ 1`
(at `i = 0` the natural subtraction gives `i - 1 = 0`; coordinate `0` is the constant `s₀ = 1`).
This is also, coordinate by coordinate, the map `F` of the proof of Lemma 4 (p. 1103). -/
def drift (lam : ℝ) (d : ℕ) (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  lam * (x (i - 1) ^ d - x i ^ d) - (x i - x (i + 1))

/-- A **trajectory** of the limiting system (1) (p. 1096) on the time axis `t ≥ 0`:
`s t` is a state for every `t ≥ 0`, and for every `i ≥ 1` the coordinate `t ↦ s t i` is
differentiable on `[0, ∞)` with derivative `ds_i/dt = λ(s_{i-1}^d - s_i^d) - (s_i - s_{i+1})`.
The derivative is taken within `[0, ∞)`: two-sided at every `t > 0`, one-sided (from the right)
at `t = 0`. Values at negative times are irrelevant. -/
def IsTrajectory (lam : ℝ) (d : ℕ) (s : ℝ → ℕ → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → IsState (s t)) ∧
  ∀ i : ℕ, 1 ≤ i → ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt (fun u => s u i) (drift lam d (s t) i) (Set.Ici 0) t

/-- The **empty system** (p. 1096): `s₀ = 1` and `s_i = 0` for `i ≥ 1`. -/
def emptyState : ℕ → ℝ := fun i => if i = 0 then 1 else 0

/-- The fixed point `π_i = λ^{(d^i - 1)/(d - 1)}` of Lemma 2 (p. 1097), written with the
natural-number exponent `(d^i - 1)/(d - 1) = 1 + d + ⋯ + d^{i-1} = ∑_{k < i} d^k`
(so `π₀ = λ⁰ = 1`). -/
def fixedPoint (lam : ℝ) (d : ℕ) (i : ℕ) : ℝ :=
  lam ^ (∑ k ∈ Finset.range i, d ^ k)

/-- Definition 1 (p. 1097) with its constants made explicit: `N`, `α`, `β`, `γ` are positive
constants with `α < 1`, `β > 1`, and `x_i ≤ γ α^{β^i}` for all `i ≥ N`. Here `N` is a natural
number and `α^{β^i}` is the real power. -/
def IsDoublyExpBound (N : ℕ) (α β γ : ℝ) (x : ℕ → ℝ) : Prop :=
  0 < N ∧ 0 < α ∧ α < 1 ∧ 1 < β ∧ 0 < γ ∧ ∀ i : ℕ, N ≤ i → x i ≤ γ * α ^ (β ^ i)

/-- Definition 1 (p. 1097): the sequence `(x_i)` **decreases doubly exponentially** if there
exist positive constants `N`, `α < 1`, `β > 1`, `γ` with `x_i ≤ γ α^{β^i}` for `i ≥ N`. -/
def DecreasesDoublyExponentially (x : ℕ → ℝ) : Prop :=
  ∃ (N : ℕ) (α β γ : ℝ), IsDoublyExpBound N α β γ x

/-- Definition 2 (p. 1097): a potential `Φ : [0, ∞) → [0, ∞]` **converges exponentially** (to
`0`) if `Φ(t) ≤ c₀ e^{-δ t}` for all `t ≥ 0`, for some constant `δ > 0` and some constant `c₀`
(which may depend on the trajectory). Since `c₀` is a real number, the bound also forces
`Φ(t) < ∞` for every `t ≥ 0`. -/
def ConvergesExponentially (Φ : ℝ → ℝ≥0∞) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ c₀ : ℝ, ∀ t : ℝ, 0 ≤ t → Φ t ≤ ENNReal.ofReal (c₀ * Real.exp (-δ * t))

/-- The weighted potential `Φ = ∑_{i ≥ 1} w_i |x_i - π_i|` of Theorem 3 (p. 1098), evaluated at
the state `x`, as an extended nonnegative real (`= ∞` when the series diverges). -/
noncomputable def potential (lam : ℝ) (d : ℕ) (w : ℕ → ℝ) (x : ℕ → ℝ) : ℝ≥0∞ :=
  ∑' i : ℕ, if 1 ≤ i then ENNReal.ofReal (w i * |x i - fixedPoint lam d i|) else 0

/-- The `L₁` distance `∑_{i ≥ 1} |x_i - π_i|` from the fixed point (Corollary 1, p. 1098, where
it is called `d(t)`; renamed here because `d` is the number of choices), as an extended
nonnegative real (`= ∞` when the series diverges). -/
noncomputable def l1Dist (lam : ℝ) (d : ℕ) (x : ℕ → ℝ) : ℝ≥0∞ :=
  ∑' i : ℕ, if 1 ≤ i then ENNReal.ofReal |x i - fixedPoint lam d i| else 0

/-- The expected time an arriving customer spends in the limiting system in state `x`
(proof of Corollary 2, p. 1099): the customer becomes the `i`-th in its queue with probability
`x_{i-1}^d - x_i^d` and then waits for `i` exponential(1) services, so the expected time is
`∑_{i ≥ 1} i (x_{i-1}^d - x_i^d)`. Computed in `[0, ∞]` (`= ∞` when the series diverges); for a
state every term is nonnegative, so `ENNReal.ofReal` clips nothing. The `i = 0` term is `0`. -/
noncomputable def expectedTime (d : ℕ) (x : ℕ → ℝ) : ℝ≥0∞ :=
  ∑' i : ℕ, ENNReal.ofReal ((i : ℝ) * (x (i - 1) ^ d - x i ^ d))

/-- `T_d(λ) = ∑_{i ≥ 1} λ^{(d^i - d)/(d - 1)}` (Corollary 2, p. 1099), in `[0, ∞]`, with the
natural-number exponent `(d^i - d)/(d - 1) = d + d² + ⋯ + d^{i-1} = ∑_{1 ≤ k < i} d^k`
(the `i = 1` term is `λ⁰ = 1`). -/
noncomputable def Td (lam : ℝ) (d : ℕ) : ℝ≥0∞ :=
  ∑' i : ℕ, if 1 ≤ i then ENNReal.ofReal (lam ^ (∑ k ∈ Finset.Ico 1 i, d ^ k)) else 0

end PowerTwoChoices.Limit


