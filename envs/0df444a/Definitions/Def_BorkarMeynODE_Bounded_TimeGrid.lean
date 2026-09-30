-- Prove2me | Definitions.Def_BorkarMeynODE_Bounded_TimeGrid
-- name    : BorkarMeynODE_Bounded_TimeGrid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:47:35.297563+00:00
-- url     : https://prove2.me/theorems/215882f6-7062-4daa-8118-2b418864dbc2
-- title:
--   ODE time grid, blocks $T(j)$, interpolations $\psi$, $\phi_j$ and block solutions $\hat\psi$, $\hat\phi$
-- statement:
--   These are the objects of the paper's proofs, built from the step sizes $a(n)$, a block length $T > 0$ and a sample path of the iterates $X(n)$.
--
--   1. The **ODE time** of step $n$ is $t(0) = 0$, $t(n) = \sum_{i=0}^{n-1} a(i)$.
--   2. The **block indices** are $m(0) = 0$ and $m(j+1) = \min\{k : t(k) > t(m(j)) + T\}$; the **block times** are $T(j) = t(m(j))$, so that $T(j+1) = \min\{t(k) : t(k) > T(j) + T\}$.
--   3. For a sequence $y(n)$, its **piecewise linear interpolation** takes the value $y(n)$ at $t(n)$ and is linear on each $[t(n), t(n+1)]$. The interpolated path $\psi$ interpolates $X(n)$.
--   4. The **scaling parameter** of block $j$ is $r(j) = \max(1, \|X(m(j))\|)$, and $\phi_j$ interpolates $X(n)/r(j)$; it is used on the closed interval $[T(j), T(j+1)]$, where it takes the values $X(n)/r(j)$, $m(j) \le n \le m(j+1)$.
--   5. A function $\hat\phi_j$ is a **block solution of (4.1)** if it is continuous on $[T(j), T(j+1)]$, solves $\dot x = h_{r(j)}(x)$ there (right derivatives on $[T(j), T(j+1))$), and $\hat\phi_j(T(j)) = \phi_j(T(j))$.
--   6. A function $\hat\psi$ is a **piecewise solution of (1.2)** if on every block $[T(j), T(j+1))$ it is continuous, solves $\dot x = h(x)$, and $\hat\psi(T(j)) = \psi(T(j))$.
--
--   The comparison of $\phi_j$ with $\hat\phi_j$ (Lemma 4.7) and of $\psi$ with $\hat\psi$ (Lemma 4.8) is the core of the ODE method under bounded stepsizes.
--
--   **Formalization Note** The minima in item 2 and the choice of interval in item 3 are `sInf`s over $\mathbb N$. They are the intended values whenever the steps are positive and $\sum_n a(n) = \infty$, which assumption (BS) guarantees. Otherwise `sInf ∅ = 0` is a junk value. The solutions $\hat\phi_j$, $\hat\psi$ are characterized by predicates rather than chosen; for a Lipschitz field they are unique on each block.
-- source:
--   Borkar and Meyn, The O.D.E. Method for Convergence of Stochastic Approximation and Reinforcement Learning, SIAM J. Control Optim. 38(2) (2000), p. 450 (t(n), T(n), ψ, ψ̂ in the proof of Theorem 2.2), pp. 460–461 (r(j), φ_j, φ, φ̂ and ODE (4.1))

import Mathlib
import Definitions.Def_BorkarMeynODE_Bounded_ODEStability

namespace BorkarMeynODE.Bounded

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The ODE time of step `n`: `t(0) = 0`, `t(n) = ∑_{i=0}^{n-1} a(i)`. -/
def stepTime (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, a i

/-- The block indices `m(j)`: `m(0) = 0` and `m(j+1)` is the least `k` with
`t(k) > t(m(j)) + T`, so that `T(j+1) = min {t(k) : t(k) > T(j) + T}`. (If `∑ a = ∞`, as under
(BS), the set is nonempty; otherwise `sInf ∅ = 0` is a junk value.) -/
noncomputable def blockIndex (a : ℕ → ℝ) (T : ℝ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => sInf {k : ℕ | stepTime a (blockIndex a T j) + T < stepTime a k}

/-- The block times `T(j) = t(m(j))`. -/
noncomputable def blockTime (a : ℕ → ℝ) (T : ℝ) (j : ℕ) : ℝ :=
  stepTime a (blockIndex a T j)

/-- Piecewise linear interpolation of a sequence `y` on the time grid `t(n)`: for
`t(n) ≤ t < t(n+1)`, `y(n) + ((t - t(n)) / a(n)) (y(n+1) - y(n))`. Here `n` is the least `k`
with `t < t(k+1)`; for positive steps with `∑ a = ∞` and `t ≥ 0` this is the unique `n` with
`t(n) ≤ t < t(n+1)`, and the value at `t(n)` is `y(n)`. -/
noncomputable def linInterp (a : ℕ → ℝ) (y : ℕ → E) (t : ℝ) : E :=
  let n := sInf {k : ℕ | t < stepTime a (k + 1)}
  y n + ((t - stepTime a n) / a n) • (y (n + 1) - y n)

/-- The interpolated path `ψ` of the iterates: `ψ(t(n)) = X(n)`, linear on `[t(n), t(n+1)]`. -/
noncomputable def interpPath {Ω : Type*} (a : ℕ → ℝ) (X : ℕ → Ω → E) (ω : Ω) : ℝ → E :=
  linInterp a (fun n => X n ω)

/-- The scaling parameter `r(j) = max(1, ‖X(m(j))‖)`. -/
noncomputable def scaleFactor {Ω : Type*} (a : ℕ → ℝ) (T : ℝ) (X : ℕ → Ω → E) (j : ℕ)
    (ω : Ω) : ℝ :=
  max 1 ‖X (blockIndex a T j) ω‖

/-- The block-`j` scaled interpolation `φ_j`: `φ_j(t(n)) = X(n) / r(j)` for
`m(j) ≤ n ≤ m(j+1)`, linear in between; it is used on the closed interval `[T(j), T(j+1)]`. -/
noncomputable def phiBlock {Ω : Type*} (a : ℕ → ℝ) (T : ℝ) (X : ℕ → Ω → E) (j : ℕ)
    (ω : Ω) : ℝ → E :=
  linInterp a (fun n => (scaleFactor a T X j ω)⁻¹ • X n ω)

/-- `φh` is the block-`j` solution `φ̂` of (4.1) `ẋ = h_{r(j)}(x)` on the closed interval
`[T(j), T(j+1)]` with initial value `φ̂(T(j)) = φ_j(T(j))`: continuous on the closed interval,
with right derivative `h_{r(j)}(φh t)` at every `t ∈ [T(j), T(j+1))`. -/
def IsPhiHatBlock {Ω : Type*} (h : E → E) (a : ℕ → ℝ) (T : ℝ) (X : ℕ → Ω → E) (j : ℕ)
    (ω : Ω) (φh : ℝ → E) : Prop :=
  φh (blockTime a T j) = phiBlock a T X j ω (blockTime a T j) ∧
    ContinuousOn φh (Set.Icc (blockTime a T j) (blockTime a T (j + 1))) ∧
    ∀ t ∈ Set.Ico (blockTime a T j) (blockTime a T (j + 1)),
      HasDerivWithinAt φh (scaledField h (scaleFactor a T X j ω) (φh t)) (Set.Ici t) t

/-- `ψh` is the piecewise solution `ψ̂` of (1.2) `ẋ = h(x)`: on every block `[T(j), T(j+1))`
it is continuous, solves (1.2) (right derivatives), and starts at `ψ̂(T(j)) = ψ(T(j))`. -/
def IsPsiHat (h : E → E) (a : ℕ → ℝ) (T : ℝ) (ψ ψh : ℝ → E) : Prop :=
  ∀ j : ℕ, ψh (blockTime a T j) = ψ (blockTime a T j) ∧
    ContinuousOn ψh (Set.Ico (blockTime a T j) (blockTime a T (j + 1))) ∧
    ∀ t ∈ Set.Ico (blockTime a T j) (blockTime a T (j + 1)),
      HasDerivWithinAt ψh (h (ψh t)) (Set.Ici t) t

end BorkarMeynODE.Bounded


