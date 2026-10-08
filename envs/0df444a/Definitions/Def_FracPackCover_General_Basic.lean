-- Prove2me | Definitions.Def_FracPackCover_General_Basic
-- name    : FracPackCover_General_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:20.870523+00:00
-- url     : https://prove2.me/theorems/0f3eb26c-e285-4cce-9783-ee6c066759e0
-- title:
--   The GENERAL problem: row values, λ(x), the dual solution, the potential Φ, conditions 𝒢1/𝒢2, the minimizing oracle (10) and the width bound
-- statement:
--   This bundle sets up the **GENERAL problem** of §4: given an arbitrary real $m \times n$ matrix $A$ with rows $a_1,\dots,a_m$, an arbitrary vector $b \in \mathbb R^m$, a positive vector $d \in \mathbb R^m$ (the error scale) and a convex set $P \subseteq \mathbb R^n$, decide whether some $x \in P$ satisfies $Ax \le b$.
--
--   1. **Row values.** $a_i x = \sum_j A_{ij} x_j$.
--   2. **The value $\lambda(x)$.** For $x \in P$, $\lambda(x)$ is the least $\lambda$ with $Ax \le b + \lambda d$, that is
--   $$\lambda(x) = \max_{1 \le i \le m} \frac{a_i x - b_i}{d_i}.$$
--   It may be negative. A point $x \in P$ is an $\varepsilon$-approximate solution when $\lambda(x) \le \varepsilon$, i.e. $Ax \le b + \varepsilon d$.
--   3. **Lagrangean value.** For $y \in \mathbb R^m$, $y^t(Ax - b) = \sum_i y_i (a_i x - b_i)$.
--   4. **Dual solution corresponding to $x$.** For a parameter $\alpha$, $y_i = \frac{1}{d_i} e^{\alpha (a_i x - b_i)/d_i}$.
--   5. **Potential.** $\Phi = y^t d = \sum_i e^{\alpha (a_i x - b_i)/d_i}$.
--   6. **Relaxed optimality conditions.** With $\lambda$ a number, $y$ a dual vector and $C$ a number standing for $C_{\mathcal G}(y) = \min\{y^t A x' - y^t b : x' \in P\}$:
--   $$(\mathcal G1)\ \ \lambda\, y^t d \le 4\, y^t(Ax - b), \qquad (\mathcal G2)\ \ y^t(Ax - b) - C \le \tfrac{\lambda}{5}\, y^t d.$$
--   7. **Subroutine (10).** A map $\mathrm{orc}$ from dual vectors to points is a minimizing oracle for $P$ and $A$ if for every $y \ge 0$, $\mathrm{orc}(y) \in P$ and $\mathrm{orc}(y)$ minimizes $c x$ over $P$ for $c = y^t A$.
--   8. **Width bound.** A number $\rho$ bounds the width of $P$ relative to $Ax \le b$ and $d$ if $|a_i x - b_i| \le \rho\, d_i$ for every $x \in P$ and every $i$; the paper's width is the least such $\rho$, $\rho = \max_i \max_{x \in P} |a_i x - b_i|/d_i$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Constraints are indexed by `Fin m` and coordinates by `Fin n`; `[NeZero m]` makes the maximum defining $\lambda(x)$ nonempty. $\rho$ is taken as any upper bound on the width rather than as a supremum, so every theorem holds in particular for the exact width. (𝒢2) takes $C_{\mathcal G}(y)$ as an argument; the theorems always supply the value at an exact minimizer, so it is the true minimum.
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Tech. Rep. 999 (1992), pp. 23–26, §4: GENERAL problem box and subroutine (10) (p. 23), width ρ (p. 23), (11), (𝒢1), (𝒢2) (p. 24), dual solution (p. 25), Φ (p. 26)

import Mathlib
import Definitions.Def_FracPackCover_Covering_Basic

namespace FracPackCover.General

/-!
# The GENERAL problem `∃? x ∈ P, Ax ≤ b` (Plotkin–Shmoys–Tardos, Cornell ORIE TR 999, §4, pp. 23–25)

Data: an arbitrary real `m × n` matrix `A`, an arbitrary vector `b ∈ ℝ^m`, a positive vector
`d ∈ ℝ^m` (the error scale), and a convex set `P ⊆ ℝ^n`. Constraints are indexed by `Fin m`,
coordinates by `Fin n`. No sign hypothesis is placed on `A`, `b` or `P`.
-/

/-- `λ(x) = max_i (a_i x − b_i)/d_i`, the least `λ` with `Ax ≤ b + λd` (p. 24). It may be
negative. Defined for `m ≥ 1` (a nonempty maximum). -/
noncomputable def lam {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => (FracPackCover.Covering.rowVal A x i - b i) / d i)

/-- The Lagrangean value `y^t(Ax − b) = ∑_i y_i (a_i x − b_i)`. -/
def lagr {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (y : Fin m → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i, y i * (FracPackCover.Covering.rowVal A x i - b i)

/-- The dual solution corresponding to `x` (p. 25): `y_i = (1/d_i) e^{α(a_i x − b_i)/d_i}`. -/
noncomputable def dualVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ) (α : ℝ)
    (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => (1 / d i) * Real.exp (α * (FracPackCover.Covering.rowVal A x i - b i) / d i)

/-- The potential function `Φ = y^t d = ∑_i e^{α(a_i x − b_i)/d_i}` (p. 26). -/
noncomputable def potential {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ) (α : ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i, Real.exp (α * (FracPackCover.Covering.rowVal A x i - b i) / d i)

/-- Relaxed optimality condition (𝒢1) (p. 24): `λ y^t d ≤ 4 y^t(Ax − b)`. -/
def G1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ) (x : Fin n → ℝ)
    (lamv : ℝ) (y : Fin m → ℝ) : Prop :=
  lamv * ∑ i, y i * d i ≤ 4 * lagr A b y x

/-- Relaxed optimality condition (𝒢2) (p. 24): `y^t(Ax − b) − C ≤ (λ/5) y^t d`, where `C` is the
value `C_𝒢(y) = min(y^t A x' − y^t b : x' ∈ P)` (supplied as a number; every use below passes
the value at an exact minimizer). -/
def G2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ) (x : Fin n → ℝ)
    (lamv : ℝ) (y : Fin m → ℝ) (C : ℝ) : Prop :=
  lagr A b y x - C ≤ lamv / 5 * ∑ i, y i * d i

/-- Subroutine (10) (p. 23): for every `y ≥ 0`, `orc y ∈ P` minimizes `c x = y^t A x` over `P`. -/
def IsMinOracle {m n : ℕ} (P : Set (Fin n → ℝ)) (A : Matrix (Fin m) (Fin n) ℝ)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ y : Fin m → ℝ, 0 ≤ y →
    orc y ∈ P ∧ ∀ x' ∈ P, ∑ i, y i * FracPackCover.Covering.rowVal A (orc y) i ≤ ∑ i, y i * FracPackCover.Covering.rowVal A x' i

/-- `ρ` is an upper bound on the width `max_i max_{x∈P} |a_i x − b_i|/d_i` (p. 23):
`|a_i x − b_i| ≤ ρ d_i` for every `x ∈ P` and every row `i`. -/
def WidthBound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (ρ : ℝ) : Prop :=
  ∀ x ∈ P, ∀ i, |FracPackCover.Covering.rowVal A x i - b i| ≤ ρ * d i

end FracPackCover.General


