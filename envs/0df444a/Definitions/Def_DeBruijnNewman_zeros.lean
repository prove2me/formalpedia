-- Prove2me | Definitions.Def_DeBruijnNewman_zeros
-- name    : DeBruijnNewman_zeros
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-13T13:15:05.379248+00:00
-- url     : https://prove2.me/theorems/b82f8ef3-ab27-4ee4-8719-dc096ec287fd
-- title:
--   Zeros of $H_t$: enumeration, counting function and classical locations
-- statement:
--   Notation and bookkeeping for the zeros of $H_t$, following Section 1.1 and Section 3 of the source.
--
--   **Modified logarithm.** $\log_+ x := \log(2 + |x|)$, which is positive for every real $x$.
--
--   **Main term of the counting formula.** $\Psi(T) := \frac{T}{4\pi}\log\frac{T}{4\pi} - \frac{T}{4\pi}$ (equation (38); the traditional lower-order term $-7/8$ is discarded, as in the source).
--
--   **Classical locations.** A function $\xi : \mathbb{Z} \to \mathbb{R}$ is a family of classical locations when $\xi_j > 1$ and $\Psi(\xi_j) = j$ for every $j \ge 1$, and $\xi_{-j} = -\xi_j$ for every $j$ (equation (42)). For each $j \ge 1$ the solution of $\Psi(\xi) = j$ in $(1,\infty)$ is unique, so the predicate pins the family down; it is used as a hypothesis rather than as a choice function.
--
--   **Zero enumerations.** A function $x : \mathbb{Z} \to \mathbb{R}$ enumerates the zeros of $H_t$ when $x_{-j} = -x_j$ for all $j$, $0 < x_1$, the map $j \mapsto x_j$ is strictly increasing on the positive integers, and a complex number $z$ satisfies $H_t(z) = 0$ exactly when $z = x_j$ for some nonzero integer $j$. This encodes the facts recorded in Section 1.1 for $\Lambda < t \le 0$: the zeros are real, simple, symmetric about the origin, avoid the origin, and are listed as $0 < x_1(t) < x_2(t) < \cdots$.
--
--   **Counting function.** $N_t(I)$ is the number of real points of $I$ at which $H_t$ vanishes, as a cardinality of a set of reals (zero by convention if that set is infinite).
--
--   **Discrete intervals.** $[a,b]_{\mathbb{Z}^*}$ is the finite set of nonzero integers $j$ with $a \le j \le b$.
-- source:
--   B. Rodgers and T. Tao, "The de Bruijn-Newman constant is non-negative", Forum of Mathematics, Pi 8 (2020), e6, https://doi.org/10.1017/fmp.2020.6, Section 1.1 (pp. 6-7) and Section 3, equations (38), (42), pp. 20-21

import Mathlib
import Definitions.Def_DeBruijnNewman_core

open MeasureTheory Set

namespace DeBruijnNewman

/-- The modified logarithm `log₊ x = log (2 + |x|)` of Rodgers–Tao, Section 1.1. -/
noncomputable def logPlus (x : ℝ) : ℝ := Real.log (2 + |x|)

/-- The main term `Ψ(T) = (T / 4π) log (T / 4π) − T / 4π` of the
Riemann–von Mangoldt formula, Rodgers–Tao equation (38). -/
noncomputable def Psi (T : ℝ) : ℝ :=
  T / (4 * Real.pi) * Real.log (T / (4 * Real.pi)) - T / (4 * Real.pi)

/-- `xi` is the family of classical locations `ξ_j` of Rodgers–Tao,
equation (42): for `j ≥ 1`, `ξ_j` is the solution in `(1, ∞)` of `Ψ(ξ_j) = j`,
extended to negative indices by `ξ_{−j} = −ξ_j`. -/
def IsClassicalLocations (xi : ℤ → ℝ) : Prop :=
  (∀ j : ℤ, 0 < j → 1 < xi j ∧ Psi (xi j) = (j : ℝ)) ∧ ∀ j : ℤ, xi (-j) = -xi j

/-- `x` enumerates the zeros `(x_j(t))_{j ∈ ℤ*}` of `H t` as in Rodgers–Tao,
Section 1.1: the zeros of `H t` are exactly the real numbers `x j` with
`j` a nonzero integer, they satisfy `0 < x 1 < x 2 < ⋯`, and
`x (−j) = −x j`. -/
def IsZeroEnumeration (t : ℝ) (x : ℤ → ℝ) : Prop :=
  (∀ j : ℤ, x (-j) = -x j) ∧ 0 < x 1 ∧
  (∀ j k : ℤ, 0 < j → j < k → x j < x k) ∧
  ∀ z : ℂ, H t z = 0 ↔ ∃ j : ℤ, j ≠ 0 ∧ z = ((x j : ℝ) : ℂ)

/-- `N_t(I)`, the number of zeros of `H t` lying in a set `I` of reals. -/
noncomputable def zeroCount (t : ℝ) (I : Set ℝ) : ℕ :=
  {y : ℝ | y ∈ I ∧ H t ((y : ℝ) : ℂ) = 0}.ncard

/-- The discrete interval `[a, b]_{ℤ*} = {j ∈ ℤ : j ≠ 0, a ≤ j ≤ b}`. -/
noncomputable def discreteIcc (a b : ℤ) : Finset ℤ := (Finset.Icc a b).erase 0

end DeBruijnNewman


