-- Prove2me | Definitions.Def_StochIneqPO_Comparison_iterProd
-- name    : StochIneqPO_Comparison_iterProd
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:05:10.939142+00:00
-- url     : https://prove2.me/theorems/93ae366c-5340-4257-99a5-554e8f958f16
-- title:
--   Eq. (2) — the iterated kernel product $P_1 * p_2 * \cdots * p_n$
-- statement:
--   Let $E_1, E_2, \dots$ be measurable spaces and write $E^{n} = E_1 \times \cdots \times E_n$. Let $P_1$ be a probability measure on $E_1$ and, for $n \ge 2$, let $p_n$ be a stochastic kernel from $E^{n-1}$ to $E_n$. For a kernel $k$ from $E'$ to $E''$ and a measure $P$ on $E'$, $P * k$ denotes the measure on $E' \times E''$ with $(P * k)(A' \times A'') = \int_{A'} k(x, A'')\,P(dx)$. The **iterated product**
--   $$P_1 * p_2 * \cdots * p_n$$
--   is the measure on $E^{n}$ obtained by iterating this construction: it is the joint law of $(X_1, \dots, X_n)$ when $X_1 \sim P_1$ and, for $2 \le i \le n$, $X_i$ is drawn from $p_i(X_1, \dots, X_{i-1}, \cdot)$.
--
--   It is the object compared in Proposition 1, and its projective limit as $n \to \infty$ is the law of the whole sequence in Theorem 2.
--
--   **Formalization Note** Coordinates are 0-based: the paper's $E_i$ ($i \ge 1$) is Lean's `E (i - 1)` and the paper's kernel $p_n$ ($n \ge 2$) is Lean's `p (n - 2) : Kernel (Π i : Iic (n - 2), E i) (E (n - 1))`. Thus the paper's $P_1 * p_2 * \cdots * p_n$ is `iterProd P₁ p (n - 1)`, a measure on `Π i : Iic (n - 1), E i`. The definition is Mathlib's `Kernel.partialTraj p 0 m` applied to $P_1$ (transported to the one-coordinate product); it coincides with the image of Mathlib's Ionescu-Tulcea measure `Kernel.trajMeasure P₁ p` under restriction to the first $m+1$ coordinates.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Sec. 1, p. 899 (definition of P₁ * k) and Proposition 1, eq. (2), p. 902 (PDF pp. 1, 4)

import Mathlib

namespace StochIneqPO.Comparison

open MeasureTheory ProbabilityTheory Finset

/-- The iterated kernel product `P₁ * p₂ * ⋯ * p_{m+1}` of Kamae–Krengel–O'Brien (1977), Sec. 1–2,
eq. (2): the joint law of the first `m + 1` coordinates `(x₀, …, x_m)` obtained by drawing `x₀`
from `P₁` and then, for `n < m`, drawing `x_{n+1}` from `p n (x₀, …, x_n)`.
Index shift: the paper's coordinate `Eᵢ` (`i ≥ 1`) is `E (i - 1)` and the paper's kernel `pₙ`
(`n ≥ 2`) is `p (n - 2)`; the paper's `P₁ * p₂ * ⋯ * pₙ` is `iterProd P₁ p (n - 1)`.
This is Mathlib's `Kernel.partialTraj` started from `P₁`, the finite-horizon restriction of
`Kernel.trajMeasure`. -/
noncomputable def iterProd {E : ℕ → Type*} [∀ n, MeasurableSpace (E n)]
    (P₁ : Measure (E 0)) (p : (n : ℕ) → Kernel (Π i : Iic n, E i) (E (n + 1))) (m : ℕ) :
    Measure (Π i : Iic m, E i) :=
  (Kernel.partialTraj p 0 m) ∘ₘ (P₁.map (MeasurableEquiv.piUnique (fun i : Iic 0 => E i)).symm)

end StochIneqPO.Comparison


