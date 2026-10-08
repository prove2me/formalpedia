-- Prove2me | Definitions.Def_ShorNonsmooth_Fejer_PolyakMethod
-- name    : ShorNonsmooth_Fejer_PolyakMethod
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T12:16:18.861979+00:00
-- url     : https://prove2.me/theorems/886200a5-3cd3-42db-a835-5053157a5617
-- title:
--   M-Fejér maps, level sets, Polyak's step (2.32) and the conjugate-subgradient procedure (2.38)
-- statement:
--   Throughout, $E_n$ is the $n$-dimensional Euclidean space with inner product $(x,y)$ and norm $\|x\|$, and $f : E_n \to \mathbb{R}$ is a function finite everywhere.
--
--   A vector $g \in E_n$ is a **subgradient** of $f$ at $x_0$ if $f(x) - f(x_0) \ge (g,\, x - x_0)$ for all $x \in E_n$ (the shared definition `ShorNonsmooth.AlmostDiff.IsSubgradient`, imported here).
--
--   1. For a nonempty set $M \subseteq E_n$, a mapping $\varphi : E_n \to E_n$ is **$M$-Fejér** if
--   $$
--   \varphi(y) = y \quad\text{and}\quad \|\varphi(x) - y\| < \|x - y\| \qquad \text{for all } y \in M,\ x \notin M .
--   $$
--   2. The **level set** of $f$ at level $c \in \mathbb{R}$ is $M(c) = \{x \in E_n : f(x) \le c\}$.
--   3. Fix a **subgradient selection** $g_f : E_n \to E_n$ (in the theorems $g_f(x)$ is required to be a subgradient of $f$ at $x$ for every $x$), a level $c$ and a factor $\gamma$. **Polyak's step** is the map
--   $$
--   \varphi_c(x) = x - \frac{\gamma\,[f(x) - c]}{\|g_f(x)\|^2}\, g_f(x) \qquad (x \notin M(c),\ g_f(x) \neq 0),
--   $$
--   and $\varphi_c(x) = x$ when $x \in M(c)$ or $g_f(x) = 0$: the method stops once it has reached $M(c)$ or a minimum point of $f$.
--   4. For the **conjugate-subgradient procedure** (2.38) of Camerini, Fratta and Maffioli, with target value $f^*$, the stepsize at the point $x_k$ with direction $s_k$ and factor $\gamma_k$ is
--   $$
--   h_k = \frac{[f(x_k) - f^*]\,\gamma_k}{\|s_k\|^2} \quad (s_k \neq 0), \qquad h_k = 0 \quad (s_k = 0),
--   $$
--   and the coefficient of Theorem 2.16, for $\alpha_k \in \mathbb{R}$, is
--   $$
--   \beta_k = \begin{cases} -\alpha_k \dfrac{(s_{k-1}, g_f(x_k))}{\|s_{k-1}\|^2} & \text{if } (s_{k-1}, g_f(x_k)) < 0,\\[4pt] 0 & \text{otherwise.}\end{cases}
--   $$
--
--   These are the objects of all results of Section 2.4: Fejér maps and their fixed-point iterations, Polyak's method $x_{k+1} = \varphi_c(x_k)$, and the procedure $x_{k+1} = x_k - h_k s_k$, $s_0 = g_f(x_0)$, $s_k = g_f(x_k) + \beta_k s_{k-1}$.
--
--   **Formalization Note** $E_n$ is `EuclideanSpace ℝ (Fin n)`. The nonemptiness of $M$ is part of the predicate `IsMFejer`. The stops in `polyakStep` (on $M(c)$, and at $g_f(x) = 0$) and the case $s_k = 0$ in `cfmStepsize` are explicit branches, so no statement relies on Lean's convention $x/0 = 0$. The iterations themselves are not defined as recursive functions: each theorem takes sequences and states the recursion as a hypothesis.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 9, inequality (1.3); p. 36, Definition (2.31); p. 37, formula (2.32) and M(c); p. 41, formula (2.38) and the coefficient of Theorem 2.16

import Mathlib
import Definitions.Def_ShorNonsmooth_AlmostDiff_IsSubgradient

namespace ShorNonsmooth.Fejer

/-- Shor (1985), p. 36, Definition (2.31) (after Eremin [23]): for a nonempty set `M ⊆ E_n`, a
mapping `φ : E_n → E_n` is **`M`-Fejér** if `φ(y) = y` and `‖φ(x) - y‖ < ‖x - y‖` for all
`y ∈ M` and `x ∉ M`. The nonemptiness `M ≠ ∅` of the definition is part of the predicate. -/
def IsMFejer {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  M.Nonempty ∧ (∀ y ∈ M, φ y = y) ∧ ∀ y ∈ M, ∀ x ∉ M, ‖φ x - y‖ < ‖x - y‖

/-- Shor (1985), p. 37: the **level set** `M(c) = {x ∈ E_n : f(x) ≤ c}`. -/
def levelSet {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (c : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | f x ≤ c}

/-- Shor (1985), p. 37, formula (2.32): **Polyak's step** with level `c` and relaxation factor
`γ`, for a subgradient selection `g` (`g x` a subgradient of `f` at `x`):
`φ_c(x) = x - γ [f(x) - c] / ‖g(x)‖² · g(x)`.
On `M(c)` the book sets `φ_c(y) = y` (p. 37), i.e. the iteration stops there; the step also
stops (returns `x`) when `g(x) = 0`, i.e. at a minimum point of `f`, where the book's formula
would divide by zero. Nothing relies on Lean's convention `x / 0 = 0`. -/
noncomputable def polyakStep {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (c γ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  if f x ≤ c ∨ g x = 0 then x
  else x - (γ * (f x - c) / ‖g x‖ ^ 2) • g x

/-- Shor (1985), p. 41, formula (2.38): the stepsize `h_k = [f(x_k) - f*] γ_k / ‖s_k‖²` of the
Camerini–Fratta–Maffioli procedure, at the point `x = x_k` with direction `s = s_k`, target value
`fstar = f*` and factor `γk = γ_k`. When `s_k = 0` the book's formula is undefined; the step is then
`0` (the procedure stays at `x_k`), stated explicitly rather than through `x / 0 = 0`. -/
noncomputable def cfmStepsize {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (fstar γk : ℝ)
    (x s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if s = 0 then 0 else (f x - fstar) * γk / ‖s‖ ^ 2

/-- Shor (1985), p. 41, the coefficient of Theorem 2.16:
`β_k = -α_k (s_{k-1}, g_f(x_k)) / ‖s_{k-1}‖²` if `(s_{k-1}, g_f(x_k)) < 0`, and `β_k = 0`
otherwise; here `sprev = s_{k-1}`, `gk = g_f(x_k)`, `αk = α_k`. (In the first case
`s_{k-1} ≠ 0`, so no division by zero occurs.) -/
noncomputable def cfmBeta {n : ℕ} (αk : ℝ) (sprev gk : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if inner ℝ sprev gk < 0 then -αk * inner ℝ sprev gk / ‖sprev‖ ^ 2 else 0

end ShorNonsmooth.Fejer


