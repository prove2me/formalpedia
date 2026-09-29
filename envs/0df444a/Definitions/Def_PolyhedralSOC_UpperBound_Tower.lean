-- Prove2me | Definitions.Def_PolyhedralSOC_UpperBound_Tower
-- name    : PolyhedralSOC_UpperBound_Tower
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:45:31.193063+00:00
-- url     : https://prove2.me/theorems/9559bf8b-d84f-4fd8-a5ab-a0c6f3a69c99
-- title:
--   The tower of variables and the systems (5) and (6)
-- statement:
--   Let $k=2^\theta$. The **tower of variables** splits the $k$ variables $y_1,\dots,y_k$ ("generation 0") into pairs $(y_1,y_2),\dots,(y_{k-1},y_k)$ and attaches to each pair a successor variable of generation 1; the $2^{\theta-1}$ variables of generation 1 are again paired, and so on, until generation $\theta$, whose only variable is $t$. Write $y_i^\ell$ for the $i$-th variable of generation $\ell$ ($i=1,\dots,2^{\theta-\ell}$), so that $y_i^0\equiv y_i$, $y_1^\theta\equiv t$, and the parents of $y_i^\ell$ are $y_{2i-1}^{\ell-1}$ and $y_{2i}^{\ell-1}$.
--
--   Three notions are defined:
--   1. a tower is **attached to** $(y,t)$ if its generation $0$ equals $y$ and its generation $\theta$ equals $t$;
--   2. the tower solves **system (5)** if
--   $$\sqrt{[y_{2i-1}^{\ell-1}]^2+[y_{2i}^{\ell-1}]^2}\le y_i^\ell,\qquad i=1,\dots,2^{\theta-\ell},\ \ell=1,\dots,\theta;$$
--   3. given for each $\ell$ a linear map $\Pi_\ell:\mathbb R^2\times\mathbb R\times\mathbb R^{p_\ell}\to\mathbb R^{q_\ell}$, the tower together with auxiliary vectors $u_i^\ell\in\mathbb R^{p_\ell}$ solves **system (6)** if
--   $$\Pi_\ell\big(y_{2i-1}^{\ell-1},y_{2i}^{\ell-1},y_i^\ell,u_i^\ell\big)\ge0,\qquad i=1,\dots,2^{\theta-\ell},\ \ell=1,\dots,\theta.$$
--
--   These systems reduce a conic quadratic constraint of dimension $k+1$ to constraints of dimension 3.
--
--   **Formalization Note** A tower is a function `Y : ℕ → ℕ → ℝ` with `Y ℓ i` $=y_{i+1}^\ell$ (0-based index), so the parents of `Y ℓ i` are `Y (ℓ-1) (2i)` and `Y (ℓ-1) (2i+1)`; only entries with $\ell\le\theta$ and $i<2^{\theta-\ell}$ are constrained. Auxiliary vectors are `U ℓ i : Fin (p ℓ) → ℝ`. $\mathbb R^2$ is `Fin 2 → ℝ` and the pair of parents is `![Y (ℓ-1) (2i), Y (ℓ-1) (2i+1)]`.
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), §2, pp. 198–199, "Tower of variables", Eqs. (5) and (6)

import Mathlib
import Definitions.Def_PolyhedralSOC_Shared_LorentzCone

namespace PolyhedralSOC.UpperBound

/-- The "tower of variables" of Ben-Tal & Nemirovski, *On Polyhedral Approximations of the
Second-Order Cone*, Math. Oper. Res. 26(2):193–205 (2001), §2, p. 198 (PDF p. 6), for
`k = 2^θ`. A tower is a family `Y ℓ i` of reals; `Y ℓ i` is the paper's `y_{i+1}^ℓ`
(0-based index `i`), and generation `ℓ ∈ {0, …, θ}` consists of the `2^(θ-ℓ)` variables
`Y ℓ 0, …, Y ℓ (2^(θ-ℓ) - 1)`; entries outside this range are never constrained.
`IsTowerOf θ y t Y` says the tower is attached to `(y, t)`: generation `0` is the original
vector `y` (`y_i^0 ≡ y_i`) and the only variable of generation `θ` is `t` (`y_1^θ ≡ t`). -/
def IsTowerOf (θ : ℕ) (y : Fin (2 ^ θ) → ℝ) (t : ℝ) (Y : ℕ → ℕ → ℝ) : Prop :=
  (∀ i : Fin (2 ^ θ), Y 0 i = y i) ∧ Y θ 0 = t

/-- The system (5) of Ben-Tal & Nemirovski 2001, §2, p. 199 (PDF p. 7):
`√([y_{2i−1}^{ℓ−1}]² + [y_{2i}^{ℓ−1}]²) ≤ y_i^ℓ` for `i = 1, …, 2^{θ−ℓ}`, `ℓ = 1, …, θ`.
With the 0-based index `i` of `IsTowerOf`, the parents of `Y ℓ i` are `Y (ℓ-1) (2i)` and
`Y (ℓ-1) (2i+1)`. -/
def TowerSystem5 (θ : ℕ) (Y : ℕ → ℕ → ℝ) : Prop :=
  ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ θ → ∀ i : ℕ, i < 2 ^ (θ - ℓ) →
    Real.sqrt (Y (ℓ - 1) (2 * i) ^ 2 + Y (ℓ - 1) (2 * i + 1) ^ 2) ≤ Y ℓ i

/-- The system (6) of Ben-Tal & Nemirovski 2001, §2, p. 199 (PDF p. 7): given, for each
generation `ℓ`, a linear map `Ps ℓ : ℝ² × ℝ × ℝ^{p ℓ} → ℝ^{q ℓ}` (meant to be a polyhedral
approximation of `L²`), the linear constraints
`Π_ℓ(y_{2i−1}^{ℓ−1}, y_{2i}^{ℓ−1}, y_i^ℓ, u_i^ℓ) ≥ 0`, `i = 1, …, 2^{θ−ℓ}`, `ℓ = 1, …, θ`,
in the tower variables `Y` and the auxiliary vectors `U ℓ i = u_{i+1}^ℓ` (0-based `i`). -/
def TowerSystem6 (θ : ℕ) (p q : ℕ → ℕ)
    (Ps : (ℓ : ℕ) → (Fin 2 → ℝ) × ℝ × (Fin (p ℓ) → ℝ) →ₗ[ℝ] (Fin (q ℓ) → ℝ))
    (Y : ℕ → ℕ → ℝ) (U : (ℓ : ℕ) → ℕ → Fin (p ℓ) → ℝ) : Prop :=
  ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ θ → ∀ i : ℕ, i < 2 ^ (θ - ℓ) →
    0 ≤ Ps ℓ (![Y (ℓ - 1) (2 * i), Y (ℓ - 1) (2 * i + 1)], Y ℓ i, U ℓ i)

end PolyhedralSOC.UpperBound


