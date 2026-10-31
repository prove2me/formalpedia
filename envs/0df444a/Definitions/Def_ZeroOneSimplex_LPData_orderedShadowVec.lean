-- Prove2me | Definitions.Def_ZeroOneSimplex_LPData_orderedShadowVec
-- name    : ZeroOneSimplex_LPData_orderedShadowVec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:55.960008+00:00
-- url     : https://prove2.me/theorems/03c6383c-5f6c-412c-bbea-659a368ac0a0
-- title:
--   The Ordered Shadow vector $v$, the index function $f$ and $\kappa_j$
-- statement:
--   For an LP of form (1), let $c^*=\|c\|_1+2$ where $\|c\|_1=\sum_i|c_i|$. For an initial vertex $x^0$ of $P$, the **Ordered Shadow vector** is
--   $$
--   v(k)=(-1)^{x^0(k)}(c^*)^k,\qquad k=1,\dots,n.
--   $$
--
--   The **index function** of Lemma 5 is $f(u)=\max(\{k : u(k)\ne x^0(k)\}\cup\{0\})$, so $f(u)=0$ exactly when $u=x^0$.
--
--   For points $x,u^0,u^1$ the **coefficients of Claim 4** are
--   $$
--   \kappa_j=\sigma_j\big[c^\top(u^0-x)(u^1(j)-x(j))-c^\top(u^1-x)(u^0(j)-x(j))\big],\qquad \sigma_j=(-1)^{x^0(j)}.
--   $$
--
--   **Formalization Note** Coordinates are `Fin n`; the paper's coordinate $k$ is `k.val + 1`, so exponents, $f$ and the index $j$ of $\kappa_j$ are 1-based (`at1` reads the 1-based coordinate). The paper states $\kappa_j$ after the change of coordinates $x^0=0$, where $\sigma_j=1$.
-- source:
--   Black, De Loera, Kafer, Sanità, On the Simplex method for 0/1 polytopes, arXiv:2111.14050v1, Definition 5, p.16 (c*, v); Lemma 5, p.17 (f); Claim 4, p.19 (κ_j)

import Mathlib
import Definitions.Def_ZeroOneSimplex_LPData

set_option autoImplicit false

namespace ZeroOneSimplex

namespace LPData

variable {n m p : ℕ} (L : LPData n m p)

/-- The constant `c* = ‖c‖₁ + 2` of Definition 5 (arXiv:2111.14050v1, p.16), with
`‖c‖₁ = Σ_i |c_i|`. -/
def cStar : ℝ := (∑ i, |L.c i|) + 2

/-- **The auxiliary vector of the Ordered Shadow rule** (arXiv:2111.14050v1, Definition 5,
p.16): for the initial extreme point `x⁰`, `v(k) = (−1)^{x⁰(k)} (c*)^k` for `k = 1, …, n`.

**Formalization Note.** Coordinates are `Fin n`, so the paper's coordinate `k` is
`k.val + 1`, and the exponent is `k.val + 1`. `x⁰` is a 0/1 vector, and the sign
`(−1)^{x⁰(k)}` is written `if x⁰ k = 0 then 1 else −1`. -/
noncomputable def orderedShadowVec (x0 : Fin n → ℝ) : Fin n → ℝ :=
  fun k => (if x0 k = 0 then (1 : ℝ) else -1) * L.cStar ^ (k.val + 1)

end LPData

/-- The coordinate `x(j)` with the paper's **1-based** index `j ∈ {1, …, n}`; it is `0` for
`j = 0` or `j > n` (never used there). -/
noncomputable def at1 {n : ℕ} (x : Fin n → ℝ) (j : ℕ) : ℝ :=
  if h : 1 ≤ j ∧ j ≤ n then x ⟨j - 1, by omega⟩ else 0

/-- The sign `σ_j = (−1)^{x⁰(j)}` of the 1-based coordinate `j`, for a 0/1 vector `x⁰`. -/
noncomputable def sgnAt {n : ℕ} (x0 : Fin n → ℝ) (j : ℕ) : ℝ :=
  if at1 x0 j = 0 then 1 else -1

/-- **The index function `f`** of Lemma 5 (arXiv:2111.14050v1, p.17):
`f(u) = max({k : u(k) − x⁰(k) ≠ 0} ∪ {0})`, with 1-based coordinates `k ∈ {1, …, n}`; so
`f(u) = 0` iff `u = x⁰`. -/
noncomputable def fIndex {n : ℕ} (x0 u : Fin n → ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun k : Fin n => u k ≠ x0 k)).sup (fun k => k.val + 1)

/-- **The coefficient `κ_j`** of Claim 4 (arXiv:2111.14050v1, p.19), with the 1-based index `j`:
`κ_j = σ_j [cᵀ(u⁰ − x)(u¹(j) − x(j)) − cᵀ(u¹ − x)(u⁰(j) − x(j))]`.

**Formalization Note.** The paper states Claims 1–4 after the change of coordinates `x⁰ = 0`
(p.19), where `σ_j = (−1)^{x⁰(j)} = 1`. Here no change of coordinates is made, so the sign
`σ_j` of `v(j)` appears as a factor; for `x⁰ = 0` this is the printed `κ_j`. -/
noncomputable def kappa {n : ℕ} (c x0 x u0 u1 : Fin n → ℝ) (j : ℕ) : ℝ :=
  sgnAt x0 j * ((c ⬝ᵥ (u0 - x)) * (at1 u1 j - at1 x j) - (c ⬝ᵥ (u1 - x)) * (at1 u0 j - at1 x j))

end ZeroOneSimplex


