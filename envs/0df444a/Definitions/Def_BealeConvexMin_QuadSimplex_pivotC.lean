-- Prove2me | Definitions.Def_BealeConvexMin_QuadSimplex_pivotC
-- name    : BealeConvexMin_QuadSimplex_pivotC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:30:40.221609+00:00
-- url     : https://prove2.me/theorems/aec2ca02-4719-4539-ab93-6940d5fd4c53
-- title:
--   Beale (1955), eqs. (3.4)–(3.6): the transformed quadratic form after a change of nonbasic variable
-- statement:
--   Beale represents a quadratic objective in the current nonbasic variables $z_1,\dots,z_N$ (where $N=n-m$) by a symmetric matrix $(c_{kl})_{k,l=0}^{N}$,
--   $$C=\sum_{k=0}^{N}\sum_{l=0}^{N} c_{kl}\,z_k z_l,\qquad z_0=1 \tag{3.1}$$
--   so that $c_{00}$ is the value of $C$ at the associated solution and $c_{k0}$ is half the linear coefficient of $z_k$. This definition file fixes the algebra of one change of nonbasic variable.
--
--   The nonbasic variables live in fixed **slots** $0,1,\dots,N$, slot $0$ holding the constant $z_0=1$. When $z_p$ leaves the nonbasic set, the variable that replaces it (the paper's $z_q$) is stored in the same slot $p$. Suppose the new variable is
--   $$z_q=d_0+\sum_{l=1}^{N} d_l z_l .\tag{3.3}$$
--   Solving for $z_p$ (possible when $d_p\neq 0$) gives $z_p=e_0+e_q z_q+\sum_{l\neq p}e_l z_l$ with
--   $$e_q=\frac{1}{d_p},\qquad e_l=-\frac{d_l}{d_p}\quad(l\neq p,\ l=0\text{ included}). \tag{3.4}$$
--   Since $z_q$ sits in slot $p$, $e_q$ is stored as entry $p$ of the vector $e$.
--
--   1. **Substitution into a linear form.** A form $\sum_l v_l z_l$ becomes $\sum_l v'_l z'_l$ with $v'_p=v_p e_p$ and $v'_l=v_l+v_p e_l$ for $l\neq p$. Applied to the row $(a_{h0},\dots,a_{hN})$ of a restricted variable $x_h$, this is the transformed row of the tableau (2.3).
--   2. **Eq. (3.5).** Substituting (3.4) for $z_p$ inside each bracket of $C$: $c'_{kq}=c_{kp}e_q$ and $c'_{kl}=c_{kl}+c_{kp}e_l$ for $l\neq q$.
--   3. **Eq. (3.6).** Substituting for the remaining $z_p$: $c''_{ql}=c'_{pl}e_q$ and $c''_{kl}=c'_{kl}+c'_{pl}e_k$ for $k\neq q$.
--
--   The matrix $(c''_{kl})$ is the coefficient matrix of $C$ in the new nonbasic variables. The file also defines the value $C(z)=\sum_{k,l}c_{kl}z_kz_l$ of (3.1) at a point $z$.
--
--   **Formalization Note** Indices run over `Fin (N+1)`. The paper's index $q$ of the new variable is the slot $p$ here, so the paper's conditions "$k\neq q$", "$l\neq q$" read "$k\neq p$", "$l\neq p$". The matrix $(c''_{kl})$ is computed literally from (3.5) and then (3.6), not from the closed form (3.7), which is a separate theorem. Lean's $1/0=0$ makes $e$ junk when $d_p=0$; every theorem that needs $d_p\neq0$ assumes it.
-- source:
--   Beale, On Minimizing a Convex Function Subject to Linear Inequalities, J. R. Statist. Soc. B 17(2), 1955, https://doi.org/10.1111/j.2517-6161.1955.tb00191.x, pp. 175–176 (PDF pp. 3–4), eqs. (3.1), (3.3), (3.4), (3.5), (3.6)

import Mathlib

namespace BealeConvexMin.QuadSimplex

/-!
Beale (1955), §3, pp. 175–176, eqs. (3.3)–(3.6): the change of nonbasic variable in a quadratic
function `C = Σ_{k,l=0}^{N} c_kl z_k z_l` with `z_0 = 1` (eq. (3.1), `N = n - m`).

Slot convention: the nonbasic variables occupy the fixed slots `Fin (N+1)`, slot `0` holding the
constant `z_0 = 1`. A pivot at slot `p` removes the old `z_p` and puts the new nonbasic variable,
which the paper calls `z_q`, **into slot `p`**. Hence the paper's index `q` in (3.4)–(3.7) is
slot `p` after the pivot, and the paper's "`l ≠ q`", "`k ≠ q`" read "`l ≠ p`", "`k ≠ p`" here.
-/

/-- Eq. (3.4). If the new nonbasic variable is `z_q = d_0 + Σ_{l=1}^{N} d_l z_l` (eq. (3.3)), then
`z_p = e_0 + e_q z_q + Σ_{l ≠ p} e_l z_l` with `e_q = 1/d_p` and `e_l = -d_l/d_p` for `l ≠ p`
(including `l = 0`: `e_0 = -d_0/d_p`). Since `z_q` is stored in slot `p`, `e_q` is entry `p`. -/
noncomputable def pivotE {N : ℕ} (d : Fin (N + 1) → ℝ) (p : Fin (N + 1)) : Fin (N + 1) → ℝ :=
  fun l => if l = p then 1 / d p else -d l / d p

/-- Substitution of `z_p = Σ_l e_l z'_l` (with `z'_0 = 1`, and `z'_p` the new variable in slot `p`)
into the linear form `Σ_l v_l z_l`: the coefficient of the new slot `p` is `v_p e_p`, and every
other coefficient becomes `v_l + v_p e_l`. This is the rule (3.5) for one row, and the rule by
which "the transformed `a_kl` are derived from the old `a_hl`" (p. 176). -/
def substVec {N : ℕ} (v e : Fin (N + 1) → ℝ) (p : Fin (N + 1)) : Fin (N + 1) → ℝ :=
  fun l => if l = p then v p * e p else v l + v p * e l

/-- The new row of a restricted variable `x_h = Σ_l a_hl z_l` after the pivot at slot `p` defined by
the new nonbasic variable with coefficients `d` (eq. (3.3)). -/
noncomputable def pivotRow {N : ℕ} (r : Fin (N + 1) → ℝ) (p : Fin (N + 1))
    (d : Fin (N + 1) → ℝ) : Fin (N + 1) → ℝ :=
  substVec r (pivotE d p) p

/-- Eq. (3.5): `c'_kq = c_kp e_q` and `c'_kl = c_kl + c_kp e_l` for `l ≠ q` (with `q` = slot `p`):
the substitution of (3.4) for `z_p` inside the brackets, i.e. in every row of `(c_kl)`. -/
noncomputable def pivotCPrime {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (p : Fin (N + 1)) (d : Fin (N + 1) → ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun k l =>
    if l = p then c k p * pivotE d p p else c k l + c k p * pivotE d p l

/-- Eq. (3.6): `c''_ql = c'_pl e_q` and `c''_kl = c'_kl + c'_pl e_k` for `k ≠ q` (with `q` = slot
`p`): the substitution of (3.4) for the remaining `z_p`, the one multiplying each bracket. The
matrix `(c''_kl)` is the transformed `(c_kl)` after the pivot at slot `p` with new nonbasic
variable (3.3) of coefficients `d`. -/
noncomputable def pivotC {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (p : Fin (N + 1)) (d : Fin (N + 1) → ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun k l =>
    if k = p then pivotCPrime c p d p l * pivotE d p p
    else pivotCPrime c p d k l + pivotCPrime c p d p l * pivotE d p k

/-- The value `C = Σ_{k=0}^{N} Σ_{l=0}^{N} c_kl z_k z_l` of eq. (3.1) at the point `z`
(the caller sets `z 0 = 1`). -/
def quadValue {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (z : Fin (N + 1) → ℝ) : ℝ :=
  ∑ k, ∑ l, c k l * z k * z l

end BealeConvexMin.QuadSimplex


