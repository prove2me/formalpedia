-- Prove2me | Definitions.Def_LasserreFC_FinConv_BHC
-- name    : LasserreFC_FinConv_BHC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:32:18.552994+00:00
-- url     : https://prove2.me/theorems/7d6d1d7e-154a-4487-aa6d-ed732987d726
-- title:
--   Conditions 2.2–2.3 (Marshall), pp. 4–5 — the boundary hessian condition
-- statement:
--   This file defines Marshall's **boundary hessian condition** (BHC) for problem (1.1) at a feasible point $u$.
--
--   **Condition 2.2** (local parametrization). The point $u$ is a nonsingular point of $V_{\mathbb R}(h)$ and there are a neighbourhood $\mathcal O$ of $u$ and local parameters $t_1, \dots, t_\ell$ of $V_{\mathbb R}(h) \cap \mathcal O$, together with indices $1 \le \nu_1 < \dots < \nu_r \le m_2$, such that $t_j = g_{\nu_j}$ ($j = 1, \dots, r$) on $V_{\mathbb R}(h) \cap \mathcal O$ and $K \cap \mathcal O$ is defined by $t_1 \ge 0, \dots, t_r \ge 0$.
--
--   **Condition 2.3.** Expand $f$ around $u$ in these parameters as $f = f_0 + f_1 + f_2 + \cdots$ with $f_i$ homogeneous of degree $i$ in $t$. Then
--
--   $$f_1 = a_1 t_1 + \dots + a_r t_r \ \text{ with } a_1, \dots, a_r > 0, \qquad f_2(0, \dots, 0, t_{r+1}, \dots, t_\ell) \succ 0.$$
--
--   Marshall proved that BHC at every global minimizer, together with archimedeanness, yields a Putinar-type representation of $f - f_{\min}$ (Theorem 2.4); Nie's Theorem 3.1 shows that the classical optimality conditions imply BHC.
--
--   **Formalization Note** The parametrization is a map $\Psi$ from an open set $W \ni 0$ of $\mathbb R^\ell$ with $\Psi(0) = u$ that is $C^\infty$, has injective derivative at every point of $W$, and is a homeomorphism of $W$ onto $V_{\mathbb R}(h) \cap \mathcal O$ (this is the reading of "parameterized by uniformizing parameters"; it forces $\ell$ to be the local dimension of $V_{\mathbb R}(h)$ at $u$). "The point $u$ on $V_{\mathbb R}(h)$ is nonsingular" is stated separately, in the real-algebraic sense of [2, Def. 3.3.9]: some $n - \ell$ polynomials of the vanishing ideal $I(V_{\mathbb R}(h))$ have linearly independent gradients at $u$ (a smooth chart alone does not give this: $V = \{y^3 + 2x^2y - x^4 = 0\}$ is an analytic graph near $0$ but singular there). The parameters $t_1, \dots, t_r$ are the first $r$ coordinates. With $F(t) = f(\Psi(t))$, $f_1$ is the derivative $DF(0)$ and $2f_2$ is the second derivative $D^2F(0)$; the condition on $f_1$ includes that its coefficients on $t_{r+1}, \dots, t_\ell$ vanish. Marshall's parameters are Nash (analytic) functions; both requirements of Condition 2.3 are unchanged under a change of parameters that keeps $t_1, \dots, t_r$, so $C^\infty$ and analytic parameters give the same condition. The condition is not defined through the particular chart used in the proof of Theorem 3.1.
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, pp. 4–5, §2.3, Condition 2.2 and Condition 2.3

import Mathlib
import Definitions.Def_LasserreFC_FinConv_Setting

namespace LasserreFC.FinConv

open MvPolynomial
open scoped ContDiff

variable {n m1 m2 : ℕ}

/-- The boundary hessian condition (BHC) at `u`, Conditions 2.2–2.3 (Marshall), pp. 4–5.

Condition 2.2: there are `ℓ`, `r ≤ ℓ`, indices `ν₁ < ⋯ < ν_r` in `[m₂]`, an open neighbourhood `O` of
`u` and a `C^∞` immersion `Ψ` of an open `W ∋ 0` in `ℝ^ℓ` with `Ψ 0 = u`, which is a homeomorphism of
`W` onto `V_ℝ(h) ∩ O` (so `t = Ψ⁻¹` are local parameters and `ℓ` is the local dimension of `V_ℝ(h)`
at `u`); `u` is a nonsingular point of `V_ℝ(h)`: some `n − ℓ` polynomials of the vanishing ideal
`I(V_ℝ(h))` have linearly independent gradients at `u` ([2, Def. 3.3.9]); in these parameters `t_j = g_{ν_j}` (`j = 1, …, r`, the first `r` coordinates) and `K ∩ O` is
`{t₁ ≥ 0, …, t_r ≥ 0}`.

Condition 2.3: with `F(t) = f(Ψ(t))`, the linear part of `F` at `0` is `a₁t₁ + ⋯ + a_r t_r` with
every `a_j > 0`, and the quadratic part restricted to `t₁ = ⋯ = t_r = 0` is positive definite. -/
def IsBHC (P : POP n m1 m2) (u : Fin n → ℝ) : Prop :=
  ∃ (ℓ r : ℕ) (hrℓ : r ≤ ℓ) (ν : Fin r → Fin m2), StrictMono ν ∧
  ∃ (O : Set (Fin n → ℝ)) (W : Set (Fin ℓ → ℝ)) (Ψ : (Fin ℓ → ℝ) → (Fin n → ℝ)),
    (∃ (m : ℕ) (q : Fin m → MvPolynomial (Fin n) ℝ), m + ℓ = n ∧
      (∀ k, q k ∈ vanishingIdeal ℝ (realVariety P)) ∧ LinearIndependent ℝ (fun k => grad (q k) u)) ∧
    IsOpen O ∧ u ∈ O ∧ IsOpen W ∧ (0 : Fin ℓ → ℝ) ∈ W ∧ Ψ 0 = u ∧
    ContDiffOn ℝ ∞ Ψ W ∧ (∀ t ∈ W, Function.Injective (fderiv ℝ Ψ t)) ∧
    Set.InjOn Ψ W ∧ Ψ '' W = realVariety P ∩ O ∧
    ContinuousOn (Function.invFunOn Ψ W) (realVariety P ∩ O) ∧
    (∀ t ∈ W, ∀ j : Fin r, eval (Ψ t) (P.g (ν j)) = t (Fin.castLE hrℓ j)) ∧
    Ψ '' {t ∈ W | ∀ j : Fin r, 0 ≤ t (Fin.castLE hrℓ j)} = P.K ∩ O ∧
    (∀ j : Fin r, 0 < fderiv ℝ (fun t => eval (Ψ t) P.f) 0 (Pi.single (Fin.castLE hrℓ j) 1)) ∧
    (∀ j : Fin ℓ, r ≤ j.val → fderiv ℝ (fun t => eval (Ψ t) P.f) 0 (Pi.single j 1) = 0) ∧
    (∀ w : Fin ℓ → ℝ, w ≠ 0 → (∀ j : Fin ℓ, j.val < r → w j = 0) →
      0 < fderiv ℝ (fderiv ℝ (fun t => eval (Ψ t) P.f)) 0 w w)

end LasserreFC.FinConv


