-- Prove2me | Definitions.Def_TSDRiem_TSDRun_BlockSmooth
-- name    : TSDRiem_TSDRun_BlockSmooth
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:27:14.52375+00:00
-- url     : https://prove2.me/theorems/29342a2d-eafe-4cc9-a72d-fa0ef4542e01
-- title:
--   Assumption 4.1 (Generalized Block Smoothness), inequality (8)
-- statement:
--   **Assumption 4.1.** There are constants $0<L_1,\dots,L_m<\infty$ such that for every $t\ge1$ and $k\in[m]$ the iterates of Algorithm 1 satisfy
--
--   $$
--   f\Big(\operatorname{Exp}_{y^{t,k-1}}\big(P^{y^{t,k-1}}_k v\big)\Big)\le f(y^{t,k-1})+\big\langle\nabla f(y^{t,k-1}),P^{y^{t,k-1}}_k v\big\rangle_{y^{t,k-1}}+\frac{L_k}{2}\big\|P^{y^{t,k-1}}_k v\big\|^2_{y^{t,k-1}}
--   $$
--
--   for all $v\in T_{y^{t,k-1}}M$.
--
--   This is a quadratic upper bound of $f$ along the selected subspace at each inner step. With stepsize $1/L_k$ it yields the per-step decrease (12) behind Lemma 4.1.
--
--   **Formalization Note** The assumption is imposed along a given run of Algorithm 1. Lean's `k : Fin m` is the paper's step $k+1$, so `L k` is $L_{k+1}$.
-- source:
--   Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, Assumption 4.1, eq. (8), p.9

import Mathlib
import Definitions.Def_TSDRiem_RiemSetting
import Definitions.Def_TSDRiem_TSDRun

open scoped RealInnerProductSpace

namespace TSDRiem

/-- Assumption 4.1 (Generalized Block Smoothness) along a run: there are constants
`0 < L_1, …, L_m < ∞` such that for any `t ≥ 1` and `k ∈ [m]` the iterates satisfy (8),
`f(Exp_{y^{t,k−1}}(P^{y^{t,k−1}}_k v)) ≤ f(y^{t,k−1}) + ⟨∇f(y^{t,k−1}), P^{y^{t,k−1}}_k v⟩_{y^{t,k−1}}
  + (L_k/2) ‖P^{y^{t,k−1}}_k v‖²_{y^{t,k−1}}` for all `v ∈ T_{y^{t,k−1}}M`.

Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, Assumption 4.1,
eq. (8), p.9.

Formalization Note: Lean's `k : Fin m` is the paper's `k + 1`, so `L k` is `L_{k+1}` and
`R.y t k.castSucc` is `y^{t,k}`. The paper states the assumption for "the iterates of
Algorithm 1"; here it is imposed along the given run (generalization). -/
def TSDRun.BlockSmooth {M : Type*} [MetricSpace M] {T : M → Type*}
    [∀ x, NormedAddCommGroup (T x)] [∀ x, InnerProductSpace ℝ (T x)]
    [∀ x, FiniteDimensional ℝ (T x)] {S : RiemSetting M T} {grad : (x : M) → T x} {m : ℕ}
    (R : TSDRun S grad m) (f : M → ℝ) (L : Fin m → ℝ) : Prop :=
  (∀ k, 0 < L k) ∧ ∀ t, 1 ≤ t → ∀ (k : Fin m) (v : T (R.y t k.castSucc)),
    f (S.exp (R.y t k.castSucc) ((R.sub t k).starProjection v)) ≤
      f (R.y t k.castSucc) + ⟪grad (R.y t k.castSucc), (R.sub t k).starProjection v⟫ +
        L k / 2 * ‖(R.sub t k).starProjection v‖ ^ 2

end TSDRiem


