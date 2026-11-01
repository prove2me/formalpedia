-- Prove2me | Definitions.Def_TSDRiem_TSDRun
-- name    : TSDRiem_TSDRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:26:25.734988+00:00
-- url     : https://prove2.me/theorems/6d83f2f5-cc07-4686-921e-ed19abeedb5e
-- title:
--   A run of Algorithm 1 (Tangent Subspace Descent)
-- statement:
--   Fix a Riemannian setting with finite-dimensional tangent spaces, a gradient field $\nabla f$ and a number $m$ of inner steps. **Tangent Subspace Descent** (Algorithm 1) produces outer iterates $x^t$ and inner iterates $y^{t,0},\dots,y^{t,m}$ by
--
--   $$
--   y^{t,0}=x^{t-1},\qquad
--   y^{t,k}=\operatorname{Exp}_{y^{t,k-1}}\!\Big(-\eta_{t,k}\,P^{y^{t,k-1}}_k\nabla f(y^{t,k-1})\Big)\ \ (k\in[m]),\qquad
--   x^t=y^{t,m},
--   $$
--
--   for $t=1,2,\dots$, where $x^0$ is the initial point, $\eta_{t,k}>0$ are stepsizes and $P^{y^{t,k-1}}_k$ is the orthogonal projection onto a subspace of $T_{y^{t,k-1}}M$ chosen by the subspace selection rule.
--
--   A run records the iterates, the stepsizes, the chosen subspaces, and, for each inner step, a tangent vector $w_{t,k}\in T_{y^{t,k-1}}M$ with $\operatorname{Exp}_{y^{t,k-1}}(w_{t,k})=y^{t,0}$. That vector fixes the geodesic along which the transport $\Gamma^{y^{t,0}}_{y^{t,k-1}}$ back to the start of the inner loop is taken.
--
--   **Formalization Note** The outer index $t\ge1$ is the paper's and the relations are imposed for $t\ge1$. The inner index is `Fin m`, shifted by one: Lean's step `k` is the paper's step $k+1$, starting at `y t k.castSucc` $=y^{t,k}$ and producing `y t k.succ` $=y^{t,k+1}$. The subspaces are data of the run rather than the output of a rule applied to the past inner iterates, and the connecting vectors are arbitrary. The paper never names the geodesic of $\Gamma^{y^{t,0}}_{y^{t,k-1}}$; p.5 uses the notation for a unique geodesic. Hypotheses that the paper places on the rule are placed on the run, so every result holds for every run of every rule satisfying them.
-- source:
--   Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, Algorithm 1, p.6 (the rule outputs orthogonal projections onto subspaces, p.2)

import Mathlib
import Definitions.Def_TSDRiem_RiemSetting

namespace TSDRiem

/-- A run of Algorithm 1 (Tangent Subspace Descent) with `m` inner steps, for the gradient field
`grad`:

```
for t = 1, 2, … do
  y^{t,0} := x^{t−1};
  for k ∈ [m] do
    pick P^{y^{t,k−1}}_k := P({y^{t,j}}_{j=0}^{k−1}, k) and η_{t,k} > 0;
    y^{t,k} := Exp_{y^{t,k−1}}(−η_{t,k} P^{y^{t,k−1}}_k ∇f(y^{t,k−1}));
  x^t := y^{t,m};
```

Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, Algorithm 1,
p.6 (the rule outputs orthogonal projections onto subspaces of the tangent space, p.2).

Fields:
* `x t` is `x^t` (`x 0` is the initial point `x⁰`); `y t j` is `y^{t,j}` for `j = 0, …, m`;
* `η t k` is the stepsize `η_{t,k+1}`, `sub t k` the subspace of `T_{y^{t,k}}M` onto which the
  rule projects at inner step `k+1`, so `P^{y^{t,k−1}}_k = (sub t (k−1)).starProjection`;
* `w t k` is a tangent vector at `y^{t,k}` (Lean `k.castSucc`) with `Exp(w t k) = y^{t,0}`; it fixes
  the geodesic of the transport `Γ^{y^{t,0}}_{y^{t,k−1}}` used to define `P_{t,k}` (p.6).

Formalization Note (index base): the outer index `t ≥ 1` is the paper's; the relations are
imposed for `t ≥ 1` only, and `y 0 ·` is unused. The inner index `k : Fin m` is the paper's
`k + 1 ∈ [m]`: `y t k.castSucc = y^{t,k}` is the point at which step `k + 1` starts (the paper's
`y^{t,(k+1)−1}`) and `y t k.succ = y^{t,k+1}` the point it produces. The connecting vectors are
required at every `t` (also `t = 0`), which every row admits by axiom (A2).

Formalization Note (generalization): the subspaces are data of the run rather than the output of
a rule `P` applied to the past inner iterates, and the connecting vectors `w` are arbitrary (the
paper never names the geodesic of `Γ^{y^{t,0}}_{y^{t,k−1}}`; p.5 uses the notation "when there is
a unique geodesic"). Hypotheses that the paper imposes on the rule are imposed on this run. -/
structure TSDRun {M : Type*} [MetricSpace M] {T : M → Type*}
    [∀ x, NormedAddCommGroup (T x)] [∀ x, InnerProductSpace ℝ (T x)]
    [∀ x, FiniteDimensional ℝ (T x)]
    (S : RiemSetting M T) (grad : (x : M) → T x) (m : ℕ) where
  /-- The outer iterates `x^t`, `x 0 = x⁰`. -/
  x : ℕ → M
  /-- The inner iterates `y^{t,j}`, `j = 0, …, m`. -/
  y : ℕ → Fin (m + 1) → M
  /-- The stepsizes: `η t k = η_{t,k+1}`. -/
  η : ℕ → Fin m → ℝ
  /-- The selected subspaces: `(sub t k).starProjection = P^{y^{t,k}}_{k+1}`. -/
  sub : (t : ℕ) → (k : Fin m) → Submodule ℝ (T (y t k.castSucc))
  /-- Connecting vectors fixing `Γ^{y^{t,0}}_{y^{t,k}}`. -/
  w : (t : ℕ) → (k : Fin m) → T (y t k.castSucc)
  η_pos : ∀ t, 1 ≤ t → ∀ k, 0 < η t k
  y_zero : ∀ t, 1 ≤ t → y t 0 = x (t - 1)
  y_succ : ∀ t, 1 ≤ t → ∀ k : Fin m,
    y t k.succ = S.exp (y t k.castSucc) (-(η t k) • (sub t k).starProjection (grad (y t k.castSucc)))
  y_last : ∀ t, 1 ≤ t → y t (Fin.last m) = x t
  w_spec : ∀ t k, S.exp (y t k.castSucc) (w t k) = y t 0

end TSDRiem


