-- Prove2me | Definitions.Def_ProjFPOracle_vhat
-- name    : ProjFPOracle_vhat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:32:22.190474+00:00
-- url     : https://prove2.me/theorems/0ded033e-ab6b-4e8e-b3a7-3ebb59426f41
-- title:
--   The stochastic approximation iterates $\vartheta_t$, $v_t$ and the Polyak–Ruppert average $\widehat v_n$
-- statement:
--   Given the projected observations $(A_t,h_t)$, a stepsize $\eta>0$ and a starting vector $\vartheta_0\in\mathbb R^d$, the **stochastic approximation iterates** are
--   $$
--   \vartheta_{t+1}=(1-\eta)\vartheta_t+\eta\big(A_{t+1}\vartheta_t+h_{t+1}\big),\qquad t=0,1,2,\dots,
--   $$
--   and $v_t=\Phi_d^*\vartheta_t\in\mathbb S$; equivalently $v_{t+1}=(1-\eta)v_t+\eta\,\Pi_{\mathbb S}(L_{t+1}v_t+b_{t+1})$. For a sample size $n$ and a burn-in time $n_0<n$, the **Polyak–Ruppert average** is
--   $$
--   \widehat v_n:=\frac1{n-n_0}\sum_{t=n_0+1}^n v_t .
--   $$
--   This is the estimator of the projected fixed point $\bar v$ whose error Theorem 1 bounds.
--
--   **Formalization Note** The recursion is by induction on $t$; step $t\to t+1$ uses observation $t+1$, so $\vartheta_t$ depends on the first $t$ observations. The start $v_0=\Phi_d^*\vartheta_0$ is deterministic and lies in $\mathbb S$. $n-n_0$ is natural-number subtraction cast to a real; every statement assumes $n_0<n$.
-- source:
--   Mou, Pananjady & Wainwright, Optimal Oracle Inequalities for Projected Fixed-Point Equations, arXiv:2012.05299v1, §3.1, p.12, Eqs. (24a), (24b), (25)

import Mathlib
import Definitions.Def_ProjFPOracle_Phi

open Matrix

namespace ProjFPOracle

/-- **The stochastic approximation iterates in `ℝ^d`** (Mou, Pananjady & Wainwright, *Optimal Oracle
Inequalities for Projected Fixed-Point Equations*, arXiv:2012.05299v1, Eq. (25), p.12):
`ϑ_{t+1} = (1 − η) ϑ_t + η (Φ_d L_{t+1} Φ_d^* ϑ_t + Φ_d b_{t+1})`, started at a fixed `ϑ_0 ∈ ℝ^d`,
with the observations `A_{t+1} = Φ_d L_{t+1} Φ_d^*`, `h_{t+1} = Φ_d b_{t+1}`.

**Formalization Note** Defined by recursion on `t`; step `t → t + 1` uses observation `t + 1`, so
`ϑ_t` depends on observations `1, …, t`. The start `ϑ_0` is deterministic. -/
noncomputable def theta {d : ℕ} {Ω : Type*} (A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (h : ℕ → Ω → Fin d → ℝ) (η : ℝ) (ϑ₀ : Fin d → ℝ) : ℕ → Ω → Fin d → ℝ
  | 0 => fun _ => ϑ₀
  | t + 1 => fun ω =>
      (1 - η) • theta A h η ϑ₀ t ω + η • (A (t + 1) ω *ᵥ theta A h η ϑ₀ t ω + h (t + 1) ω)

/-- **The iterates `v_t = Φ_d^* ϑ_t` in `𝕏`** (arXiv:2012.05299v1, Eqs. (24a), (25), p.12):
`v_{t+1} = (1 − η) v_t + η Π_𝕊(L_{t+1} v_t + b_{t+1})` with `v_0 = Φ_d^* ϑ_0 ∈ 𝕊`. -/
noncomputable def vIter {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {S : Submodule ℝ X} {d : ℕ} (φ : OrthonormalBasis (Fin d) ℝ S) {Ω : Type*}
    (A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (h : ℕ → Ω → Fin d → ℝ) (η : ℝ) (ϑ₀ : Fin d → ℝ)
    (t : ℕ) (ω : Ω) : X :=
  PhiStar φ (theta A h η ϑ₀ t ω)

/-- **The Polyak–Ruppert average `v̂_n`** (arXiv:2012.05299v1, Eq. (24b), p.12):
`v̂_n := (1/(n − n_0)) ∑_{t=n_0+1}^n v_t`, with burn-in time `n_0`.

**Formalization Note** `n − n_0` is natural-number subtraction cast to `ℝ`; every statement using
`vhat` assumes `n_0 < n`, so it is the true difference and is positive. -/
noncomputable def vhat {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {S : Submodule ℝ X} {d : ℕ} (φ : OrthonormalBasis (Fin d) ℝ S) {Ω : Type*}
    (A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (h : ℕ → Ω → Fin d → ℝ) (η : ℝ) (ϑ₀ : Fin d → ℝ)
    (n₀ n : ℕ) (ω : Ω) : X :=
  (1 / ((n - n₀ : ℕ) : ℝ)) • ∑ t ∈ Finset.Ioc n₀ n, vIter φ A h η ϑ₀ t ω

end ProjFPOracle


