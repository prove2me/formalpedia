-- Prove2me | Definitions.Def_WassTwoStage_LP1_Reformulations
-- name    : WassTwoStage_LP1_Reformulations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:56:25.607976+00:00
-- url     : https://prove2.me/theorems/104ad44f-c22c-4b4c-bd8e-f4925fe2027d
-- title:
--   The moment problem (5), the dual (6), problem (33) and the linear program (32) in the setting of §4
-- statement:
--   In the setting of Section 4 (recourse value $Z$, samples $\hat\xi_i$, radius $\epsilon$, gauge $\|\cdot\|$ of (31) with dual norm $\|\cdot\|_*$), fix a first-stage decision $x$. The following optimal values are defined, all in $[-\infty,+\infty]$.
--
--   1. The **moment problem (5)** with $r = 1$ and $\Xi=\mathbb R^K$:
--   $$\sup\ \frac1I\sum_{i\in[I]}\int Z(x,\xi)\,\mathbb P_i(d\xi)\quad\text{s.t.}\quad \mathbb P_1,\dots,\mathbb P_I \text{ probability measures on } \mathbb R^K,\ \ \frac1I\sum_{i\in[I]}\int \|\xi-\hat\xi_i\|\,\mathbb P_i(d\xi)\le\epsilon.$$
--   2. The **dual problem (6)** with $r = 1$:
--   $$\inf_{\lambda\ge 0}\ \epsilon\lambda + \frac1I\sum_{i\in[I]}\sup_{\xi\in\mathbb R^K}\big[Z(x,\xi) - \lambda\|\xi-\hat\xi_i\|\big].$$
--   3. **Problem (33)**:
--   $$\inf\ \epsilon\lambda + \frac1I\sum_{i\in[I]}\ \sup_{p\ge 0,\ W^\top p = q}\ h(x)^\top p + (T(x)^\top p)^\top\hat\xi_i \quad\text{s.t.}\quad \lambda\in\mathbb R_+,\ \ \|T(x)^\top p\|_*\le\lambda\ \ \forall p\in\mathbb R^M_+ : W^\top p = q.$$
--   4. The **linear program (32) at fixed $x$**: minimize $\epsilon\lambda + \frac1I\sum_{i\in[I]} q^\top y_i$ over $\lambda\in\mathbb R_+$, $y_i\in\mathbb R^{N_2}$ ($i\in[I]$), $\phi_k,\psi_k\in\mathbb R^{N_2}$ ($k\in[K]$) subject to
--   $$T(x)\hat\xi_i + h(x)\le Wy_i\ \ \forall i\in[I],\qquad q^\top\phi_k\le\lambda,\ \ q^\top\psi_k\le\lambda,\ \ T(x)e_k/w_+\le W\phi_k,\ \ -T(x)e_k/w_-\le W\psi_k\ \ \forall k\in[K],$$
--   where $e_k$ is the $k$-th unit vector.
--   5. The **linear program (32) over all variables with $c^\top x$ restored**: minimize $c^\top x + \epsilon\lambda + \frac1I\sum_i q^\top y_i$ over $x\in\mathcal X$ and the variables of item 4, subject to the constraints of item 4.
--
--   Infeasible problems have value $+\infty$. These are the problems connected by Theorem 1, display (33) and Theorem 6.
--
--   **Formalization Note** The printed objective of (32) omits the first-stage cost $c^\top x$ of problem (1); item 5 restores it, which is what makes (32) equivalent to (1) as a problem over $x$. Integrals of the extended-real recourse value use `erealExpectation`. The finite-first-moment requirement $\mathbb P_i\in\mathcal M^1$ of (5) is implied by the transport constraint and is not repeated.
-- source:
--   Hanasusanto, Kuhn, Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over Wasserstein Balls, arXiv:1609.07505v3, p. 7, (5)–(6); p. 22, (32); p. 23, (33)

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_erealExpectation
import Definitions.Def_WassTwoStage_LP1_Gauge
import Definitions.Def_WassTwoStage_LP1_Setting

open MeasureTheory Matrix

namespace WassTwoStage.LP1

variable {K M N₁ N₂ I : ℕ}

/-- The optimal value of the generalized moment problem (5) of Theorem 1, Hanasusanto–Kuhn,
arXiv:1609.07505v3, p. 7, in the instance of §4 (`r = 1`, `Ξ = ℝ^K`, `d(ξ, ξ') = ‖ξ − ξ'‖` with
the gauge (31)):
`sup (1/I) Σ_i ∫ Z(x, ξ) ℙ_i(dξ)` over families of probability measures `ℙ_1, …, ℙ_I` on `ℝ^K`
with `(1/I) Σ_i ∫ ‖ξ − ξ̂_i‖ ℙ_i(dξ) ≤ ε`. The integrals of the extended-real recourse value use
the convention of `erealExpectation` (`+∞` whenever the positive part has infinite integral). The
finite-first-moment requirement `ℙ_i ∈ M¹(ℝ^K)` is implied by the transport constraint, because
the gauge dominates `min(w₊, w₋)` times the 1-norm. -/
noncomputable def Data.momentValue (d : Data K M N₁ N₂ I) (x : Fin N₁ → ℝ) : EReal :=
  ⨆ (P : Fin I → Measure (Fin K → ℝ))
    (_ : (∀ i, IsProbabilityMeasure (P i)) ∧
      (I : ENNReal)⁻¹ * ∑ i, ∫⁻ ξ, gaugeCost d.wp d.wm ξ (d.ξhat i) ∂(P i)
        ≤ ENNReal.ofReal d.ε),
    (((I : ℝ)⁻¹ : ℝ) : EReal) *
      ∑ i, WassersteinDRO.Duality.erealExpectation (P i) (fun ξ => d.recourse x ξ)

/-- The optimal value of the dual robust optimization problem (6) of Theorem 1, p. 7, in the
instance of §4 (`r = 1`, `Ξ = ℝ^K`, gauge cost (31)):
`inf_{λ ≥ 0} ελ + (1/I) Σ_i sup_{ξ ∈ ℝ^K} [Z(x, ξ) − λ‖ξ − ξ̂_i‖]`. -/
noncomputable def Data.dualValue6 (d : Data K M N₁ N₂ I) (x : Fin N₁ → ℝ) : EReal :=
  ⨅ (lam : ℝ) (_ : 0 ≤ lam),
    ((d.ε * lam : ℝ) : EReal) + (((I : ℝ)⁻¹ : ℝ) : EReal) *
      ∑ i, ⨆ ξ : Fin K → ℝ,
        d.recourse x ξ - ((lam * gauge d.wp d.wm (ξ - d.ξhat i) : ℝ) : EReal)

/-- Feasibility in the dual recourse problem (4) with `Q = 0`: `p ∈ ℝ^M_+` and `Wᵀp = q`. -/
def Data.DualFeasible (d : Data K M N₁ N₂ I) (p : Fin M → ℝ) : Prop :=
  0 ≤ p ∧ d.Wᵀ *ᵥ p = d.q

/-- The optimal value of problem (33), proof of Theorem 6, p. 23:
`inf ελ + (1/I) Σ_i sup_{p ≥ 0, Wᵀp = q} [h(x)ᵀp + (T(x)ᵀp)ᵀ ξ̂_i]` over `λ ∈ ℝ_+` subject to
`‖T(x)ᵀp‖_* ≤ λ` for every `p ∈ ℝ^M_+` with `Wᵀp = q`, where `‖·‖_*` is the dual norm (polar) of
the gauge (31). Inner suprema and the value are extended reals (`+∞` allowed; an infeasible
`λ`-constraint gives `+∞`). -/
noncomputable def Data.value33 (d : Data K M N₁ N₂ I) (x : Fin N₁ → ℝ) : EReal :=
  ⨅ (lam : ℝ)
    (_ : 0 ≤ lam ∧ ∀ p, d.DualFeasible p → dualGauge d.wp d.wm ((d.T x)ᵀ *ᵥ p) ≤ (lam : EReal)),
    ((d.ε * lam : ℝ) : EReal) + (((I : ℝ)⁻¹ : ℝ) : EReal) *
      ∑ i, ⨆ (p : Fin M → ℝ) (_ : d.DualFeasible p),
        ((d.h x ⬝ᵥ p + ((d.T x)ᵀ *ᵥ p) ⬝ᵥ d.ξhat i : ℝ) : EReal)

/-- The constraints of the linear program (32), Theorem 6, p. 22, at a fixed first-stage
decision `x`: `λ ∈ ℝ_+`, `y_i ∈ ℝ^{N₂}` (`i ∈ [I]`), `φ_k, ψ_k ∈ ℝ^{N₂}` (`k ∈ [K]`) with
* `T(x)ξ̂_i + h(x) ≤ W y_i` for all `i ∈ [I]`;
* `qᵀφ_k ≤ λ`, `qᵀψ_k ≤ λ`, `T(x)e_k / w₊ ≤ W φ_k` and `−T(x)e_k / w₋ ≤ W ψ_k` for all
  `k ∈ [K]`, where `T(x)e_k` is the `k`-th column of `T(x)`. -/
def Data.LP32Feasible (d : Data K M N₁ N₂ I) (x : Fin N₁ → ℝ) (lam : ℝ)
    (y : Fin I → Fin N₂ → ℝ) (phi psi : Fin K → Fin N₂ → ℝ) : Prop :=
  0 ≤ lam ∧ (∀ i, d.T x *ᵥ d.ξhat i + d.h x ≤ d.W *ᵥ y i) ∧
    ∀ k, d.q ⬝ᵥ phi k ≤ lam ∧ d.q ⬝ᵥ psi k ≤ lam ∧
      (1 / d.wp) • (d.T x *ᵥ Pi.single k 1) ≤ d.W *ᵥ phi k ∧
      -((1 / d.wm) • (d.T x *ᵥ Pi.single k 1)) ≤ d.W *ᵥ psi k

/-- The optimal value of the linear program (32), Theorem 6, p. 22, at a fixed first-stage
decision `x`: the infimum of `ελ + (1/I) Σ_i qᵀy_i` over the constraints `LP32Feasible`
(`+∞` if they are infeasible). -/
noncomputable def Data.lp32 (d : Data K M N₁ N₂ I) (x : Fin N₁ → ℝ) : EReal :=
  ⨅ (lam : ℝ) (y : Fin I → Fin N₂ → ℝ) (phi : Fin K → Fin N₂ → ℝ)
    (psi : Fin K → Fin N₂ → ℝ)
    (_ : d.LP32Feasible x lam y phi psi),
    ((d.ε * lam + (1 / (I : ℝ)) * ∑ i, d.q ⬝ᵥ y i : ℝ) : EReal)

/-- The optimal value of the linear program (32) over all its variables, including
`x ∈ X`, **with the first-stage cost `cᵀx` of problem (1) added to the objective** (the printed
objective of (32) omits it): `inf cᵀx + ελ + (1/I) Σ_i qᵀy_i` subject to `x ∈ X` and the
constraints of (32). -/
noncomputable def Data.value32 (d : Data K M N₁ N₂ I) : EReal :=
  ⨅ (x : Fin N₁ → ℝ) (lam : ℝ) (y : Fin I → Fin N₂ → ℝ) (phi : Fin K → Fin N₂ → ℝ)
    (psi : Fin K → Fin N₂ → ℝ)
    (_ : x ∈ d.X ∧ d.LP32Feasible x lam y phi psi),
    ((d.c ⬝ᵥ x + d.ε * lam + (1 / (I : ℝ)) * ∑ i, d.q ⬝ᵥ y i : ℝ) : EReal)

end WassTwoStage.LP1


