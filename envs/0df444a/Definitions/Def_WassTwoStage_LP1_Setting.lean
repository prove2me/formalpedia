-- Prove2me | Definitions.Def_WassTwoStage_LP1_Setting
-- name    : WassTwoStage_LP1_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:55:35.74211+00:00
-- url     : https://prove2.me/theorems/b26562eb-cfb4-408b-8b85-843c50121ee8
-- title:
--   Two-stage DRO data with $Q = 0$, recourse value $Z(x,\xi)$, the 1-Wasserstein ball over the gauge (31), worst-case expectation $\mathcal Z(x)$ and problem (1)
-- statement:
--   The data of the two-stage distributionally robust linear program of Section 4 of Hanasusanto and Kuhn consist of
--
--   1. a first-stage cost $c\in\mathbb R^{N_1}$ and a feasible set $\mathcal X\subseteq\mathbb R^{N_1}$;
--   2. a second-stage cost $q\in\mathbb R^{N_2}$, a recourse matrix $W\in\mathbb R^{M\times N_2}$, and matrix- and vector-valued affine functions $T(x)\in\mathbb R^{M\times K}$, $h(x)\in\mathbb R^M$ of the first-stage decision $x$;
--   3. samples $\hat\xi_1,\dots,\hat\xi_I\in\mathbb R^K$, a radius $\epsilon$, and the parameters $w_+, w_-$ of the gauge (31).
--
--   The uncertain parameter $\xi$ ranges over $\Xi = \mathbb R^K$ and enters only the constraints of the recourse problem ($Q = 0$). The **recourse value** is
--
--   $$Z(x,\xi) = \inf\{\, q^\top y \;:\; y\in\mathbb R^{N_2},\ T(x)\xi + h(x) \le Wy \,\} \in [-\infty, +\infty].$$
--
--   The problem has **sufficiently expensive recourse** (Definition 2 with $Q = 0$, $\Xi=\mathbb R^K$) if there is $p\in\mathbb R^M_+$ with $W^\top p = q$.
--
--   The **1-Wasserstein ball** $\mathcal B^1_\epsilon(\hat{\mathbb P}_I)$ is the set of probability measures $\mathbb P$ on $\mathbb R^K$ whose optimal transport cost to the empirical distribution $\hat{\mathbb P}_I = \frac1I\sum_{i\in[I]}\delta_{\hat\xi_i}$, for the cost $d(\xi,\xi') = \|\xi-\xi'\|$ of (31), is at most $\epsilon$. The **worst-case expectation** and the value of problem (1) are
--
--   $$\mathcal Z(x) = \sup_{\mathbb P\in\mathcal B^1_\epsilon(\hat{\mathbb P}_I)} \mathbb E_{\mathbb P}\big[Z(x,\tilde\xi)\big], \qquad \inf_{x\in\mathcal X}\; c^\top x + \mathcal Z(x).$$
--
--   This is the model of every statement of the mission.
--
--   **Formalization Note** All optimal values are extended reals, defined as infima and suprema over the feasible sets: an infeasible recourse problem has value $+\infty$. Expectations of the extended-real recourse value use the platform's `erealExpectation` (value $+\infty$ whenever the positive part has infinite integral). The transport cost is the platform's `transportCost`, whose couplings have first marginal $\mathbb P$ and second marginal $\hat{\mathbb P}_I$. The finite-first-moment requirement $\mathbb P\in\mathcal M^1(\mathbb R^K)$ of Definition 3 is not repeated: finite transport cost to the finitely supported $\hat{\mathbb P}_I$ implies it, because the gauge dominates $\min\{w_+,w_-\}$ times the 1-norm. $Q = 0$ is built in by omitting $Q$ from the data.
-- source:
--   Hanasusanto, Kuhn, Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over Wasserstein Balls, arXiv:1609.07505v3, pp. 5–6, (1)–(3), Definitions 2–3; p. 22, §4 preamble and (31)

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_WassersteinDRO_Duality_erealExpectation
import Definitions.Def_WassTwoStage_LP1_Gauge

open MeasureTheory Matrix

namespace WassTwoStage.LP1

/-- The data of the two-stage distributionally robust linear program (1)–(3) of Hanasusanto–Kuhn,
*Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over
Wasserstein Balls*, arXiv:1609.07505v3, pp. 5–7, in the setting of §4 (p. 22), where `Q = 0`:

* `c ∈ ℝ^{N₁}` and `X ⊆ ℝ^{N₁}`: the first-stage cost and feasible set of (1);
* `q ∈ ℝ^{N₂}`: the second-stage cost `qᵀy` of (3) (the uncertainty-dependent part `Qξ` is
  absent because `Q = 0` throughout §4);
* `T(x) ∈ ℝ^{M×K}`, `h(x) ∈ ℝ^M`: matrix- and vector-valued **affine** functions of the
  first-stage decision `x` (p. 6), and `W ∈ ℝ^{M×N₂}` the recourse matrix;
* `ξhat i ∈ ℝ^K`, `i ∈ [I]`: the samples defining the empirical distribution `ℙ̂_I`;
* `ε`: the radius of the 1-Wasserstein ball;
* `wp = w₊`, `wm = w₋`: the positive scaling parameters of the reference gauge (31).

The uncertain parameter ranges over `Ξ = ℝ^K` (no support constraints, §4), modelled as
`Fin K → ℝ` with its product (= Borel) σ-algebra. -/
structure Data (K M N₁ N₂ I : ℕ) where
  c : Fin N₁ → ℝ
  X : Set (Fin N₁ → ℝ)
  q : Fin N₂ → ℝ
  T : (Fin N₁ → ℝ) →ᵃ[ℝ] Matrix (Fin M) (Fin K) ℝ
  h : (Fin N₁ → ℝ) →ᵃ[ℝ] (Fin M → ℝ)
  W : Matrix (Fin M) (Fin N₂) ℝ
  ξhat : Fin I → (Fin K → ℝ)
  ε : ℝ
  wp : ℝ
  wm : ℝ

variable {K M N₁ N₂ I : ℕ}

/-- The recourse function (3), p. 5, with `Q = 0` (§4, p. 22):
`Z(x, ξ) = inf {qᵀy : y ∈ ℝ^{N₂}, T(x)ξ + h(x) ≤ Wy}`, an extended real number: `+∞` when the
recourse problem is infeasible and `−∞` when it is unbounded below. -/
noncomputable def Data.recourse (d : Data K M N₁ N₂ I) (x : Fin N₁ → ℝ) (ξ : Fin K → ℝ) :
    EReal :=
  ⨅ (y : Fin N₂ → ℝ) (_ : d.T x *ᵥ ξ + d.h x ≤ d.W *ᵥ y), ((d.q ⬝ᵥ y : ℝ) : EReal)

/-- Definition 2 (sufficiently expensive recourse), p. 6, specialised to `Q = 0` and
`Ξ = ℝ^K`: the dual recourse problem (4), `sup {(T(x)ξ + h(x))ᵀp : p ∈ ℝ^M_+, Wᵀp = q}`, is
feasible, i.e. there is `p ≥ 0` with `Wᵀp = q` (the condition no longer depends on `ξ`). -/
def Data.SufficientlyExpensiveRecourse (d : Data K M N₁ N₂ I) : Prop :=
  ∃ p : Fin M → ℝ, 0 ≤ p ∧ d.Wᵀ *ᵥ p = d.q

/-- The 1-Wasserstein ball `B¹_ε(ℙ̂_I)` of Definition 3 (p. 6) in the setting of §4 (p. 22):
the probability measures `ℙ` on `ℝ^K` whose optimal transport cost to the empirical distribution
`ℙ̂_I = (1/I) Σ_i δ_{ξ̂_i}`, for the cost `d(ξ, ξ') = ‖ξ − ξ'‖` of (31), is at most `ε`. The
coupling has first marginal `ℙ` and second marginal `ℙ̂_I`. -/
def Data.ball (d : Data K M N₁ N₂ I) : Set (Measure (Fin K → ℝ)) :=
  {P | IsProbabilityMeasure P ∧
    RWPI.SqrtLasso.transportCost (gaugeCost d.wp d.wm) P
      (WassersteinDRO.Duality.empiricalDistribution d.ξhat) ≤ ENNReal.ofReal d.ε}

/-- The worst-case expectation (2), p. 5, over the 1-Wasserstein ball of §4:
`𝒵(x) = sup_{ℙ ∈ B¹_ε(ℙ̂_I)} E_ℙ[Z(x, ξ̃)]`, where the expectation of the extended-real recourse
value is `+∞` whenever its positive part has infinite integral. -/
noncomputable def Data.worstCase (d : Data K M N₁ N₂ I) (x : Fin N₁ → ℝ) : EReal :=
  ⨆ (P : Measure (Fin K → ℝ)) (_ : P ∈ d.ball),
    WassersteinDRO.Duality.erealExpectation P (fun ξ => d.recourse x ξ)

/-- The optimal value of the two-stage distributionally robust problem (1), p. 5:
`inf {cᵀx + 𝒵(x) : x ∈ X}`. -/
noncomputable def Data.value1 (d : Data K M N₁ N₂ I) : EReal :=
  ⨅ x ∈ d.X, ((d.c ⬝ᵥ x : ℝ) : EReal) + d.worstCase x

end WassTwoStage.LP1


