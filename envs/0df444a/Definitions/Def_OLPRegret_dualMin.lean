-- Prove2me | Definitions.Def_OLPRegret_dualMin
-- name    : OLPRegret_dualMin
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:03:27.170467+00:00
-- url     : https://prove2.me/theorems/60d138c4-018b-4e2f-91c3-1718dafc3221
-- title:
--   The empirical dual and its minimizers
-- statement:
--   For a sample of the $t$ customers of periods $t,\dots,1$ define the **empirical dual** and its subgradient
--   $$
--   \Lambda_t^b(y)=b'y+\sum_{s=1}^t\Delta_s(y)^+/t,\qquad \dot\Lambda_t^b(y)=b-\sum_{s=1}^t\mathbb 1\{\Delta_s(y)>0\}a_s/t.
--   $$
--   The **empirical shadow prices** $y_t^b$ are the minimizers of $\Lambda_t^b$ over $\mathbb R^m_+$, which need not be unique. A **choice of shadow prices** for a sample $\omega$ of horizon $n$ assigns to each $k\ge1$ and $c\ge0$ a minimizer $y_k^c$ of the dual on periods $k,\dots,1$, is unconstrained at $c\not\ge0$, and has $y_0=0$.
--
--   The minimizers are the primal-dual link of the proof: the dual on periods $t-1,\dots,1$ is independent of period $t$ and of the history.
--
--   **Formalization Note** The set `dualMin` is nonempty for $t\ge1$, $b\ge0$. The paper leaves $y_0$ undefined; (30) at $t=1$ forces $y_0=0$.
-- source:
--   Bray, arXiv:1912.08917v6, (19)–(21), p.19; (24), p.21; (29)–(39), pp.26–32

import Mathlib
import Definitions.Def_OLPRegret_Policy

set_option autoImplicit false

open MeasureTheory

namespace OLPRegret

/-- The empirical dual `Λₜᵇ(y) = b′y + Σₛ Δₛ(y)⁺/t` over a sample of the `t` customers of periods
`t, …, 1` (Bray, arXiv:1912.08917v6, (19)–(20), p.19). -/
noncomputable def Lambda {m t : ℕ} (s : Sample m t) (b y : E m) : ℝ :=
  inner ℝ b y + (∑ i, max (surplus (s i) y) 0) / (t : ℝ)

open scoped Classical in
/-- The subgradient `Λ̇ₜᵇ(y) = b − Σₛ 𝟙{Δₛ(y) > 0}aₛ/t` (Bray, arXiv:1912.08917v6, (24), p.21). -/
noncomputable def LambdaDot {m t : ℕ} (s : Sample m t) (b y : E m) : E m :=
  b - (t : ℝ)⁻¹ • ∑ i, (if 0 < surplus (s i) y then (s i).2 else 0)

/-- The set of empirical shadow prices: the minimizers `yₜᵇ` of `Λₜᵇ` over `ℝᵐ₊`
(Bray, arXiv:1912.08917v6, (21), p.19, "a not-necessarily-unique shadow price minimizer").

**Formalization Note** The minimizers of `tΛₜᵇ` and of `Λₜᵇ` agree for `t ≥ 1`. This set is nonempty
for `b ≥ 0`, `t ≥ 1`: (19) is a feasible linear program with objective bounded below by `0`. -/
def dualMin {m t : ℕ} (s : Sample m t) (b : E m) : Set (E m) :=
  {y | IsMinimizer (Lambda s b) y}

/-- The customers of periods `k, …, 1` of a sample of horizon `n ≥ k`. -/
def lower {m n : ℕ} (ω : Sample m n) (k : ℕ) (h : k ≤ n) : Sample m k :=
  fun i => ω (Fin.castLE h i)

/-- `Y k c` is a choice of shadow prices `y_k^c` for the sample `ω`: a minimizer of the dual on
periods `k, …, 1` for every `k ≥ 1` and `c ≥ 0`, unconstrained at `c ≱ 0`, and `y₀ = 0`
(Bray, arXiv:1912.08917v6, (21), p.19, as used in (29)–(39), pp.26–32).

**Formalization Note** The paper leaves `y₀` undefined. `(30)` at `t = 1` reads
`x a′y₀ ≤ V̄₀ − V̄₀ = 0`, which for every bundle forces `y₀ = 0`. -/
def IsShadowPriceChoice {m n : ℕ} (ω : Sample m n) (Y : ℕ → E m → E m) : Prop :=
  (∀ c, Y 0 c = 0) ∧
    ∀ (k : ℕ) (h : k ≤ n), 1 ≤ k → ∀ c, VNonneg c → Y k c ∈ dualMin (lower ω k h) c

end OLPRegret


