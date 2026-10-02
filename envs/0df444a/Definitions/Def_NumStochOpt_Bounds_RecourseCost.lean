-- Prove2me | Definitions.Def_NumStochOpt_Bounds_RecourseCost
-- name    : NumStochOpt_Bounds_RecourseCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T18:51:02.309402+00:00
-- url     : https://prove2.me/theorems/b8779532-2d25-46ba-a0a4-3dfb9c9dff73
-- title:
--   The recourse cost $Q(x,\xi)$, complete recourse, dual feasibility, expected recourse and the dual-multiplier minorant
-- statement:
--   This file fixes the objects of the linear two-stage problem with fixed recourse (Kall, Ruszczyński and Frauendorfer, §2.2.1).
--
--   Let $W$ be a deterministic $m_2\times n_2$ recourse matrix. For a cost vector $q\in\mathbb R^{n_2}$, a right-hand side $h\in\mathbb R^{m_2}$, a technology matrix $T$ of size $m_2\times n_1$ and a first-stage decision $x\in\mathbb R^{n_1}$, the **recourse cost** is the optimal value of the second-stage problem (2.12),
--   $$
--   Q(x,\xi)=\inf\{\,q^{T}y \;:\; Wy=h-Tx,\ y\ge 0\,\},\qquad \xi=(q,h,T),
--   $$
--   taken in the extended reals: it is $+\infty$ when (2.12) is infeasible (the book's convention on p. 39) and $-\infty$ when (2.12) is unbounded.
--
--   1. **Complete recourse** (p. 39): $\{Wy : y\ge 0\}=\mathbb R^{m_2}$.
--   2. **Dual feasibility** of $q$ (p. 39): some $u\in\mathbb R^{m_2}$ satisfies $W^{T}u\le q$; by linear programming duality this is exactly what excludes $Q=-\infty$.
--   3. The **expected recourse function** (2.11), property (e): for random data $\xi(\omega)=(q(\omega),h(\omega),T(\omega))$ on a probability space $(\Omega,P)$,
--   $$
--   \mathcal Q(x)=\int_\Omega Q(x,\xi(\omega))\,P(d\omega).
--   $$
--   4. The **dual-multiplier minorant** of (2.30): for vectors $u_1,\dots,u_L$ ($L\ge 1$), $\max_{1\le \ell\le L}(h-Tx)^{T}u_\ell$.
--
--   These are the objects about which properties (b), (d), (e) and the lower bound (2.30)–(2.31) are stated.
--
--   **Formalization Note** The recourse cost is an `EReal`-valued infimum over the feasible set, so the book's $\pm\infty$ values are represented exactly. Row, recourse and first-stage index sets are arbitrary finite types. The expected recourse function integrates the real part (`EReal.toReal`) of the recourse cost; it is meaningful when the cost is finite, which the theorems guarantee by carrying the standing assumptions (complete recourse, dual feasibility). The book writes $Q$ for both $Q(x,\xi)$ and $\mathcal Q(x)$; here they are `recourseCost` and `expectedRecourse`. The book reuses the names $\tilde Q$, $\tilde\psi$ of (2.27) for the minorant of (2.30); here it is `dualLowerBound`.
-- source:
--   P. Kall, A. Ruszczyński, K. Frauendorfer, "Approximation Techniques in Stochastic Programming", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 2, pp. 38-40, Eqs. (2.11)-(2.12), complete recourse and dual feasibility (p. 39), property (e) (p. 40); p. 43, Eq. (2.30)

import Mathlib

open MeasureTheory Matrix

namespace NumStochOpt.Bounds

/-- The second-stage (recourse) cost `Q(x, ξ)` of Kall–Ruszczyński–Frauendorfer (2.12), p. 38:
the optimal value of `minimize qᵀy subject to W y = h − T x, y ≥ 0`, as an extended real.
The infimum over an empty feasible set is `⊤ = +∞` (the book's convention on p. 39), and an
unbounded problem gives `⊥ = −∞`. Rows are indexed by `ι` (`m₂` constraints), recourse
variables by `κ` (`n₂`), first-stage variables by `ν` (`n₁`). -/
noncomputable def recourseCost {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (W : Matrix ι κ ℝ) (q : κ → ℝ) (h : ι → ℝ) (T : Matrix ι ν ℝ) (x : ν → ℝ) : EReal :=
  ⨅ y ∈ {y : κ → ℝ | 0 ≤ y ∧ W *ᵥ y = h - T *ᵥ x}, ((q ⬝ᵥ y : ℝ) : EReal)

/-- Complete recourse (p. 39): `{W y : y ≥ 0} = ℝ^{m₂}`, i.e. every right-hand side is
reachable by a nonnegative recourse decision. -/
def CompleteRecourse {ι κ : Type*} [Fintype κ] (W : Matrix ι κ ℝ) : Prop :=
  ∀ z : ι → ℝ, ∃ y : κ → ℝ, 0 ≤ y ∧ W *ᵥ y = z

/-- Dual feasibility of the cost vector `q` (p. 39): some `u ∈ ℝ^{m₂}` satisfies `Wᵀ u ≤ q`
componentwise; by LP duality this is what makes `Q(x, ξ) > −∞`. -/
def DualFeasible {ι κ : Type*} [Fintype ι] (W : Matrix ι κ ℝ) (q : κ → ℝ) : Prop :=
  ∃ u : ι → ℝ, W.transpose *ᵥ u ≤ q

/-- The expected recourse function `Q(x) = ∫_Ω Q(x, ξ(ω)) P(dω)` of (2.11) and property (e),
p. 40, for random data `ξ(ω) = (q(ω), h(ω), T(ω))`. The integrand is the real part of the
extended-real recourse cost; it is only meaningful where that cost is finite, which is what the
standing assumptions (complete recourse, dual feasibility) guarantee. -/
noncomputable def expectedRecourse {Ω ι κ ν : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    [Fintype ν] (P : Measure Ω) (W : Matrix ι κ ℝ) (q : Ω → κ → ℝ) (h : Ω → ι → ℝ)
    (T : Ω → Matrix ι ν ℝ) (x : ν → ℝ) : ℝ :=
  ∫ ω, (recourseCost W (q ω) (h ω) (T ω) x).toReal ∂P

/-- The dual-multiplier minorant of (2.30), p. 43: for multiplier vectors `u_1, …, u_L`
(`L ≥ 1`), the value `max_{1 ≤ ℓ ≤ L} (h − T x)ᵀ u_ℓ`. The book calls it `Q̃(x, ξ)`, a name it
already used for a different function in (2.27); here it is `dualLowerBound`. -/
noncomputable def dualLowerBound {ι ν : Type*} [Fintype ι] [Fintype ν] {L : ℕ} [NeZero L]
    (u : Fin L → ι → ℝ) (h : ι → ℝ) (T : Matrix ι ν ℝ) (x : ν → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun ℓ => (h - T *ᵥ x) ⬝ᵥ u ℓ

end NumStochOpt.Bounds


