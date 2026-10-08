-- Prove2me | Definitions.Def_MyersonAuction_Optimal_Ironing
-- name    : MyersonAuction_Optimal_Ironing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:46:28.206098+00:00
-- url     : https://prove2.me/theorems/41425cc6-eab3-4774-9cdd-ccddd7a93d93
-- title:
--   Convex-envelope ironing and Myerson’s optimal allocation and payments
-- statement:
--   For bidder $i$, transform the virtual value to quantiles by $h_i(q)=c_i(F_i^{-1}(q))$ and integrate it to $H_i(q)=\int_0^q h_i(r)\,dr$. Let $G_i$ be the convex envelope of $H_i$ on $[0,1]$, let $g_i$ be its right-continuous slope, and define the ironed priority $\bar c_i(s)=g_i(F_i(s))$. At a profile $t$, the set $M(t)$ consists of bidders whose priority is maximal and at least the seller’s value $t_0$. The proposed allocation and payment are
--
--   $$
--   \bar p_i(t)=\mathbf 1_{\{i\in M(t)\}}/|M(t)|,\qquad
--   \bar x_i(t)=\bar p_i(t)v_i(t)-\int_{a_i}^{t_i}\bar p_i(t_{-i},s)\,ds.
--   $$
--
--   These are the auction rule and payment formula in the source theorem. If $M(t)$ is empty, the seller keeps the object.
--
--   **Formalization Note** $F_i^{-1}$ is the infimum of supported types whose CDF reaches $q$. $G_i$ is the two-point infimum in (6.3). Below $q=1$, $g_i$ is the right derivative; at $1$ it is the left derivative. The indicator formula is shorthand for the branch in (6.7), so no division occurs when $M(t)$ is empty.
-- source:
--   Myerson, Optimal Auction Design, Math. Oper. Res. 6(1) (1981), pp. 68–69, §6, eqs. (6.1)–(6.8)

import Definitions.Def_MyersonAuction_Optimal_Mechanism

noncomputable section

namespace MyersonAuction.Optimal

open MeasureTheory

/-- The inverse of the strictly increasing CDF on its supported range. -/
def inverseF {ι : Type} [Fintype ι] (E : Environment ι) (i : ι) (q : ℝ) : ℝ :=
  sInf {s : ℝ | s ∈ Set.Icc (E.a i) (E.b i) ∧ q ≤ F E i s}

/-- The quantile form (6.1) of the virtual value. -/
def h {ι : Type} [Fintype ι] (E : Environment ι) (i : ι) (q : ℝ) : ℝ :=
  let s := inverseF E i q
  s - E.e i s - (1 - q) / E.f i s

/-- The primitive (6.2). -/
def H {ι : Type} [Fintype ι] (E : Environment ι) (i : ι) (q : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..q, h E i r

/-- The two-point convex envelope (6.3) on `[0,1]`. -/
def G {ι : Type} [Fintype ι] (E : Environment ι) (i : ι) (q : ℝ) : ℝ :=
  sInf {z : ℝ | ∃ w r₁ r₂ : ℝ,
    w ∈ Set.Icc 0 1 ∧ r₁ ∈ Set.Icc 0 1 ∧ r₂ ∈ Set.Icc 0 1 ∧
    w * r₁ + (1 - w) * r₂ = q ∧
    z = w * H E i r₁ + (1 - w) * H E i r₂}

/-- The right derivative of `G` on `[0,1)`, with the left derivative at `1`. -/
def g {ι : Type} [Fintype ι] (E : Environment ι) (i : ι) (q : ℝ) : ℝ :=
  if q < 1 then derivWithin (G E i) (Set.Ioi q) q
  else derivWithin (G E i) (Set.Iio 1) 1

/-- The ironed priority (6.5). -/
def ironedPriority {ι : Type} [Fintype ι]
    (E : Environment ι) (i : ι) (s : ℝ) : ℝ :=
  g E i (F E i s)

/-- Winners at profile `t` according to (6.6), including ties with `t₀`. -/
def winners {ι : Type} [Fintype ι]
    (E : Environment ι) (t : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => E.t0 ≤ ironedPriority E i (t i) ∧
    ∀ j, ironedPriority E j (t j) ≤ ironedPriority E i (t i))

/-- The tied optimal allocation (6.7). -/
def pbar {ι : Type} [Fintype ι]
    (E : Environment ι) : Outcome ι := by
  classical
  exact fun i t => if i ∈ winners E t then 1 / (winners E t).card else 0

/-- The envelope-form payment (6.8). -/
def xbar {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : Environment ι) : Outcome ι :=
  fun i t => pbar E i t * bidderValue E i t -
    ∫ s in E.a i..t i, pbar E i (Function.update t i s)

end MyersonAuction.Optimal


