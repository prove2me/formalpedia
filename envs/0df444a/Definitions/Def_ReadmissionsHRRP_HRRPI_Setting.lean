-- Prove2me | Definitions.Def_ReadmissionsHRRP_HRRPI_Setting
-- name    : ReadmissionsHRRP_HRRPI_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:28.069271+00:00
-- url     : https://prove2.me/theorems/3430bbc9-3def-4796-89f2-57173059a9f6
-- title:
--   §3–§4.1 — hospital yardstick model: action box, cost R and standing assumptions, welfare S (2), yardsticks (6), HRRP-I transfer (9), profit (1), Nash and symmetric equilibria
-- statement:
--   **Primitives.** Each of $N$ identical hospitals receives patients at rate $\lambda$. Hospital $i$ chooses a readmission rate $r_i\in[r_{\min},r_{\max}]$ and a marginal treatment cost $c_i\in[c_{\min},c_{\max}]$, and pays the investment cost $R(r_i,c_i)$ to reach them. Write $B=[r_{\min},r_{\max}]\times[c_{\min},c_{\max}]$ for the action box, $V(\lambda)$ (a fixed real number $V$) for the total patient utility, and $R_r,R_c,R_{rr},R_{cc},R_{rc},R_{cr}$ for the partial derivatives of $R$, the mixed ones taken in the order of the subscripts ($R_{rc}=\partial_c R_r$, $R_{cr}=\partial_r R_c$).
--
--   **Standing assumptions** (§3.1, p. 10): $0<r_{\min}\le r_{\max}<1$, $0\le c_{\min}<c_{\max}$, $\lambda>0$; $R$ is twice continuously differentiable on an open set containing $B$, decreasing in $r$ and in $c$ on $B$, and jointly convex on $B$; and at every point of $B$
--   $$R_{rr}R_{cc}>(R_{rc}+\lambda)^2,\qquad R_{cr}\ge 0 .$$
--   **Interior first best.** Every maximizer of the welfare $S$ (below) over $B$ lies in $(r_{\min},r_{\max})\times(c_{\min},c_{\max})$. This stands in for the boundary conditions of the paper's Appendix A.
--
--   **Welfare** (2): $S(r,c)=V(\lambda)-c(1+r)\lambda-R(r,c)$. A **first-best action** is a maximizer of $S$ over $B$.
--
--   **Yardsticks** (6): at a profile $x=((r_1,c_1),\dots,(r_N,c_N))$,
--   $$\bar c_i=\frac{1}{N-1}\sum_{k\ne i}c_k,\qquad \bar r_i=\frac{1}{N-1}\sum_{k\ne i}r_k,\qquad \bar R_i=\frac{1}{N-1}\sum_{k\ne i}R(r_k,c_k).$$
--   **HRRP-I transfer** (9) and **hospital profit** (1):
--   $$T_i=\bar c_i\lambda(1+r_i)-\frac{1}{\bar r_i}(r_i-\bar r_i)(1+r_i)\bar c_i\lambda+\bar R_i,\qquad \Pi_i=T_i-c_i(1+r_i)\lambda-R(r_i,c_i).$$
--   **Equilibria.** A profile is an **HRRP-I equilibrium** if it is a pure-strategy Nash equilibrium of the game in which hospital $i$ chooses $(r_i,c_i)\in B$ to maximize $\Pi_i$ against the others' actions. A point $(\tilde r,\tilde c)\in\mathbb R^2$ is a **symmetric equilibrium** if the profile in which every hospital plays it is an HRRP-I equilibrium.
--
--   These objects are the whole model behind Proposition 1: the yardsticks make each hospital's payment depend on the others' readmission rates and costs, and the factor $(1+r_i)/\bar r_i$ in (9) is the multiplier whose effect the proposition isolates.
--
--   **Formalization Note** $\lambda$ is a Lean keyword, so the arrival rate is `lam`. $R$ is curried, `R r c`. Partial derivatives are `deriv` of the sections of $R$; they are the true partials because $R$ is $C^2$ on an open set containing $B$. Profiles are maps `Fin N → ℝ × ℝ` with first coordinate $r_i$ and second $c_i$; the equilibrium is the published pure-Nash relation `CarbonDoubleCount.Planner.IsPureNash` (feasible profile, no profitable feasible unilateral deviation, deviation by `Function.update`) with every hospital's feasible set equal to $B$ and payoff $\Pi_i$; the averages divide by the real number $N-1$, and every theorem assumes $N\ge 2$. "Decreasing" is read as non-increasing in each variable on $B$. The interiority hypothesis `FirstBestInterior` replaces Appendix A, which is not part of the cited manuscript; the paper states that Appendix A's conditions ensure interior optima, so the hypothesis is implied by the paper's assumptions.
-- source:
--   Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the right incentives: Issues and remedies, author-accepted manuscript, LBS Research Online eprint 1402 (Management Science 67(4), 2021, doi:10.1287/mnsc.2020.3649), pp. 9–14, §3.1 (1), (2), standing assumptions p. 10; §3.2 (6); §4.1 (9)

import Mathlib
import Definitions.Def_CarbonDoubleCount_Planner_PureGame

namespace ReadmissionsHRRP.HRRPI

/-- The primitives of the hospital model (§3.1, pp. 9–10): the patient arrival rate `lam` (λ),
the total patient utility `V` (V(λ)), the bounds of the action box
`[rmin, rmax] × [cmin, cmax]`, and the investment cost `R r c` (R(r, c)). -/
structure Model where
  lam : ℝ
  V : ℝ
  rmin : ℝ
  rmax : ℝ
  cmin : ℝ
  cmax : ℝ
  R : ℝ → ℝ → ℝ

/-- Yardstick (6): `c̄_i = (1/(N − 1)) Σ_{k ≠ i} c_k` at the profile `x` (`(x k).2 = c_k`). -/
noncomputable def cbar (N : ℕ) (x : Fin N → ℝ × ℝ) (i : Fin N) : ℝ :=
  (1 / ((N : ℝ) - 1)) * ∑ k ∈ Finset.univ.erase i, (x k).2

/-- Yardstick (6): `r̄_i = (1/(N − 1)) Σ_{k ≠ i} r_k` at the profile `x` (`(x k).1 = r_k`). -/
noncomputable def rbar (N : ℕ) (x : Fin N → ℝ × ℝ) (i : Fin N) : ℝ :=
  (1 / ((N : ℝ) - 1)) * ∑ k ∈ Finset.univ.erase i, (x k).1

namespace Model

variable (M : Model)

/-- The action box `[rmin, rmax] × [cmin, cmax]`; a point is `(r, c)`. -/
def box : Set (ℝ × ℝ) := Set.Icc M.rmin M.rmax ×ˢ Set.Icc M.cmin M.cmax

/-- Partial derivative `R_r(r, c)`. -/
noncomputable def Rr (r c : ℝ) : ℝ := deriv (fun r' => M.R r' c) r

/-- Partial derivative `R_c(r, c)`. -/
noncomputable def Rc (r c : ℝ) : ℝ := deriv (fun c' => M.R r c') c

/-- Second partial derivative `R_rr(r, c)`. -/
noncomputable def Rrr (r c : ℝ) : ℝ := deriv (fun r' => M.Rr r' c) r

/-- Second partial derivative `R_cc(r, c)`. -/
noncomputable def Rcc (r c : ℝ) : ℝ := deriv (fun c' => M.Rc r c') c

/-- Mixed partial `R_rc(r, c)`: the `c`-derivative of `R_r`. -/
noncomputable def Rrc (r c : ℝ) : ℝ := deriv (fun c' => M.Rr r c') c

/-- Mixed partial `R_cr(r, c)`: the `r`-derivative of `R_c`. -/
noncomputable def Rcr (r c : ℝ) : ℝ := deriv (fun r' => M.Rc r' c) r

/-- The regulator's objective, total social welfare (2): `S(r, c) = V(λ) − c(1 + r)λ − R(r, c)`. -/
def S (r c : ℝ) : ℝ := M.V - c * (1 + r) * M.lam - M.R r c

/-- The standing assumptions of §3.1 (p. 10): `0 < rmin ≤ rmax < 1`, `0 ≤ cmin < cmax`, `λ > 0`;
`R` is twice continuously differentiable on an open set containing the box, decreasing in `r` and
in `c` on the box, jointly convex on the box; and on the box `R_rr R_cc > (R_rc + λ)²` and
`R_cr ≥ 0`. -/
def Standing : Prop :=
  0 < M.rmin ∧ M.rmin ≤ M.rmax ∧ M.rmax < 1 ∧ 0 ≤ M.cmin ∧ M.cmin < M.cmax ∧ 0 < M.lam ∧
  (∃ U : Set (ℝ × ℝ), IsOpen U ∧ M.box ⊆ U ∧
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => M.R p.1 p.2) U) ∧
  (∀ c ∈ Set.Icc M.cmin M.cmax, AntitoneOn (fun r => M.R r c) (Set.Icc M.rmin M.rmax)) ∧
  (∀ r ∈ Set.Icc M.rmin M.rmax, AntitoneOn (fun c => M.R r c) (Set.Icc M.cmin M.cmax)) ∧
  ConvexOn ℝ M.box (fun p : ℝ × ℝ => M.R p.1 p.2) ∧
  (∀ p ∈ M.box, (M.Rrc p.1 p.2 + M.lam) ^ 2 < M.Rrr p.1 p.2 * M.Rcc p.1 p.2) ∧
  (∀ p ∈ M.box, 0 ≤ M.Rcr p.1 p.2)

/-- `xs` is a first-best action: a maximizer of the welfare `S` over the box. -/
def IsFirstBest (xs : ℝ × ℝ) : Prop :=
  xs ∈ M.box ∧ ∀ y ∈ M.box, M.S y.1 y.2 ≤ M.S xs.1 xs.2

/-- Replacement for the boundary conditions of Appendix A (p. 10: "to ensure that optimal actions
are interior"): every maximizer of `S` over the box lies in `(rmin, rmax) × (cmin, cmax)`. -/
def FirstBestInterior : Prop :=
  ∀ x : ℝ × ℝ, M.IsFirstBest x →
    x.1 ∈ Set.Ioo M.rmin M.rmax ∧ x.2 ∈ Set.Ioo M.cmin M.cmax

/-- Yardstick (6): `R̄_i = (1/(N − 1)) Σ_{k ≠ i} R(r_k, c_k)` at the profile `x`. -/
noncomputable def Rbar (N : ℕ) (x : Fin N → ℝ × ℝ) (i : Fin N) : ℝ :=
  (1 / ((N : ℝ) - 1)) * ∑ k ∈ Finset.univ.erase i, M.R (x k).1 (x k).2

/-- The HRRP-I transfer (9):
`T_i = c̄_i λ (1 + r_i) − (1/r̄_i)(r_i − r̄_i)(1 + r_i) c̄_i λ + R̄_i`. -/
noncomputable def TI (N : ℕ) (x : Fin N → ℝ × ℝ) (i : Fin N) : ℝ :=
  cbar N x i * M.lam * (1 + (x i).1)
    - 1 / rbar N x i * ((x i).1 - rbar N x i) * (1 + (x i).1) * cbar N x i * M.lam
    + M.Rbar N x i

/-- Hospital `i`'s profit (1) under HRRP-I: `Π_i = T_i − c_i(1 + r_i)λ − R(r_i, c_i)`. -/
noncomputable def profitI (N : ℕ) (x : Fin N → ℝ × ℝ) (i : Fin N) : ℝ :=
  M.TI N x i - (x i).2 * (1 + (x i).1) * M.lam - M.R (x i).1 (x i).2

/-- Pure-strategy Nash equilibrium of the `N`-hospital game under HRRP-I: every hospital's action
lies in the box, and no hospital gains by a unilateral deviation within the box (the published
`CarbonDoubleCount.Planner.IsPureNash`, with every hospital's feasible set the box and payoff
`profitI`). -/
def IsEqI (N : ℕ) (x : Fin N → ℝ × ℝ) : Prop :=
  CarbonDoubleCount.Planner.IsPureNash (strategy := fun _ : Fin N => ℝ × ℝ)
    (fun _ => M.box) (fun i y => M.profitI N y i) x

/-- `(r̃, c̃) = p` is a symmetric equilibrium: the constant profile at `p` is an equilibrium. -/
def IsSymEqI (N : ℕ) (p : ℝ × ℝ) : Prop :=
  M.IsEqI N (fun _ => p)

end Model

end ReadmissionsHRRP.HRRPI


