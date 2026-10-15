-- Prove2me | Definitions.Def_MaintPOMDP_Frontier_Setting
-- name    : MaintPOMDP_Frontier_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T23:01:28.923908+00:00
-- url     : https://prove2.me/theorems/1cdb531b-165c-4448-b50e-a420771baaf0
-- title:
--   §4.1–§4.4 — the maintenance POMDP with obvious failures: dual value iteration (12)–(16), u^(Ṗ), the production recursion, f, g, (35), ĉ, uI†, Table 1's sets
-- statement:
--   This file sets up the two-state machine-maintenance model with obvious failures of Zhang and Zhang (§4.1, pp. 13–14) and every object that the paper's main results refer to.
--
--   **The model.** A machine is in a hidden state $x\in\{0,1\}$ (good or bad) or in the observable failure state $F$. The parameters are costs $c^P, c^I, c^R, c^F$ and probabilities $\gamma_0,\gamma_1$ and a discount factor $\beta$. The **standing assumptions** are
--   $$0<\beta<1,\qquad 0<c^P<c^I<c^R<c^F,\qquad 0<\gamma_0<1,\quad 0<\gamma_1<1 .$$
--   Write $\bar\gamma_x=1-\gamma_x$, $\rho_x=\beta\bar\gamma_x$, $\bar\rho_x=1-\rho_x$, $\mathbf p_0=(\bar\gamma_0,\gamma_0)'$, $\mathbf p_1=(0,\bar\gamma_1)'$, $\mathbf g^P(u_F)=(0,c^P+\beta\gamma_1u_F)'$, $\mathbf g^I(u_F)=(c^I,c^I+\beta\gamma_1u_F)'$, and $\mathbf P^P\mathbf u=(\mathbf p_0'\mathbf u,\mathbf p_1'\mathbf u)'$; its transpose acts on beliefs as $(\mathbf P^P)'\boldsymbol\pi=(\bar\gamma_0\pi_0,\gamma_0\pi_0+\bar\gamma_1\pi_1)'$.
--
--   **Value iteration.** A pair $(W,w_F)$, where $W(\boldsymbol\pi)=\min_{\mathbf u\in U}\boldsymbol\pi'\mathbf u$ is the support function of a frontier $U$ on unnormalized beliefs $\boldsymbol\pi\ge0$ and $w_F$ is the cost after a failure, is mapped by the dual value iteration (12)–(16) to $(W',w_F')$ with
--   $$W'(\boldsymbol\pi)=\min\Big\{\boldsymbol\pi'\mathbf g^P(w_F)+\beta W\big((\mathbf P^P)'\boldsymbol\pi\big),\ (\pi_0+\pi_1)\big(c^R+\beta W(\mathbf p_0)\big),\ \boldsymbol\pi'\mathbf g^I(w_F)+\beta\big(\pi_0W(\mathbf p_0)+\pi_1W(\mathbf p_1)\big)\Big\},\qquad w_F'=c^F+\beta W(\mathbf p_0).$$
--   The three terms belong to production $P$, replacement $R$ and inspection $I$; the action set $\{P,R\}$ drops the third term and $\{P\}$ keeps only the first. The iterates start from $W\equiv0$, $w_F=0$ (Example 1). A finite nonempty set $U$ with a number $u_F$ **solves** the model with action set $A$ if the iterates converge to $\min_{\mathbf u\in U}\boldsymbol\pi'\mathbf u$ for every $\boldsymbol\pi\ge0$ and to $u_F$ in the failure coordinate.
--
--   **Geometry.** $U$ is an **extreme set** if every point of $U$ is the unique minimizer of $\boldsymbol\pi'\mathbf u$ over $U$ for some $\boldsymbol\pi$ in the closed simplex (§3.3); $\mathbf z$ is **dominated** by $U$ if $\min_U\boldsymbol\pi'\mathbf u\le\boldsymbol\pi'\mathbf z$ for every $\boldsymbol\pi$ in the simplex; $\mathbf z$ lies **on the frontier** of $U$ if it belongs to $NCo(U)$ of Definition 1 (p. 9), the closure of the points of the convex hull minimizing $\boldsymbol\pi'\cdot$ over it for some strictly positive normalized $\boldsymbol\pi$.
--
--   **Sequences and anchors.** The production sequence is $\mathbf u_{i+1}=\mathbf g^P(u_F)+\beta\mathbf P^P\mathbf u_i$; the inspection start (35) is $\mathbf u^I_0=(u^R_0-c^R+c^I,\ c^I+\beta\gamma_1u_F+\rho_1u^R_0)'$. The anchor $f(m)$ is the unique solution $u^R$ of $u^R=c^R+\beta\mathbf p_0'\mathbf u_m$, where $\mathbf u_0=(u^R,u^R)'$ and $u_F=u^R+c^F-c^R$ (Lemma 3); $g(m)$ is the same with the sequence started at the inspection point (Lemma 7). The right-hand side is affine in $u^R$ with slope in $[0,\beta]$, so the solution is intercept$/(1-$slope$)$. The printed closed forms (29)–(31) and (38)–(40) are separate definitions.
--
--   **Named points.** With $D=1-\beta+\beta(\gamma_0+\gamma_1)$:
--   $$\mathbf u^{(\dot P)}=\frac{c^P+\beta\gamma_1c^F}{(1-\beta)D}\begin{pmatrix}\beta\gamma_0\\1-\beta+\beta\gamma_0\end{pmatrix},\quad u_F^{(\dot P)}=u_0^{(\dot P)}+c^F,\quad \mathbf u^{(R\dot P)}=(c^R+u_0^{(\dot P)})\mathbf 1,$$
--   Table 1's point $\mathbf u^I=\big(c^I+u_0^{(\dot P)},\ c^I+\beta\bar\gamma_1(c^R+u_0^{(\dot P)})+\beta\gamma_1(c^F+u_0^{(\dot P)})\big)'$, the threshold $(c^P+\beta\gamma_1c^F)/D$,
--   $$\hat c=(1+\beta\gamma_0)c^P-\beta\bar\gamma_1(1-\beta+\beta\gamma_0+\beta\gamma_1)c^R+\beta^2\gamma_1\bar\gamma_1c^F,$$
--   and $\mathbf u^{I\dagger}=(u^\dagger_0-c^R+c^I,\ c^I+\beta\gamma_1(c^F-c^R)+\beta u^\dagger_0)'$. The frontier sets of Table 1 are $U^\dagger(m)=\{\mathbf u_0,\dots,\mathbf u_{m+1}\}$ from $\mathbf u_0=(f(m),f(m))'$; the $[PIR]$ set $\{\mathbf u^R_0,\dots,\mathbf u^R_{n_R}\}\cup\{\mathbf u^I_0,\dots,\mathbf u^I_{n_I}\}$ from the anchor $g(m)$; and the $I[PR]$ set $U^\dagger(m)\cup\{\mathbf u^I_0,\dots,\mathbf u^I_{n_I}\}$ with $\mathbf u^I_0=\mathbf u^{I\dagger}$.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** Vectors and beliefs are `Fin 2 → ℝ` (index 0 = good state). The paper's optimal solution $(U^*,u^*_F)$ is the fixed point of (12)–(16) reached by value iteration (§4.2, p. 16); here it is the limit of the support-function iterates from zero terminal costs, which carry the same information as the extreme-point sets because $NCoEx$ does not change minima. The ranges $0<\gamma_0,\gamma_1<1$ are not stated in the paper and are added. $f$ and $g$ are defined through the anchor equations, so they are valid also for $\gamma_0=\gamma_1$, where the closed forms are $0/0$.
-- source:
--   Zhang, Zhang, Analytical Solution to a Partially Observable Machine Maintenance Problem with Obvious Failures, SSRN 2945049 (version of 2022-08-21), pp. 9–29: Definition 1 (p. 9), §3.3 (p. 12), §4.1 (4)–(6), (12)–(16) (p. 14), (17) (p. 16), Proposition 2 (p. 17), (23)–(24) (p. 18), p. 19, (29)–(31), (35)–(40), Theorem 2 (pp. 27–28), Table 1 (p. 29)

import Mathlib

namespace MaintPOMDP.Frontier

noncomputable section

open Filter Topology

/-- Cost-to-go vectors `u = (u₀, u₁)` and (unnormalized) beliefs `π = (π₀, π₁)`;
index `0` is the good state, index `1` the bad state. -/
abbrev Vec := Fin 2 → ℝ

/-- The inner product `π′u = π₀ u₀ + π₁ u₁`. -/
def dot (π u : Vec) : ℝ := π 0 * u 0 + π 1 * u 1

/-- The vector `(x, x)′` on the 45° ray. -/
def diag (x : ℝ) : Vec := ![x, x]

/-- The model primitives of §4.1 (pp. 13–14): costs `cP, cI, cR, cF`, deterioration
probabilities `γ0` (state 0 → 1) and `γ1` (state 1 → failure `F`), discount factor `β`. -/
structure Params where
  cP : ℝ
  cI : ℝ
  cR : ℝ
  cF : ℝ
  γ0 : ℝ
  γ1 : ℝ
  β : ℝ

/-- The three action sets used in the paper: `{P}` (the stationary policy `(Ṗ)`),
`{P, R}` (§4.3) and `{P, I, R}` (§4.1, §4.4). -/
inductive ActSet
  | P
  | PR
  | PIR

namespace Params

variable (M : Params)

/-- Standing assumptions: `0 < β < 1` (p. 14, (6)), `0 < cP < cI < cR < cF` (p. 14, (4)), and
`0 < γ0 < 1`, `0 < γ1 < 1` (never stated in the paper; needed for `γ0/γ1` and for the
probabilities to be nondegenerate). -/
def Standing : Prop :=
  0 < M.β ∧ M.β < 1 ∧ 0 < M.cP ∧ M.cP < M.cI ∧ M.cI < M.cR ∧ M.cR < M.cF ∧
    0 < M.γ0 ∧ M.γ0 < 1 ∧ 0 < M.γ1 ∧ M.γ1 < 1

/-- The same model with the inspection cost replaced by `c`. -/
def withCI (c : ℝ) : Params := { M with cI := c }

/-- `γ̄0 = 1 − γ0`. -/
def γ0bar : ℝ := 1 - M.γ0
/-- `γ̄1 = 1 − γ1`. -/
def γ1bar : ℝ := 1 - M.γ1
/-- `ρ0 = β γ̄0`. -/
def ρ0 : ℝ := M.β * M.γ0bar
/-- `ρ1 = β γ̄1`. -/
def ρ1 : ℝ := M.β * M.γ1bar
/-- `ρ̄0 = 1 − ρ0`. -/
def ρ0bar : ℝ := 1 - M.ρ0
/-- `ρ̄1 = 1 − ρ1`. -/
def ρ1bar : ℝ := 1 - M.ρ1

/-- `p0 = (γ̄0, γ0)′`, the transition row out of the good state. -/
def p0 : Vec := ![M.γ0bar, M.γ0]
/-- `p1 = (0, γ̄1)′`, the transition row out of the bad state into `X = {0, 1}`
(it does not sum to one: the rest of the mass goes to the failure state). -/
def p1 : Vec := ![0, M.γ1bar]

/-- `gP(uF) = (0, cP + β γ1 uF)′`. -/
def gP (uF : ℝ) : Vec := ![0, M.cP + M.β * M.γ1 * uF]
/-- `gI(uF) = (cI, cI + β γ1 uF)′`. -/
def gI (uF : ℝ) : Vec := ![M.cI, M.cI + M.β * M.γ1 * uF]

/-- `P^P u = (p0′u, p1′u)′`, the production transition matrix acting on cost vectors. -/
def PP (u : Vec) : Vec := ![dot M.p0 u, dot M.p1 u]
/-- `(P^P)′π = (γ̄0 π0, γ0 π0 + γ̄1 π1)′`, its transpose acting on beliefs. -/
def PPt (π : Vec) : Vec := ![M.γ0bar * π 0, M.γ0 * π 0 + M.γ1bar * π 1]

/-- One step of the dual value iteration (12)–(16), in support-function form.
A pair `(W, wF)` stands for `(π ↦ min_{u ∈ U} π′u, u_F)`. The new pair is
`W′(π) = min` of the terms of the available actions, where
* P-term: `π′gP(wF) + β W((P^P)′π)`;
* R-term: `(π0 + π1)(cR + β W(p0))`;
* I-term: `π′gI(wF) + β (π0 W(p0) + π1 W(p1))`;

and `wF′ = cF + β W(p0)` (16). -/
def bellman (A : ActSet) (V : (Vec → ℝ) × ℝ) : (Vec → ℝ) × ℝ :=
  let W := V.1
  let wF := V.2
  let tP : Vec → ℝ := fun π => dot π (M.gP wF) + M.β * W (M.PPt π)
  let tR : Vec → ℝ := fun π => (π 0 + π 1) * (M.cR + M.β * W M.p0)
  let tI : Vec → ℝ := fun π => dot π (M.gI wF) + M.β * (π 0 * W M.p0 + π 1 * W M.p1)
  (fun π =>
      match A with
      | ActSet.P => tP π
      | ActSet.PR => min (tP π) (tR π)
      | ActSet.PIR => min (min (tP π) (tR π)) (tI π),
    M.cF + M.β * W M.p0)

/-- The `n`-th value-iteration iterate, started from zero terminal costs
`U*_{T+1} = {0}`, `u*_{T+1,F} = 0` (Example 1). -/
def VI (A : ActSet) (n : ℕ) : (Vec → ℝ) × ℝ :=
  (M.bellman A)^[n] (fun _ => 0, 0)

end Params

/-- `min_{u ∈ U} π′u` for a nonempty finite set `U` (and `0` for the empty set, which is
never used: every statement below requires `U` nonempty). -/
def minDot (U : Finset Vec) (π : Vec) : ℝ :=
  if h : U.Nonempty then U.inf' h (dot π) else 0

/-- `π` lies in the closed simplex `Π = {π : π_i ≥ 0, π0 + π1 = 1}`. -/
def InSimplex (π : Vec) : Prop := 0 ≤ π 0 ∧ 0 ≤ π 1 ∧ π 0 + π 1 = 1

/-- `NCoEx(U) = U` for a finite set (§3.3, p. 12): every `u ∈ U` is the strict unique
minimizer of `π′·` over `U` for some `π` in the closed simplex. -/
def IsExtremeSet (U : Finset Vec) : Prop :=
  ∀ u ∈ U, ∃ π : Vec, InSimplex π ∧ ∀ z ∈ U, z ≠ u → dot π u < dot π z

/-- `z` is (weakly) dominated by `U`: along every direction `π` of the closed simplex,
some point of `U` is at least as good as `z`. -/
def Dominated (z : Vec) (U : Finset Vec) : Prop :=
  ∀ π : Vec, InSimplex π → minDot U π ≤ dot π z

/-- `z` lies on the efficient frontier `NCo(U)` of Definition 1 (p. 9): the closure of the
set of points of the convex hull `Co(U)` minimizing `π′·` over `Co(U)` for some `π` with
strictly positive entries summing to one. -/
def OnFrontier (z : Vec) (U : Finset Vec) : Prop :=
  z ∈ closure {u : Vec | u ∈ convexHull ℝ (U : Set Vec) ∧
    ∃ π : Vec, (0 < π 0 ∧ 0 < π 1 ∧ π 0 + π 1 = 1) ∧
      ∀ z' ∈ convexHull ℝ (U : Set Vec), dot π u ≤ dot π z'}

/-- `m` is the least minimizer of `h` over `ℕ`. -/
def IsLeastMin (h : ℕ → ℝ) (m : ℕ) : Prop :=
  (∀ k, h m ≤ h k) ∧ ∀ k < m, h m < h k

namespace Params

variable (M : Params)

/-- "`(U, uF)` is the optimal solution under the action set `A`", at the value level:
`U` is a nonempty finite set, and value iteration from zero converges, for every belief
`π ≥ 0`, to `min_{u ∈ U} π′u`, and in the failure coordinate to `uF`. -/
def Solves (A : ActSet) (U : Finset Vec) (uF : ℝ) : Prop :=
  U.Nonempty ∧
    (∀ π : Vec, 0 ≤ π 0 → 0 ≤ π 1 →
      Tendsto (fun n => (M.VI A n).1 π) atTop (𝓝 (minDot U π))) ∧
    Tendsto (fun n => (M.VI A n).2) atTop (𝓝 uF)

/-- The production recursion (p. 19, (36)–(37)): `u_0` given and
`u_{i+1} = gP(uF) + β P^P u_i`. -/
def prodSeq (u0 : Vec) (uF : ℝ) : ℕ → Vec
  | 0 => u0
  | i + 1 => M.gP uF + M.β • M.PP (prodSeq u0 uF i)

/-- The inspection start point (35) with a free `uF` (middle form):
`u^I_0 = (uR0 − cR + cI, cI + β γ1 uF + ρ1 uR0)′`. -/
def inspStart (uR0 uF : ℝ) : Vec :=
  ![uR0 - M.cR + M.cI, M.cI + M.β * M.γ1 * uF + M.ρ1 * uR0]

/-- The right-hand side of the anchor equation of Lemma 3,
`x ↦ cR + β p0′u_m` where `u_0 = (x, x)′`, `uF = x + cF − cR`. It is affine in `x`. -/
def anchorF (m : ℕ) (x : ℝ) : ℝ :=
  M.cR + M.β * dot M.p0 (M.prodSeq (diag x) (x + M.cF - M.cR) m)

/-- The right-hand side of the anchor equation of Lemma 7,
`x ↦ cR + β p0′u^I_m` where `u^I_0` is (35) at `uR0 = x`, `uF = x + cF − cR`. -/
def anchorG (m : ℕ) (x : ℝ) : ℝ :=
  M.cR + M.β * dot M.p0 (M.prodSeq (M.inspStart x (x + M.cF - M.cR)) (x + M.cF - M.cR) m)

/-- `f(m)`: the solution `uR` of the affine equation `uR = anchorF m uR`, written as
intercept / (1 − slope). The slope lies in `[0, β]`, so the denominator is positive. -/
def f (m : ℕ) : ℝ :=
  M.anchorF m 0 / (1 - (M.anchorF m 1 - M.anchorF m 0))

/-- `g(m)`: the solution `uR0` of the affine equation `uR0 = anchorG m uR0`. -/
def g (m : ℕ) : ℝ :=
  M.anchorG m 0 / (1 - (M.anchorG m 1 - M.anchorG m 0))

/-- The closed form (29)–(30) of Lemma 1. -/
def seq29_30 (uR uF : ℝ) (i : ℕ) : Vec :=
  let K := M.cP + M.β * M.γ1 * uF
  ![M.γ1 / (M.γ1 - M.γ0) * (uR - M.γ0 / M.γ1 * K / M.ρ0bar) * M.ρ0 ^ i
      - M.γ0 / (M.γ1 - M.γ0) * (uR - K / M.ρ1bar) * M.ρ1 ^ i
      + M.β * M.γ0 * K / (M.ρ0bar * M.ρ1bar),
    (uR - K / M.ρ1bar) * M.ρ1 ^ i + K / M.ρ1bar]

/-- The closed form (31) of `f(m)`. -/
def f31 (m : ℕ) : ℝ :=
  (M.ρ0bar * M.ρ1bar * M.cR
      + (M.β * M.γ0 + M.γ0 / (M.γ1 - M.γ0)
          * (M.ρ0bar * M.ρ1 ^ (m + 1) - M.ρ1bar * M.ρ0 ^ (m + 1)))
        * (M.cP + M.β * M.γ1 * (M.cF - M.cR)))
    / (M.ρ0bar * M.ρ1bar - M.β ^ 2 * M.γ0 * M.γ1
        - (1 - M.β) / (M.γ1 - M.γ0)
          * (M.γ1 * M.ρ1bar * M.ρ0 ^ (m + 1) - M.γ0 * M.ρ0bar * M.ρ1 ^ (m + 1)))

/-- The closed form (31) read on a real variable `m`, with `ρ^(m+1)` a real power. -/
def f31R (m : ℝ) : ℝ :=
  (M.ρ0bar * M.ρ1bar * M.cR
      + (M.β * M.γ0 + M.γ0 / (M.γ1 - M.γ0)
          * (M.ρ0bar * M.ρ1 ^ (m + 1) - M.ρ1bar * M.ρ0 ^ (m + 1)))
        * (M.cP + M.β * M.γ1 * (M.cF - M.cR)))
    / (M.ρ0bar * M.ρ1bar - M.β ^ 2 * M.γ0 * M.γ1
        - (1 - M.β) / (M.γ1 - M.γ0)
          * (M.γ1 * M.ρ1bar * M.ρ0 ^ (m + 1) - M.γ0 * M.ρ0bar * M.ρ1 ^ (m + 1)))

/-- The closed form (38)–(39) of Lemma 6. -/
def seq38_39 (uR0 uF : ℝ) (i : ℕ) : Vec :=
  let K := M.cP + M.β * M.γ1 * uF
  let d := M.γ1 - M.γ0
  ![(M.γ1 / d * M.cI - M.cR + M.γ0 / d * (M.β * M.γ1 * uF)
        + (1 + M.γ0 / d * M.ρ1) * uR0 - M.γ0 / d * (K / M.ρ0bar)) * M.ρ0 ^ i
      - M.γ0 / d * (M.cI + M.β * M.γ1 * uF + M.ρ1 * uR0 - K / M.ρ1bar) * M.ρ1 ^ i
      + M.β * M.γ0 * (K / (M.ρ0bar * M.ρ1bar)),
    (M.cI + M.β * M.γ1 * uF + M.ρ1 * uR0 - K / M.ρ1bar) * M.ρ1 ^ i + K / M.ρ1bar]

/-- The numerator term `a(m)` of (40). -/
def a40 (m : ℕ) : ℝ :=
  -(M.ρ0bar * M.ρ1bar * M.ρ0 ^ (m + 1) * M.cR)
    + M.ρ0bar * M.ρ1bar * ((M.γ1 * M.ρ0 ^ (m + 1) - M.γ0 * M.ρ1 ^ (m + 1)) / (M.γ1 - M.γ0))
      * M.cI
    + M.γ0 * (M.ρ0bar * M.ρ1 ^ (m + 1) - M.ρ1bar * M.ρ0 ^ (m + 1)) / (M.γ1 - M.γ0) * M.cP
    + M.β * M.γ0 * M.γ1 * (M.ρ0bar * M.ρ1 ^ (m + 2) - M.ρ1bar * M.ρ0 ^ (m + 2))
      / (M.γ1 - M.γ0) * (M.cF - M.cR)

/-- The closed form (40) of `g(m)`. -/
def g40 (m : ℕ) : ℝ :=
  let d := M.γ1 - M.γ0
  (M.ρ0bar * M.ρ1bar * M.cR + M.β * M.γ0 * (M.cP + M.β * M.γ1 * (M.cF - M.cR)) + M.a40 m)
    / (M.ρ0bar * M.ρ1bar - M.β ^ 2 * M.γ0 * M.γ1
        + (1 - M.β) / d * (M.γ0 * M.ρ0bar - M.γ1) * M.ρ1bar * M.ρ0 ^ (m + 1)
        + (1 - M.β) / d * M.γ0 * M.ρ0bar * M.ρ1 ^ (m + 2))

/-- `D = 1 − β + β(γ0 + γ1)`. -/
def D : ℝ := 1 - M.β + M.β * (M.γ0 + M.γ1)

/-- The replacement threshold `(cP + β γ1 cF) / (1 − β + β(γ0 + γ1))` of Theorems 1 and 2. -/
def thrP : ℝ := (M.cP + M.β * M.γ1 * M.cF) / M.D

/-- `u^(Ṗ)` (23): `(cP + βγ1cF) / ((1 − β)[1 − β + β(γ0 + γ1)]) · (βγ0, 1 − β + βγ0)′`. -/
def uPdot : Vec :=
  let K := (M.cP + M.β * M.γ1 * M.cF) / ((1 - M.β) * M.D)
  ![K * (M.β * M.γ0), K * (1 - M.β + M.β * M.γ0)]

/-- `u_F^(Ṗ) = u_0^(Ṗ) + cF` (24). -/
def uFPdot : ℝ := M.uPdot 0 + M.cF

/-- `u^(RṖ) = (cR + u_0^(Ṗ), cR + u_0^(Ṗ))′` (Theorem 1(2)). -/
def uRPdot : Vec := diag (M.cR + M.uPdot 0)

/-- Table 1's `IR[P]` point
`u^I = (cI + u_0^(Ṗ), cI + β γ̄1 (cR + u_0^(Ṗ)) + β γ1 (cF + u_0^(Ṗ)))′`. -/
def uIRP : Vec :=
  ![M.cI + M.uPdot 0,
    M.cI + M.β * M.γ1bar * (M.cR + M.uPdot 0) + M.β * M.γ1 * (M.cF + M.uPdot 0)]

/-- `ĉ = (1 + βγ0) cP − β γ̄1 (1 − β + βγ0 + βγ1) cR + β² γ1 γ̄1 cF` (Theorem 2). -/
def chat : ℝ :=
  (1 + M.β * M.γ0) * M.cP - M.β * M.γ1bar * (1 - M.β + M.β * M.γ0 + M.β * M.γ1) * M.cR
    + M.β ^ 2 * M.γ1 * M.γ1bar * M.cF

/-- `u^{I†} = (u†_0 − cR + cI, cI + βγ1(cF − cR) + β u†_0)′` (Theorem 2), for the anchor
value `u†_0`. -/
def uIdag (u0dag : ℝ) : Vec :=
  ![u0dag - M.cR + M.cI, M.cI + M.β * M.γ1 * (M.cF - M.cR) + M.β * u0dag]

/-- Theorem 1(3)'s frontier `U† = {u_i : i = 0, …, n†}`, `n† = m + 1`, with
`u_0 = (f(m), f(m))′` and `u†_F = f(m) + cF − cR`. -/
def Udag (m : ℕ) : Finset Vec :=
  (Finset.range (m + 2)).image (M.prodSeq (diag (M.f m)) (M.f m + M.cF - M.cR))

/-- Table 1's `[PIR]` set `{u^R_0, …, u^R_{nR}} ∪ {u^I_0, …, u^I_{nI}}`, with
`u^R_0 = (g(m), g(m))′`, `u*_F = g(m) + cF − cR`, `u^I_0` by (35), both sequences by (36)–(37). -/
def UPIR (m nR nI : ℕ) : Finset Vec :=
  (Finset.range (nR + 1)).image (M.prodSeq (diag (M.g m)) (M.g m + M.cF - M.cR)) ∪
    (Finset.range (nI + 1)).image
      (M.prodSeq (M.inspStart (M.g m) (M.g m + M.cF - M.cR)) (M.g m + M.cF - M.cR))

/-- Table 1's `I[PR]` set `U† ∪ {u^I_0, …, u^I_{nI}}`, with `U† = Udag m`,
`u^I_0 = u^{I†}` and the inspection sequence by (37) with `u†_F = f(m) + cF − cR`. -/
def UIPR (m nI : ℕ) : Finset Vec :=
  M.Udag m ∪
    (Finset.range (nI + 1)).image (M.prodSeq (M.uIdag (M.f m)) (M.f m + M.cF - M.cR))

/-- The `[PIR]` row of Table 1 at the value level: some minimizer `m*` of `g` over `ℕ` and some
indices `nR, nI` such that `(UPIR m* nR nI, g(m*) + cF − cR)` solves the `{P, I, R}` model. -/
def PIRStructure : Prop :=
  ∃ mstar : ℕ, (∀ m, M.g mstar ≤ M.g m) ∧
    ∃ nR nI : ℕ, M.Solves ActSet.PIR (M.UPIR mstar nR nI) (M.g mstar + M.cF - M.cR)

end Params

end

end MaintPOMDP.Frontier


