-- Prove2me | Definitions.Def_OffloadGNEP_Exist_Setting
-- name    : OffloadGNEP_Exist_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:52.892951+00:00
-- url     : https://prove2.me/theorems/6eaf260c-5dca-443c-bd31-8f5437c1f311
-- title:
--   (10)–(15), Assumption A, K̃_u, Ω, K and F, pp. 10–11 — the offloading GNEP, its variational inequality and its solutions
-- statement:
--   This file fixes the objects of the computation-offloading game of Cardellini et al. (§§4–5.1).
--
--   There are $N$ users $u=1,\dots,N$ and three execution tiers $I=\{m,\mathrm{clet},\mathrm{cloud}\}$: the user's mobile device, a cloudlet of $n$ servers, and the distant cloud. User $u$ chooses the fractions $x_u=(x_{u,m},x_{u,\mathrm{clet}},x_{u,\mathrm{cloud}})$ of its tasks run on each tier; a **strategy profile** is $x=(x_1,\dots,x_N)\in\mathbb R^{3N}$, and $a^\top b=\sum_u\sum_{i\in I}a_{u,i}\,b_{u,i}$ denotes the Euclidean inner product of two profiles.
--
--   The data are numbers $\alpha_u,\beta_u,\gamma_u,\delta_u$ (the rescaled service and transfer rates of p. 10), powers $P_{u,m},P_{u,t},P_{u,\max}$, the number $n$ of cloudlet servers, the offloadable fraction $\chi$ and the utilisation cap $U_{\max}$.
--
--   1. **Assumption A** (p. 11): $U_{\max}$ and all $\alpha_u$, $\delta_u$ are positive and smaller than $1$. The **standing hypotheses** are $n\ge1$ (p. 7) and $0<\chi\le1$ (p. 9).
--   2. The **cloudlet load** is $\frac1n\sum_v\delta_v x_{v,\mathrm{clet}}$, and $D(x)=1-\frac1n\sum_v\delta_v x_{v,\mathrm{clet}}$.
--   3. User $u$'s private feasible set, with the joint constraint neglected, is
--   $$\tilde K_u=\Big\{x_u\in\mathbb R^3_+:\ \sum_{i\in I}x_{u,i}=1,\ x_{u,\mathrm{clet}}+x_{u,\mathrm{cloud}}\le\chi,\ \alpha_uP_{u,m}x_{u,m}+\beta_uP_{u,t}(x_{u,\mathrm{clet}}+x_{u,\mathrm{cloud}})\le P_{u,\max}\Big\}.$$
--   The shared constraint is $\Omega=\{x\in\mathbb R^{3N}:\frac1n\sum_u\delta_ux_{u,\mathrm{clet}}\le U_{\max}\}$, and $K=\big(\prod_u\tilde K_u\big)\cap\Omega$.
--   4. User $u$'s cost (10) is
--   $$\lambda_uR_u(x_u,x_{-u})=\frac{\alpha_ux_{u,m}}{1-\alpha_ux_{u,m}}+\beta_ux_{u,\mathrm{clet}}+\gamma_ux_{u,\mathrm{cloud}}+\frac{\delta_ux_{u,\mathrm{clet}}}{1-\frac1n\sum_v\delta_vx_{v,\mathrm{clet}}}.$$
--   5. The map $F:\mathbb R^{3N}\to\mathbb R^{3N}$ stacks the blocks
--   $$F(x)_u=\Big(\frac{\alpha_u}{(1-\alpha_ux_{u,m})^2},\ \beta_u+\delta_u\frac{1-\frac1n\sum_{v\ne u}\delta_vx_{v,\mathrm{clet}}}{\big(1-\frac1n\sum_v\delta_vx_{v,\mathrm{clet}}\big)^2},\ \gamma_u\Big).$$
--   6. A point $\bar x$ **solves the variational inequality** $\mathrm{VI}(S,G)$ if $\bar x\in S$ and $G(\bar x)^\top(x-\bar x)\ge0$ for all $x\in S$ (footnote 2). A **variational solution** of the game is a solution of $\mathrm{VI}(K,F)$.
--   7. A **solution of the GNEP** (10)–(15) is a profile $\bar x\in K$ such that for every user $u$ and every $y\in\tilde K_u$ with $(y,\bar x_{-u})\in\Omega$,
--   $$\lambda_uR_u(\bar x_u,\bar x_{-u})\le\lambda_uR_u(y,\bar x_{-u}).$$
--
--   These are the objects of Proposition 1 and of the milestones leading to it.
--
--   **Formalization Note** Users are indexed by `Fin N` (0-based). A profile is `x : Fin N → Tier → ℝ`, and the deviation $(y,\bar x_{-u})$ is `Function.update x u y`. The inner product is written out as a double sum, never through Mathlib's sup norm on Pi types. The cost and $F$ are given by the paper's closed forms; $F$ is **not** defined as a derivative, and the fact that it is the stacked partial gradient is a separate milestone. Both formulas contain divisions by $1-\alpha_ux_{u,m}$ and by $D(x)$; Lean returns $0$ on division by zero, but under Assumption A both denominators are positive on $K$ and at every point compared in the GNEP definition ($y_m\le1$ and $\alpha_u<1$; $D\ge1-U_{\max}>0$ on $\Omega$). The GNEP definition keeps the shared constraint $\Omega$ in each player's feasible set (dropping it would define a different game, a NEP). The paper's notion of a GNEP solution is the standard one of its references [16, 18]; it is not spelled out on the page. No positivity is assumed of $\beta_u,\gamma_u$ or the powers, as in the paper. The `Fintype` instance of `Tier` is written by hand because the `deriving Fintype` handler fails in this environment.
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), pp. 7, 9–11, (10)–(15), Assumption A, the definitions of K̃_u, Ω, K, F, footnote 2

import Mathlib

namespace OffloadGNEP.Exist

/-- The three places a task can be executed (p. 8): the mobile device `m`, the cloudlet `clet`
and the distant cloud `cloud`. The paper's index set is `I = {m, clet, cloud}`. -/
inductive Tier | m | clet | cloud
  deriving DecidableEq

/-- `Tier` is finite with exactly the three elements `m`, `clet`, `cloud`. (Written by hand: the
`deriving Fintype` handler fails in this environment.) -/
instance : Fintype Tier :=
  ⟨{Tier.m, Tier.clet, Tier.cloud}, fun x => by cases x <;> simp⟩

/-- The Euclidean inner product `aᵀb` on strategy profiles `ℝ^{3N}`, written out coordinatewise
(Mathlib's norm on Pi types is the sup norm, so no norm is used). -/
def pair {N : ℕ} (a b : Fin N → Tier → ℝ) : ℝ := ∑ u, ∑ i, a u i * b u i

/-- The data of the offloading game (10)–(15), p. 10, with users `u : Fin N`:
`alpha u = λ_u/µ_{u,m}`, `beta u = λ_u/µ_{u,wl}`, `delta u = λ_u/µ_{u,clet}`,
`gamma u = λ_u (1/µ_{u,wl} + 1/µ_{u,wn} + 1/µ_{u,cloud})`; `Pm u = P_{u,m}`, `Pt u = P_{u,t}`,
`Pmax u = P_{u,max}` (power constraint (12)); `n` the number of cloudlet servers (p. 7);
`chi` the offloadable fraction χ (13); `Umax` the cloudlet utilisation cap U_max (11). -/
structure Params (N : ℕ) where
  alpha : Fin N → ℝ
  beta : Fin N → ℝ
  gamma : Fin N → ℝ
  delta : Fin N → ℝ
  Pm : Fin N → ℝ
  Pt : Fin N → ℝ
  Pmax : Fin N → ℝ
  n : ℕ
  chi : ℝ
  Umax : ℝ

namespace Params

variable {N : ℕ}

/-- Assumption A (p. 11): `U_max` and all `α_u`, `δ_u` are positive and smaller than 1. -/
def AssumptionA (P : Params N) : Prop :=
  0 < P.Umax ∧ P.Umax < 1 ∧ ∀ u, 0 < P.alpha u ∧ P.alpha u < 1 ∧ 0 < P.delta u ∧ P.delta u < 1

/-- Standing hypotheses of the model: at least one cloudlet server (p. 7) and `0 < χ ≤ 1` (p. 9). -/
def Standing (P : Params N) : Prop :=
  0 < P.n ∧ 0 < P.chi ∧ P.chi ≤ 1

end Params

variable {N : ℕ}

/-- The cloudlet load `(1/n) ∑_v δ_v x_{v,clet}`, the left side of (11). -/
noncomputable def load (P : Params N) (x : Fin N → Tier → ℝ) : ℝ :=
  (1 / (P.n : ℝ)) * ∑ v, P.delta v * x v .clet

/-- `D = 1 - (1/n) ∑_v δ_v x_{v,clet}` (p. 12). -/
noncomputable def D (P : Params N) (x : Fin N → Tier → ℝ) : ℝ := 1 - load P x

/-- `K̃_u` (p. 11): the feasible set of user `u` with the joint constraint (11) neglected,
i.e. constraints (12)–(15). -/
def Ktil (P : Params N) (u : Fin N) : Set (Tier → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ y .m + y .clet + y .cloud = 1 ∧ y .clet + y .cloud ≤ P.chi ∧
    P.alpha u * P.Pm u * y .m + P.beta u * P.Pt u * (y .clet + y .cloud) ≤ P.Pmax u}

/-- `∏_u K̃_u`. -/
def Kprod (P : Params N) : Set (Fin N → Tier → ℝ) := {x | ∀ u, x u ∈ Ktil P u}

/-- `Ω = {x ∈ ℝ^{3N} : (1/n) ∑_u δ_u x_{u,clet} ≤ U_max}` (p. 11), the shared constraint (11). -/
def Omega (P : Params N) : Set (Fin N → Tier → ℝ) := {x | load P x ≤ P.Umax}

/-- `K = (∏_u K̃_u) ∩ Ω` (p. 11), the joint feasible set of the GNEP and the set of the VI. -/
def K (P : Params N) : Set (Fin N → Tier → ℝ) := Kprod P ∩ Omega P

/-- User `u`'s objective `λ_u R_u(x_u, x_{-u})` in the closed form of p. 10:
`α_u x_{u,m}/(1 - α_u x_{u,m}) + β_u x_{u,clet} + γ_u x_{u,cloud} + δ_u x_{u,clet}/(1 - (1/n)∑_v δ_v x_{v,clet})`.
The formula is meaningful where `1 - α_u x_{u,m} > 0` and `1 - load > 0`; under Assumption A both hold
at every profile whose `u`-th block lies in `K̃_u` and which lies in `Ω`. Elsewhere Lean's `x / 0 = 0`
gives a junk value, and no statement of this mission evaluates `cost` there. -/
noncomputable def cost (P : Params N) (u : Fin N) (x : Fin N → Tier → ℝ) : ℝ :=
  P.alpha u * x u .m / (1 - P.alpha u * x u .m) + P.beta u * x u .clet + P.gamma u * x u .cloud +
    P.delta u * x u .clet / (1 - load P x)

/-- The VI map `F` (p. 11), the stack of the partial gradients `∇_{x_u} λ_u R_u`, in the closed form
displayed on p. 11 (not defined as a derivative). Meaningful on `K` (see `cost`). -/
noncomputable def F (P : Params N) (x : Fin N → Tier → ℝ) : Fin N → Tier → ℝ :=
  fun u i =>
    match i with
    | .m => P.alpha u / (1 - P.alpha u * x u .m) ^ 2
    | .clet => P.beta u + P.delta u *
        (1 - (1 / (P.n : ℝ)) * ∑ v ∈ Finset.univ.erase u, P.delta v * x v .clet) /
          (1 - load P x) ^ 2
    | .cloud => P.gamma u

/-- Footnote 2 (p. 11): `xb` solves the variational inequality VI(S, G), i.e. `xb ∈ S` and
`G(xb)ᵀ(x - xb) ≥ 0` for all `x ∈ S`. -/
def IsVISol (S : Set (Fin N → Tier → ℝ)) (G : (Fin N → Tier → ℝ) → (Fin N → Tier → ℝ))
    (xb : Fin N → Tier → ℝ) : Prop :=
  xb ∈ S ∧ ∀ x ∈ S, 0 ≤ pair (G xb) (x - xb)

/-- A solution of the GNEP (10)–(15): `xb ∈ K`, and for every user `u`, `xb_u` minimises
`λ_u R_u(·, xb_{-u})` over user `u`'s feasible set given the others,
`{y ∈ K̃_u : (y, xb_{-u}) ∈ Ω}` (the standard notion of [16, 18]). Only costs at points of `Ω` with
`u`-th block in `K̃_u` are compared, where the formula of `cost` is meaningful under Assumption A. -/
def IsGNEPSol (P : Params N) (xb : Fin N → Tier → ℝ) : Prop :=
  xb ∈ K P ∧ ∀ u, ∀ y ∈ Ktil P u, Function.update xb u y ∈ Omega P →
    cost P u xb ≤ cost P u (Function.update xb u y)

end OffloadGNEP.Exist


