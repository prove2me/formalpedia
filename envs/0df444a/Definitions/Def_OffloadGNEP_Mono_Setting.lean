-- Prove2me | Definitions.Def_OffloadGNEP_Mono_Setting
-- name    : OffloadGNEP_Mono_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:00.133316+00:00
-- url     : https://prove2.me/theorems/abe8c3e6-5b45-4059-bc5d-c2b822a71a20
-- title:
--   (10)–(17), Assumption A, K̃_u, Ω, K, F, JF and Bˢ, pp. 10–13 — the offloading GNEP, its VI map and its Jacobian
-- statement:
--   This file fixes the objects of §5.1 of Cardellini et al. (the computation-offloading game) and the matrices used in the proof of its Theorem 1.
--
--   **Users and strategies.** There are $N$ users $u$. Each user splits its task stream over three tiers $I=\{m,\mathit{clet},\mathit{cloud}\}$ (mobile device, cloudlet, distant cloud) and chooses the fractions $x_u=(x_{u,m},x_{u,clet},x_{u,cloud})$. A strategy profile is $x=(x_u)_u\in\mathbb R^{3N}$, and $a^\top b=\sum_u\sum_{i\in I}a_{u,i}b_{u,i}$ is the Euclidean inner product on $\mathbb R^{3N}$.
--
--   **Parameters.** For each user, $\alpha_u=\lambda_u/\mu_{u,m}$, $\beta_u=\lambda_u/\mu_{u,wl}$, $\delta_u=\lambda_u/\mu_{u,clet}$, $\gamma_u=\lambda_u(1/\mu_{u,wl}+1/\mu_{u,wn}+1/\mu_{u,cloud})$, and the powers $P_{u,m},P_{u,t},P_{u,\max}$; further $n$ is the number of cloudlet servers, $\chi$ the offloadable fraction and $U_{\max}$ the cloudlet utilisation cap.
--
--   1. **Assumption A** (p. 11): $U_{\max}$ and all $\alpha_u$, $\delta_u$ lie in $(0,1)$.
--   2. **Standing hypotheses**: $n\ge1$ (p. 7) and $0<\chi\le1$ (p. 9).
--
--   **Feasible sets.** The cloudlet load is $\frac1n\sum_v\delta_vx_{v,clet}$ and $D(x)=1-\frac1n\sum_t\delta_tx_{t,clet}$. User $u$'s private feasible set is
--   $$\tilde K_u=\Big\{x_u\in\mathbb R^3_+:\ \textstyle\sum_{i\in I}x_{u,i}=1,\ x_{u,clet}+x_{u,cloud}\le\chi,\ \alpha_uP_{u,m}x_{u,m}+\beta_uP_{u,t}(x_{u,clet}+x_{u,cloud})\le P_{u,\max}\Big\},$$
--   the shared constraint is $\Omega=\{x:\frac1n\sum_u\delta_ux_{u,clet}\le U_{\max}\}$, and $K=(\prod_u\tilde K_u)\cap\Omega$.
--
--   **Cost and VI map.** User $u$ minimises $\lambda_uR_u(x)=\frac{\alpha_ux_{u,m}}{1-\alpha_ux_{u,m}}+\beta_ux_{u,clet}+\gamma_ux_{u,cloud}+\frac{\delta_ux_{u,clet}}{D(x)}$, and $F$ stacks the partial gradients in each user's own variables:
--   $$F(x)_u=\Big(\frac{\alpha_u}{(1-\alpha_ux_{u,m})^2},\ \beta_u+\delta_u\frac{1-\frac1n\sum_{v\ne u}\delta_vx_{v,clet}}{D(x)^2},\ \gamma_u\Big).$$
--   A map $G$ is **monotone** on a set $S$ if $(G(y)-G(x))^\top(y-x)\ge0$ for all $x,y\in S$ (footnote 3).
--
--   **Jacobian.** With $A_u=\frac{2\alpha_u^2}{(1-\alpha_ux_{u,m})^3}$, $B_u=\frac2n\delta_u^2\frac{1-\frac1n\sum_{v\ne u}\delta_vx_{v,clet}}{D^3}$ and $B_{uv}=\frac1n\delta_v\delta_u\frac{D+\frac2n\delta_ux_{u,clet}}{D^3}$ (17), the matrix $JF(x)$ of (16), indexed by pairs (user, tier), has $A_u$ at $((u,m),(u,m))$, $B_u$ at $((u,clet),(u,clet))$, $B_{uv}$ at $((u,clet),(v,clet))$ for $v\ne u$, and zeros elsewhere. $B$ is the $N\times N$ matrix with diagonal $B_u$ and off-diagonal entries $B_{uv}$, and $B^s=\frac12(B^\top+B)$ is its symmetric part. Finally $\delta_{\max}=\max_u\delta_u$, $x^\delta_{clet}=(\delta_1x_{1,clet},\dots,\delta_Nx_{N,clet})^\top$, $e$ is the all-ones vector, $E$ the all-ones matrix, and $\|v\|=(\sum_uv_u^2)^{1/2}$ is the Euclidean norm on $\mathbb R^N$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Users are `Fin N` (0-based). $F$ is defined by its closed form, not as a derivative. The formulas for the cost, $F$, $A_u$, $B_u$, $B_{uv}$ contain the denominators $1-\alpha_ux_{u,m}$ and $D$; they are meaningful where these are nonzero (on $K$ under Assumption A both are positive), and Lean's convention $a/0=0$ gives junk values elsewhere, where no statement of the mission evaluates them. $\delta_{\max}$ is a real supremum over the users, equal to the maximum for $N\ge1$ and to $0$ for $N=0$. The norm is written out because Mathlib's norm on `Fin N → ℝ` is the sup norm.
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), pp. 7, 9–13: (10)–(15), Assumption A, the definitions of K̃_u, Ω, K and F (p. 11), footnote 3, (16)–(17), δ_max (Theorem 1), B and Bˢ (proof of Theorem 1, p. 12), x^δ_clet, e, E (p. 13)

import Mathlib

namespace OffloadGNEP.Mono

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


/-- Footnote 3 (p. 12): `G` is monotone on `S` if `(G(y) - G(x))ᵀ(y - x) ≥ 0` for all `x, y ∈ S`;
the pairing is the Euclidean inner product `pair` over all `3N` coordinates. -/
def IsMonotoneOn (S : Set (Fin N → Tier → ℝ)) (G : (Fin N → Tier → ℝ) → (Fin N → Tier → ℝ)) :
    Prop :=
  ∀ x ∈ S, ∀ y ∈ S, 0 ≤ pair (G y - G x) (y - x)

/-- `δ_max = max_{u=1,…,N} δ_u` (Theorem 1, p. 12), as the supremum of the finitely many `δ_u`.
For `N ≥ 1` this is the maximum; for `N = 0` Lean's real supremum of the empty family is `0`. -/
noncomputable def deltaMax (P : Params N) : ℝ := ⨆ u, P.delta u

/-- The Euclidean norm `‖v‖ = (∑_u v_u²)^{1/2}` on `ℝ^N`, used in (21)–(23). (Mathlib's `‖v‖`
on `Fin N → ℝ` is the sup norm, which is not the paper's norm.) -/
noncomputable def eucNorm (v : Fin N → ℝ) : ℝ := Real.sqrt (∑ u, v u ^ 2)

/-- `A_u = 2α_u² / (1 - α_u x_{u,m})³`, (17), p. 12: the derivative of `F_{u,m}` in `x_{u,m}`.
Meaningful where `1 - α_u x_{u,m} ≠ 0`, in particular on `K` under Assumption A. -/
noncomputable def Au (P : Params N) (x : Fin N → Tier → ℝ) (u : Fin N) : ℝ :=
  2 * P.alpha u ^ 2 / (1 - P.alpha u * x u .m) ^ 3

/-- `B_u = (2/n) δ_u² (1 - (1/n) ∑_{v≠u} δ_v x_{v,clet}) / (1 - (1/n) ∑_t δ_t x_{t,clet})³`,
(17), p. 12. Meaningful where `D ≠ 0`, in particular on `K` under Assumption A. -/
noncomputable def Bu (P : Params N) (x : Fin N → Tier → ℝ) (u : Fin N) : ℝ :=
  2 / (P.n : ℝ) * P.delta u ^ 2 *
    (1 - 1 / (P.n : ℝ) * ∑ v ∈ Finset.univ.erase u, P.delta v * x v .clet) / (1 - load P x) ^ 3

/-- `B_uv = (1/n) δ_v δ_u (1 - (1/n) ∑_t δ_t x_{t,clet} + (2/n) δ_u x_{u,clet}) /
(1 - (1/n) ∑_t δ_t x_{t,clet})³`, (17), p. 12 (used for `v ≠ u`; note the row index `u` in
`δ_u x_{u,clet}`, so `B_uv ≠ B_vu` in general). Meaningful where `D ≠ 0`. -/
noncomputable def Buv (P : Params N) (x : Fin N → Tier → ℝ) (u v : Fin N) : ℝ :=
  1 / (P.n : ℝ) * P.delta v * P.delta u *
    (1 - load P x + 2 / (P.n : ℝ) * P.delta u * x u .clet) / (1 - load P x) ^ 3

/-- The Jacobian `JF(x)` of (16), p. 12, indexed by pairs (user, tier): row `(u, m)` has `A_u` in
column `(u, m)`; row `(u, clet)` has `B_u` in column `(u, clet)` and `B_uv` in column `(v, clet)`,
`v ≠ u`; every other entry (in particular the whole row `(u, cloud)`) is `0`. -/
noncomputable def JF (P : Params N) (x : Fin N → Tier → ℝ) :
    Matrix (Fin N × Tier) (Fin N × Tier) ℝ :=
  Matrix.of fun p q =>
    match p.2, q.2 with
    | .m, .m => if p.1 = q.1 then Au P x p.1 else 0
    | .clet, .clet => if p.1 = q.1 then Bu P x p.1 else Buv P x p.1 q.1
    | _, _ => 0

/-- The `N × N` block `B` of `JF(x)` after reordering the variables (proof of Theorem 1, p. 12):
diagonal `B_u`, off-diagonal `B_uv`. -/
noncomputable def Bmat (P : Params N) (x : Fin N → Tier → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun u v => if u = v then Bu P x u else Buv P x u v

/-- The symmetric part `Bˢ = ½(Bᵀ + B)` (proof of Theorem 1, p. 12). -/
noncomputable def Bs (P : Params N) (x : Fin N → Tier → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  (1 / 2 : ℝ) • ((Bmat P x).transpose + Bmat P x)

/-- `x^δ_clet = (δ_1 x_{1,clet}, …, δ_N x_{N,clet})ᵀ` (p. 13). -/
def xdelta (P : Params N) (x : Fin N → Tier → ℝ) : Fin N → ℝ := fun u => P.delta u * x u .clet

/-- `e ∈ ℝ^N`, the vector of all ones (p. 13). -/
def ones : Fin N → ℝ := fun _ => 1

/-- `E`, the `N × N` matrix with all entries equal to `1` (p. 13). -/
def Eall : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun _ _ => 1

end OffloadGNEP.Mono


