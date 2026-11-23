-- Prove2me | Definitions.Def_OffloadGNEP_Mono_Supplement_Algorithms
-- name    : OffloadGNEP_Mono_Supplement_Algorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:17:38.726535+00:00
-- url     : https://prove2.me/theorems/fd46b519-ee50-442a-9e52-3f161b1fc463
-- title:
--   Algorithms 1–2 and (24), p. 17 — δ_max, ᾱ, the regularized map F_e + α(· − c), and the runs of the proximal-point and Jacobi schemes
-- statement:
--   The objects of §6 (p. 17) of Cardellini et al., built on the extended game of p. 15. A point of the extended game is a pair $(x,\rho)$ of a strategy profile $x=(x_u)_{u=1}^N$, $x_u=(x_{u,m},x_{u,clet},x_{u,cloud})$, and a cloudlet price $\rho$. The feasible set is $K_e=(\prod_u\tilde K_u)\times\mathbb R_+$ and $F_e$ is the VI map of the extended game. Fix a regularization parameter $\alpha$ and a prox centre $c=(x^k,\rho^k)$.
--
--   1. **Threshold (24).** $\delta_{\max}=\max_u\delta_u$ and
--   $$\bar\alpha=\frac{3N}{n}\,\frac{\delta_{\max}}{(1-U_{\max})^3}.$$
--   2. **Regularized map.** $F_e+\alpha(\cdot-c)$, that is, $(x,\rho)\mapsto F_e(x,\rho)+\alpha\big((x,\rho)-c\big)$.
--   3. **User objective of Step (S.2) of Algorithm 2.** At the current iterate $(x^i,\rho^i)$, user $u$ minimises over $y\in\tilde K_u$
--   $$\lambda_uR_u(y,x^i_{-u})+\rho^i\frac{\delta_u}{n}y_{clet}+\frac{\alpha}{2}\|y-x^k_u\|^2 ,$$
--   where $\|\cdot\|$ is the Euclidean norm on $\mathbb R^3$.
--   4. **Price update of Step (S.3).** $\rho^{i+1}=\max\{0,\ \rho^k+\tfrac1\alpha(\tfrac1n\sum_u\delta_u x^i_{u,clet}-U_{\max})\}$.
--   5. **Jacobi step.** $(x^{i+1},\rho^{i+1})$ follows $(x^i,\rho^i)$ when every $x^{i+1}_u$ is a minimiser of item 3 (all users respond to the same $x^i$ and $\rho^i$) and $\rho^{i+1}$ is given by item 4. A **run of Algorithm 2** is a sequence that starts in $K_e$ and follows Jacobi steps.
--   6. **Run of Algorithm 1.** A sequence $(x^k,\rho^k)_k$ that starts in $K_e$ and in which every $(x^{k+1},\rho^{k+1})$ solves $\mathrm{VI}(K_e,F_e+\alpha(\cdot-(x^k,\rho^k)))$.
--
--   These are the algorithms whose convergence Theorem 3 asserts.
--
--   **Formalization Note** The paper prints $\alpha\|x_u-x_u^k\|^2$ in (S.2) and $1/(2\alpha)$ in (S.3). With those constants the fixed points of the inner scheme solve the VI regularized by $2\alpha$, while Algorithm 1, Theorem 3 and the Jacobian (25) all use $\alpha$. The weights $\alpha/2$ and $1/\alpha$ are the ones whose optimality conditions are the blocks of $F_e+\alpha(\cdot-c)$. The printed scheme with parameter $\alpha$ is this scheme with parameter $2\alpha$. Users are indexed by `Fin N`, from 0. $\delta_{\max}$ is $0$ when $N=0$. The stopping tests (S.1) are not encoded: a solution is a fixed point of each update, so a stopped run corresponds to a run that stays constant.
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), p. 17, Algorithm 1, Algorithm 2 and (24); δ_max from Theorem 1, p. 12

import Mathlib
import Definitions.Def_OffloadGNEP_Ext_Setting

namespace OffloadGNEP.Mono.Supplement

open OffloadGNEP.Ext

noncomputable section

/-- `δ_max = max_u δ_u` (p. 12), on the parameters of the extended game. It is `0` when `N = 0`
(the supremum of the empty family of reals). -/
def deltaMax {N : ℕ} (P : Params N) : ℝ := ⨆ u, P.delta u

/-- The threshold `ᾱ = (3N/n) · δ_max/(1 − U_max)³` of (24), p. 17. -/
def alphaBar {N : ℕ} (P : Params N) : ℝ :=
  3 * (N : ℝ) / (P.n : ℝ) * (deltaMax P / (1 - P.Umax) ^ 3)

/-- The regularized VI map `F_e + α(· − c)` of Algorithms 1 and 2 (p. 17), with prox centre
`c = (x^k, ρ^k)`. -/
def regMap {N : ℕ} (P : Params N) (α : ℝ) (c : (Fin N → Exist.Tier → ℝ) × ℝ)
    (p : (Fin N → Exist.Tier → ℝ) × ℝ) : (Fin N → Exist.Tier → ℝ) × ℝ :=
  Fe P p + α • (p - c)

/-- User `u`'s objective in Step (S.2) of Algorithm 2 (p. 17), at the current iterate
`z = (x^i, ρ^i)` and prox centre `c = (x^k, ρ^k)`, as a function of the user's own strategy `y`:
`λ_u R_u(y, x^i_{−u}) + ρ^i (δ_u/n) y_clet + (α/2) ‖y − x^k_u‖²`, with the Euclidean norm on `ℝ³`
written out. The weight `α/2` repairs the printed `α` (see the mission notes): it is the weight
whose first-order condition is the `u`-block of `F_e + α(· − c)`. -/
def alg2Obj {N : ℕ} (P : Params N) (α : ℝ) (c z : (Fin N → Exist.Tier → ℝ) × ℝ) (u : Fin N)
    (y : Exist.Tier → ℝ) : ℝ :=
  cost P u (Function.update z.1 u y) + z.2 * (P.delta u / (P.n : ℝ) * y .clet) +
    α / 2 * ∑ i, (y i - c.1 u i) ^ 2

/-- The price update of Step (S.3) of Algorithm 2 (p. 17):
`ρ^{i+1} = max{0, ρ^k + (1/α)((1/n) ∑_u δ_u x^i_{u,clet} − U_max)}`. The step `1/α` repairs the
printed `1/(2α)` (see the mission notes). -/
def alg2Price {N : ℕ} (P : Params N) (α : ℝ) (c z : (Fin N → Exist.Tier → ℝ) × ℝ) : ℝ :=
  max 0 (c.2 + 1 / α * (load P z.1 - P.Umax))

/-- One Jacobi step `z = (x^i, ρ^i) ↦ z' = (x^{i+1}, ρ^{i+1})` of Algorithm 2 (p. 17) with prox
centre `c`: every user's new strategy minimises its (S.2) objective over `K̃_u`, all users
responding to the same `x^i` and `ρ^i`, and the new price is the (S.3) formula. -/
def IsAlg2Step {N : ℕ} (P : Params N) (α : ℝ) (c z z' : (Fin N → Exist.Tier → ℝ) × ℝ) : Prop :=
  (∀ u, z'.1 u ∈ Ktil P u ∧
      ∀ y ∈ Ktil P u, alg2Obj P α c z u (z'.1 u) ≤ alg2Obj P α c z u y) ∧
    z'.2 = alg2Price P α c z

/-- A run of Algorithm 2 with prox centre `c`: a start `(x⁰, ρ⁰) ∈ K_e` (S.0) followed by Jacobi
steps (S.2)–(S.3). -/
def IsAlg2Run {N : ℕ} (P : Params N) (α : ℝ) (c : (Fin N → Exist.Tier → ℝ) × ℝ)
    (s : ℕ → (Fin N → Exist.Tier → ℝ) × ℝ) : Prop :=
  s 0 ∈ Ke P ∧ ∀ i, IsAlg2Step P α c (s i) (s (i + 1))

/-- A run of Algorithm 1 (p. 17): a start `(x⁰, ρ⁰) ∈ K_e` (S.0), and each next iterate a solution
of `VI(K_e, F_e + α(· − (x^k, ρ^k)))` (S.2). -/
def IsAlg1Run {N : ℕ} (P : Params N) (α : ℝ) (t : ℕ → (Fin N → Exist.Tier → ℝ) × ℝ) : Prop :=
  t 0 ∈ Ke P ∧ ∀ k, IsVISolE (Ke P) (regMap P α (t k)) (t (k + 1))

end

end OffloadGNEP.Mono.Supplement


