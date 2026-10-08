-- Prove2me | Definitions.Def_RealTimeIter_Contract_Iteration
-- name    : RealTimeIter_Contract_Iteration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:32:31.597859+00:00
-- url     : https://prove2.me/theorems/484f6d01-9ffe-4f95-b7bf-2a88c4d47a7c
-- title:
--   §3.1, §4, §5, pp. 1719–1724 — the real-time iteration, the domains $D_k$, compatible norms, $\delta_k$, the ball $B_0$, the Newton-type scheme (2.4), $F_{\rm real}$, $F_{\rm opt}$
-- statement:
--   This file builds on the problems $P_k(x_k)$, the Lagrangians $\mathcal L^k$, the matrices $J^k$ and the projections $\Pi^{k+1}$.
--
--   1. **Newton-type step.** For $y\in\mathbb R^{n_k}$ and initial value $x$, $\Delta y=-J^k(y)^{-1}\nabla_y\mathcal L^k(y)$ (the step of (2.4) for $P_k(x)$).
--   2. **Real-time iteration** (§3.1). Starting from the system state $x_0$ and a guess $y^0\in\mathbb R^{n_0}$: given $(x_k,y^k)$, take the step $\Delta y^k=-J^k(y^k)^{-1}\nabla_y\mathcal L^k(y^k)$ in $P_k(x_k)$, apply $u_k:=q^k_k+\Delta q^k_k$, let the system move undisturbed, $x_{k+1}=f_k(x_k,u_k)$, and shrink: $y^{k+1}:=\Pi^{k+1}(y^k+\Delta y^k)$.
--   3. **Domains.** Given $D_0\subset\mathbb R^{n_0}$, $D_{k+1}:=\Pi^{k+1}D_k$.
--   4. **Compatible norms** (§4). A family of norms $\|\cdot\|_k$ on $\mathbb R^{n_k}$ (definite, absolutely homogeneous, subadditive) with $\|\Pi^{k+1}y\|_{k+1}\le\|y\|_k$ and $\|(\Pi^{k+1})^T\tilde y\|_k=\|\tilde y\|_{k+1}$.
--   5. **Contraction rates.** $\delta_k:=\kappa+\frac{\omega}{2}\|\Delta y^k\|_k$, and the ball (4.1e) $$B_0:=\Big\{y\in\mathbb R^{n_0}\ \Big|\ \|y-y^0\|_0\le\frac{\|\Delta y^0\|_0}{1-\delta_0}\Big\}.$$
--   6. **Newton-type scheme** (2.2), (2.4) for $P_k(x)$ from $z$: $y_0=z$, $y_{i+1}=y_i-J^k(y_i)^{-1}\nabla_y\mathcal L^k(y_i)$ (the "hypothetical algorithm" of the proof of Theorem 4.1).
--   7. **Objective values** (§5). $F_{\rm real}=\sum_{i=0}^{N-1}L_i(x_i,u_i)+E(x_N)$ along the real-time closed loop, and, for $y^*\in\mathbb R^{n_0}$, $F_{\rm opt}=\sum_{i=0}^{N-1}L_i(s^*_i,q^*_i)+E(s^*_N)$; $y_{\rm real}:=y^0+\Delta y^0+(\Pi^1)^T\Delta y^1+\dots+(\Pi^N\cdots\Pi^1)^T\Delta y^N$.
--   8. **The hypotheses of Theorem 4.1** (`Thm41Hyp`), for $k=0,\dots,N$: $y^0\in D_0$; $\mathcal L^k$ twice continuously differentiable at every point of $D_k$; $J^k$ continuous on $D_k$, invertible at every point of $D_k$, with $\sup_{y\in D_k}\|J^k(y)^{-1}\|<\infty$; $\kappa<1$; for all $y',y\in D_k$, $\Delta y=y'-y$, $t\in[0,1]$ with $y+t\Delta y\in D_k$,
--   $$\big\|J^k(y')^{-1}\big(J^k(y+t\Delta y)-\nabla^2_y\mathcal L^k(y+t\Delta y)\big)\Delta y\big\|_k\le\kappa\|\Delta y\|_k,\tag{4.1a}$$
--   $$\big\|J^k(y')^{-1}\big(J^k(y+t\Delta y)-J^k(y)\big)\Delta y\big\|_k\le\omega t\|\Delta y\|_k^2,\tag{4.1b}$$
--   and, for $k\le N-1$, $$\big\|J^{k+1}(\Pi^{k+1}y')^{-1}\Pi^{k+1}\big(J^k(y+t\Delta y)-J^k(y)\big)\Delta y\big\|_{k+1}\le\omega t\|\Delta y\|_k^2;\tag{4.1c}$$ finally $\delta_0<1$ (4.1d) and $B_0\subseteq D_0$ (4.1e).
--
--   **Formalization Note.** `rti P x0 y0 k` is the pair $(x_k,y^k)$; it is defined for every $k$, and only $k\le N$ is used. The inverse is Mathlib's `ContinuousLinearMap.inverse`, which is $0$ at a non-invertible operator; invertibility on $D_k$ is a hypothesis. The norm axioms are fields of `CompatNorms` so that (4.1a)–(4.1c) cannot be met by a degenerate "norm"; the topology is the Euclidean one (all norms on $\mathbb R^{n_k}$ are equivalent). The paper's $J^k$ and $\mathcal L^k$ are defined on $D_k$ only and $D_k$ need not be convex, so (4.1a)–(4.1c) are required only for $t$ with $y+t\Delta y\in D_k$. In (4.1d) the paper writes $\Delta y^0:=J^0(y^0)^{-1}\nabla\mathcal L^0(y^0)$ without the minus sign; only its norm enters. The paper's $F_{\rm real}, F_{\rm opt}$ print $\sum_{i=k}^{N-1}$; both are objectives of $P_0(x_0)$, so the sum starts at $0$.
-- source:
--   Diehl, Bock, Schlöder, A real-time iteration scheme for nonlinear optimization in optimal feedback control, SIAM J. Control Optim. 43 (2005), pp. 1717–1724, (2.2), (2.4), §3.1, §4 (D_k, norms), Theorem 4.1 hypotheses (4.1a)–(4.1e), proof of Theorem 4.1 p. 1723, Theorem 5.1 (F_real, F_opt), proof p. 1724 (y_real)

import Mathlib
import Definitions.Def_RealTimeIter_Contract_Problem

noncomputable section

namespace RealTimeIter.Contract

/-- The Newton-type step `Δy = −J^k(y)^{-1} ∇_y ℒ^k(y)` of (2.4) for problem `P_k(x)`
(`ContinuousLinearMap.inverse` is `0` where `J^k(y)` is not invertible). -/
def step (P : OCP) (k : ℕ) (x : Vec P.nx) (y : PD P k) : PD P k :=
  -((J P k y).inverse (grad P k x y))

/-- The real-time iteration of §3.1 along the undisturbed closed loop: `rti P x0 y0 k = (x_k, y^k)`,
with `(x_0, y^0) = (x0, y0)`, `Δy^k = −J^k(y^k)^{-1}∇_y ℒ^k(y^k)` (for `P_k(x_k)`),
`u_k = q^k_k + Δq^k_k`, `x_{k+1} = f_k(x_k, u_k)` and `y^{k+1} = Π^{k+1}(y^k + Δy^k)`. -/
def rti (P : OCP) (x0 : Vec P.nx) (y0 : PD P 0) : (k : ℕ) → Vec P.nx × PD P k
  | 0 => (x0, y0)
  | k + 1 =>
      let xy := rti P x0 y0 k
      let yn := xy.2 + step P k xy.1 xy.2
      (P.f k xy.1 (qL P k k yn), proj P k yn)

/-- The real-time step `Δy^k = −J^k(y^k)^{-1}∇_y ℒ^k(y^k)` taken in problem `P_k(x_k)`. -/
def rtiStep (P : OCP) (x0 : Vec P.nx) (y0 : PD P 0) (k : ℕ) : PD P k :=
  step P k (rti P x0 y0 k).1 (rti P x0 y0 k).2

/-- The feedback control `u_k = q^k_k + Δq^k_k` given to the system. -/
def ctrl (P : OCP) (x0 : Vec P.nx) (y0 : PD P 0) (k : ℕ) : Vec P.nu :=
  qL P k k ((rti P x0 y0 k).2 + rtiStep P x0 y0 k)

/-- The domains `D_0 ⊂ ℝ^{n_0}` and `D_{k+1} := Π^{k+1} D_k`. -/
def Dset (P : OCP) (D0 : Set (PD P 0)) : (k : ℕ) → Set (PD P k)
  | 0 => D0
  | k + 1 => proj P k '' Dset P D0 k

/-- A family of norms `‖·‖_k` on the spaces `ℝ^{n_k}`, compatible with the projections (§4, p. 1720):
`‖Π^{k+1} y‖_{k+1} ≤ ‖y‖_k` and `‖(Π^{k+1})ᵀ ỹ‖_k = ‖ỹ‖_{k+1}`. -/
structure CompatNorms (P : OCP) where
  nrm : (k : ℕ) → PD P k → ℝ
  eq_zero : ∀ k (y : PD P k), nrm k y = 0 → y = 0
  smul : ∀ k (c : ℝ) (y : PD P k), nrm k (c • y) = |c| * nrm k y
  triangle : ∀ k (y z : PD P k), nrm k (y + z) ≤ nrm k y + nrm k z
  proj_le : ∀ k (y : PD P k), nrm (k + 1) (proj P k y) ≤ nrm k y
  projT_eq : ∀ k (z : PD P (k + 1)), nrm k (projT P k z) = nrm (k + 1) z

/-- `δ_k := κ + (ω/2)‖Δy^k‖_k`, for the real-time steps. -/
def delta (P : OCP) (ν : CompatNorms P) (x0 : Vec P.nx) (y0 : PD P 0) (κ ω : ℝ) (k : ℕ) : ℝ :=
  κ + ω / 2 * ν.nrm k (rtiStep P x0 y0 k)

/-- The ball `B_0 := {y ∈ ℝ^{n_0} | ‖y − y^0‖_0 ≤ ‖Δy^0‖_0 / (1 − δ_0)}` of (4.1e). -/
def ball0 (P : OCP) (ν : CompatNorms P) (x0 : Vec P.nx) (y0 : PD P 0) (κ ω : ℝ) : Set (PD P 0) :=
  {y | ν.nrm 0 (y - y0) ≤ ν.nrm 0 (rtiStep P x0 y0 0) / (1 - delta P ν x0 y0 κ ω 0)}

/-- The Newton-type scheme (2.2)/(2.4) for `P_k(x)` started at `z`: `y_0 = z`,
`y_{i+1} = y_i − J^k(y_i)^{-1}∇_y ℒ^k(y_i)` (the "hypothetical algorithm" of p. 1723). -/
def newtonIter (P : OCP) (k : ℕ) (x : Vec P.nx) (z : PD P k) : ℕ → PD P k
  | 0 => z
  | i + 1 => newtonIter P k x z i + step P k x (newtonIter P k x z i)

/-- `F_real = Σ_{i=0}^{N-1} L_i(x_i, u_i) + E(x_N)`, the objective along the real-time closed loop. -/
def Freal (P : OCP) (x0 : Vec P.nx) (y0 : PD P 0) : ℝ :=
  (∑ i ∈ Finset.range P.N, P.L i (rti P x0 y0 i).1 (ctrl P x0 y0 i)) + P.Eterm (rti P x0 y0 P.N).1

/-- `F_opt = Σ_{i=0}^{N-1} L_i(s*_i, q*_i) + E(s*_N)`, the objective at the primal part of `y* ∈ ℝ^{n_0}`. -/
def Fopt (P : OCP) (ystar : PD P 0) : ℝ :=
  (∑ i ∈ Finset.range P.N, P.L i (sL P 0 i ystar) (qL P 0 i ystar)) + P.Eterm (sL P 0 P.N ystar)

/-- `y_real := y^0 + Δy^0 + (Π^1)ᵀΔy^1 + ⋯ + (Π^N⋯Π^1)ᵀΔy^N` (proof of Theorem 5.1, p. 1724). -/
def yReal (P : OCP) (x0 : Vec P.nx) (y0 : PD P 0) : PD P 0 :=
  y0 + ∑ k ∈ Finset.range (P.N + 1), liftFrom P k (rtiStep P x0 y0 k)

/-- The hypotheses of Theorem 4.1 (pp. 1720–1721), for the system started at `x0` and the real-time
iteration started at `y0 ∈ D0`. -/
structure Thm41Hyp (P : OCP) (ν : CompatNorms P) (x0 : Vec P.nx) (y0 : PD P 0)
    (D0 : Set (PD P 0)) (κ ω : ℝ) : Prop where
  /-- `y^0 ∈ D_0`. -/
  mem : y0 ∈ D0
  /-- `ℒ^k` is twice continuously differentiable on `D_k`, `k = 0, …, N`. -/
  c2 : ∀ k ≤ P.N, ∀ y ∈ Dset P D0 k, ContDiffAt ℝ 2 (lagr P k 0) y
  /-- `J^k` is continuous on `D_k`. -/
  J_cont : ∀ k ≤ P.N, ContinuousOn (J P k) (Dset P D0 k)
  /-- `J^k(y)` is invertible for `y ∈ D_k`. -/
  J_inv : ∀ k ≤ P.N, ∀ y ∈ Dset P D0 k, (J P k y).IsInvertible
  /-- `(J^k)^{-1}` is bounded on `D_k`. -/
  J_inv_bdd : ∀ k ≤ P.N, ∃ β : ℝ, ∀ y ∈ Dset P D0 k, ‖(J P k y).inverse‖ ≤ β
  /-- `κ < 1`. -/
  kappa_lt : κ < 1
  /-- (4.1a). -/
  h41a : ∀ k ≤ P.N, ∀ y' ∈ Dset P D0 k, ∀ y ∈ Dset P D0 k, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    y + t • (y' - y) ∈ Dset P D0 k →
    ν.nrm k ((J P k y').inverse
        ((J P k (y + t • (y' - y)) - hess P k (y + t • (y' - y))) (y' - y)))
      ≤ κ * ν.nrm k (y' - y)
  /-- (4.1b). -/
  h41b : ∀ k ≤ P.N, ∀ y' ∈ Dset P D0 k, ∀ y ∈ Dset P D0 k, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    y + t • (y' - y) ∈ Dset P D0 k →
    ν.nrm k ((J P k y').inverse ((J P k (y + t • (y' - y)) - J P k y) (y' - y)))
      ≤ ω * t * ν.nrm k (y' - y) ^ 2
  /-- (4.1c), `k = 0, …, N − 1`. -/
  h41c : ∀ k < P.N, ∀ y' ∈ Dset P D0 k, ∀ y ∈ Dset P D0 k, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    y + t • (y' - y) ∈ Dset P D0 k →
    ν.nrm (k + 1) ((J P (k + 1) (proj P k y')).inverse
        (proj P k ((J P k (y + t • (y' - y)) - J P k y) (y' - y))))
      ≤ ω * t * ν.nrm k (y' - y) ^ 2
  /-- (4.1d): `δ_0 = κ + (ω/2)‖Δy^0‖_0 < 1`. -/
  h41d : delta P ν x0 y0 κ ω 0 < 1
  /-- (4.1e): `B_0 ⊆ D_0`. -/
  h41e : ball0 P ν x0 y0 κ ω ⊆ D0

end RealTimeIter.Contract

end


