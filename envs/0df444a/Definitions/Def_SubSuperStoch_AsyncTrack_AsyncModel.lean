-- Prove2me | Definitions.Def_SubSuperStoch_AsyncTrack_AsyncModel
-- name    : SubSuperStoch_AsyncTrack_AsyncModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:42:30.067924+00:00
-- url     : https://prove2.me/theorems/2be04ac8-1656-455d-a6bd-4623f88913dc
-- title:
--   §2.5 and §3, pp. 13–15 — asynchronous instants (2.10), protocol (3.3), system (3.1)–(3.2), M(k), errors (3.5), bipartite tracking (Definition 3.1)
-- statement:
--   This file encodes the asynchronous first-order leader–follower system of §2.5 and §3. The weights $a_{ij}$ and $a_{i0}$ are those of the signed digraph of §2.3. Positions lie in $\mathbb R^p$, and time is discrete with step size $\tau>0$: the time instants are $k\tau$, $k\in\mathbb N$.
--
--   1. **Asynchronous instants (§2.5, (2.10)).** Follower $v_i$ communicates with its neighbours only at its own instants $s^i_0\tau<s^i_1\tau<\dots$, where $s^i_k\in\mathbb N$, $s^i_0=0$ and, for a constant $h\in\mathbb Z_+$,
--   $$s^i_{k+1}-s^i_k\le h\qquad(k\in\mathbb N,\ i=1,\dots,n).$$
--   2. **Dynamics (3.1)–(3.3).** The leader is static, $x_0(k+1)=x_0(k)$, and each follower moves by $x_i(k+1)=x_i(k)+\tau u_i(k)$ with the protocol
--   $$u_i(k)=\psi\sum_{v_j\in\mathcal N_i}|a_{ij}|\big[\operatorname{sgn}(a_{ij})x_j(k)-x_i(k)\big]+\psi|a_{i0}|\big[\operatorname{sgn}(a_{i0})x_0(k)-x_i(k)\big]$$
--   if $k\tau$ is one of the instants of $v_i$, and $u_i(k)=0$ otherwise. Here $\psi>0$ is the gain, $\mathcal N_i=\{v_j: a_{ij}\neq 0\}$ and $\operatorname{sgn}$ is the signum function ($1$, $0$, $-1$).
--   3. **The matrices $M(k)$ (p. 15).** Let $a_{ij}(k)=a_{ij}$ and $a_{i0}(k)=a_{i0}$ if $k\tau$ is an instant of $v_i$, and $a_{ij}(k)=a_{i0}(k)=0$ otherwise. With $\mathcal D(k)=\operatorname{diag}\{\sum_j|a_{ij}(k)|\}$, $\mathcal B(k)=\operatorname{diag}\{|a_{i0}(k)|\}$ and $|\mathcal A(k)|=[|a_{ij}(k)|]$,
--   $$M(k)=I_n-\tau\psi\mathcal D(k)-\tau\psi\mathcal B(k)+\tau\psi|\mathcal A(k)|.$$
--   4. **Error coordinates (3.5).** For a set $V_1$ of followers (those in $\mathcal V_1$), $e_i(k)=x_i(k)-x_0(k)$ if $v_i\in V_1$ and $e_i(k)=-x_i(k)-x_0(k)$ otherwise.
--   5. **Bipartite tracking (Definition 3.1).** Bipartite tracking is realized if
--   $$\lim_{k\to\infty}\|x_i(k)-x_0(k)\|=0\ \ (v_i\in\mathcal V_1),\qquad \lim_{k\to\infty}\|x_i(k)+x_0(k)\|=0\ \ (v_i\in\mathcal V_2).$$
--
--   Between its communication instants a follower's position is frozen. The matrices $M(k)$ are the transition matrices of the error system (3.6), and the paper reduces bipartite tracking to the convergence of their products.
--
--   **Formalization Note** Followers are `Fin n` (0-based), positions are in `EuclideanSpace ℝ (Fin p)`, and `s i k` is $s^i_k$, so the protocol is active at step $k$ iff `k ∈ Set.range (s i)` (`active s i k`). The sum in `protocol` runs over all followers; the terms with $a_{ij}=0$ vanish, so it equals the printed sum over $\mathcal N_i$. $\operatorname{sgn}$ is `Real.sign`. `IsRun` leaves the initial states free. In `BipartiteTracking V₁ x0 x`, $\mathcal V_1$ is the leader together with the followers in `V₁` and $\mathcal V_2$ is the other followers. The norm is the Euclidean norm; the paper leaves it unspecified, and all norms on $\mathbb R^p$ give the same limits.
-- source:
--   Shi, Zheng, Shao, Cheng, arXiv:2004.01867v2, p. 13, §2.5 Asynchronous setting and (2.10); p. 14, (3.1)–(3.3) and Definition 3.1; pp. 14–15, 𝒜(k), a_i0(k), 𝒟(k), ℬ(k), (3.5) and M(k) below (3.6)

import Mathlib

namespace SubSuperStoch.AsyncTrack

open Filter Topology

/-!
The asynchronous first-order leader–follower system of §2.5 and §3 (pp. 13–15).
Followers are `Fin n` (0-based), the leader is not an index; `a i j = a_ij`, `b i = a_i0` as in
`Def_SubSuperStoch_AsyncTrack_SignedDigraph`. Positions live in `EuclideanSpace ℝ (Fin p)` (`ℝ^p`).
-/

/-- The asynchronous communication instants of §2.5 (p. 13): follower `i` communicates at the
time instants `s i k * τ`, `k ∈ ℕ`, with `s i 0 = 0`, strictly increasing, and
(2.10) `s^i_{k+1} − s^i_k ≤ h` for a constant `h ∈ ℤ₊` (`h ≥ 1`). -/
def IsAsyncInstants {n : ℕ} (s : Fin n → ℕ → ℕ) (h : ℕ) : Prop :=
  1 ≤ h ∧ ∀ i, s i 0 = 0 ∧ StrictMono (s i) ∧ ∀ k, s i (k + 1) ≤ s i k + h

/-- Follower `i` communicates at the time instant `kτ`, i.e. `kτ ∈ {s^i_k τ}`. -/
def active {n : ℕ} (s : Fin n → ℕ → ℕ) (i : Fin n) (k : ℕ) : Prop :=
  k ∈ Set.range (s i)

open Classical in
/-- The asynchronous distributed protocol (3.3) (p. 14): at a communication instant of follower `i`,
`u_i(k) = ψ ∑_{v_j ∈ 𝒩_i} |a_ij| (sgn(a_ij) x_j(k) − x_i(k)) + ψ |a_i0| (sgn(a_i0) x_0(k) − x_i(k))`,
and `u_i(k) = 0` otherwise. `sgn` is `Real.sign` (`1`, `0`, `−1`). The sum runs over all followers
`j`; the terms with `a_ij = 0` (non-neighbours) vanish, so it equals the printed sum over `𝒩_i`. -/
noncomputable def protocol {n p : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (ψ : ℝ)
    (s : Fin n → ℕ → ℕ) (x0 : ℕ → EuclideanSpace ℝ (Fin p))
    (x : Fin n → ℕ → EuclideanSpace ℝ (Fin p)) (i : Fin n) (k : ℕ) : EuclideanSpace ℝ (Fin p) :=
  if active s i k then
    ψ • (∑ j, |a i j| • (Real.sign (a i j) • x j k - x i k)) +
      ψ • (|b i| • (Real.sign (b i) • x0 k - x i k))
  else 0

/-- `(x0, x)` is a trajectory of the closed loop (3.1)–(3.3) (p. 14): the leader is static,
`x_0(k+1) = x_0(k)`, and every follower obeys `x_i(k+1) = x_i(k) + τ u_i(k)` with `u_i` the
protocol (3.3). Initial states are arbitrary. -/
def IsRun {n p : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (τ ψ : ℝ)
    (s : Fin n → ℕ → ℕ) (x0 : ℕ → EuclideanSpace ℝ (Fin p))
    (x : Fin n → ℕ → EuclideanSpace ℝ (Fin p)) : Prop :=
  (∀ k, x0 (k + 1) = x0 k) ∧ ∀ i k, x i (k + 1) = x i k + τ • protocol a b ψ s x0 x i k

open Classical in
/-- The matrix `M(k) = I_n − τψ𝒟(k) − τψℬ(k) + τψ|𝒜(k)|` of the error system (3.6) (p. 15), where
`a_ij(k) = a_ij` and `a_i0(k) = a_i0` if follower `i` communicates at `kτ` and both are `0`
otherwise, `𝒟(k) = diag{∑_j |a_ij(k)|}`, `ℬ(k) = diag{|a_i0(k)|}` and `|𝒜(k)| = [|a_ij(k)|]`. -/
noncomputable def Mmat {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (τ ψ : ℝ)
    (s : Fin n → ℕ → ℕ) (k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  let A : Matrix (Fin n) (Fin n) ℝ := fun i j => if active s i k then a i j else 0
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i => ∑ j, |A i j|)
  let B : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i => if active s i k then |b i| else 0)
  let Aabs : Matrix (Fin n) (Fin n) ℝ := fun i j => |A i j|
  1 - (τ * ψ) • D - (τ * ψ) • B + (τ * ψ) • Aabs

open Classical in
/-- The error coordinates (3.5) (p. 15): `e_i(k) = x_i(k) − x_0(k)` for `v_i ∈ 𝒱₁` (`i ∈ V₁`) and
`e_i(k) = −x_i(k) − x_0(k)` for `v_i ∈ 𝒱₂` (`i ∉ V₁`). -/
noncomputable def errVec {n p : ℕ} (V₁ : Set (Fin n)) (x0 : ℕ → EuclideanSpace ℝ (Fin p))
    (x : Fin n → ℕ → EuclideanSpace ℝ (Fin p)) (i : Fin n) (k : ℕ) : EuclideanSpace ℝ (Fin p) :=
  (if i ∈ V₁ then x i k else -x i k) - x0 k

/-- Definition 3.1 (p. 14): bipartite tracking is realized if `‖x_i(k) − x_0(k)‖ → 0` for every
`v_i ∈ 𝒱₁` and `‖x_i(k) + x_0(k)‖ → 0` for every `v_i ∈ 𝒱₂`, as `k → ∞`. Here `𝒱₁` is the leader
together with the followers in `V₁`, and `𝒱₂` is the remaining followers. -/
def BipartiteTracking {n p : ℕ} (V₁ : Set (Fin n)) (x0 : ℕ → EuclideanSpace ℝ (Fin p))
    (x : Fin n → ℕ → EuclideanSpace ℝ (Fin p)) : Prop :=
  (∀ i ∈ V₁, Tendsto (fun k => ‖x i k - x0 k‖) atTop (𝓝 0)) ∧
    ∀ i ∉ V₁, Tendsto (fun k => ‖x i k + x0 k‖) atTop (𝓝 0)

end SubSuperStoch.AsyncTrack


