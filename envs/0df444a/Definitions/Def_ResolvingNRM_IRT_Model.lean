-- Prove2me | Definitions.Def_ResolvingNRM_IRT_Model
-- name    : ResolvingNRM_IRT_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T02:07:40.694087+00:00
-- url     : https://prove2.me/theorems/29ff158c-8db3-4a46-bc83-10535be3d0a8
-- title:
--   Sec. 2 and Algorithms 1, 3 — the Poisson network revenue-management model, $v^{\mathrm{DLP}}$, $v^{\mathrm{HO}}$, probabilistic allocation windows, IRT$^{K'}$ and HO$^{K'}$
-- statement:
--   **The model** (Bumpensanti–Wang, Sec. 2, p. 7). There are $n$ customer classes $j \in [n]$ and $m$ resources $l \in [m]$. Class-$j$ customers arrive according to independent Poisson processes of rates $\lambda_j > 0$ over a horizon of length $T$. Accepting a class-$j$ customer earns $r_j \ge 0$ and consumes $a_{lj} \ge 0$ units of resource $l$; $A = (a_{lj}) \in \mathbb R^{m\times n}$ is the bill-of-materials matrix with columns $A_j$, and $C \in \mathbb R^m_{\ge 0}$ is the vector of initial capacities. A customer can only be accepted if $A_j \le C'$ componentwise, where $C'$ is the remaining capacity.
--
--   This file introduces the following objects, all relative to fixed data $(\lambda, r, A)$.
--
--   1. **Poisson mass function** $p_\mu(k) = e^{-\mu}\mu^k/k!$ for $\mu \ge 0$.
--   2. **Optimal-solution selector.** A map $\mathrm{sel}$ from right-hand sides $b \ge 0$ to an optimal solution of the per-unit-time DLP
--   $$\max_x \Big\{ \sum_{j} r_j x_j \ \Big|\ \sum_j A_j x_j \le b,\ 0 \le x_j \le \lambda_j\ \forall j \Big\},$$
--   i.e. $\mathrm{sel}(b)$ is feasible and no feasible point has a larger objective. It models the paper's "$x \leftarrow \arg\max$" with an arbitrary tie-breaking rule.
--   3. **DLP value** (2): $v^{\mathrm{DLP}}(T, C) = T \cdot \max\{ r^\top x : Ax \le C/T,\ 0 \le x \le \lambda\}$.
--   4. **Hindsight optimum** (3): with $\Lambda_j(T)$ independent Poisson$(\lambda_j T)$,
--   $$v^{\mathrm{HO}}(T, C) = \mathbb E\Big[\max_z \Big\{ \sum_j r_j z_j \ \Big|\ \sum_j A_j z_j \le C,\ 0 \le z_j \le \Lambda_j(T)\ \forall j\Big\}\Big],$$
--   the expectation of the value of the real hindsight LP.
--   5. **Probabilistic allocation over a window.** Over a window of length $\ell$, starting with capacity $c$ and acceptance probabilities $p_j \in [0,1]$, every class-$j$ arrival is accepted with probability $p_j$ provided $A_j \le C'$, in which case $r_j$ is earned and $C' \leftarrow C' - A_j$. The window value $\mathrm{win}(\ell, p, c, W)$ is the expected revenue collected in the window plus $W(C'_{\mathrm{end}})$, the continuation value $W$ of the capacity left at the end.
--   6. **Thresholded probabilities** (Algorithm 3, epochs $u < K$), for an LP solution $x$ and remaining time $\tau$:
--   $$p_j = \begin{cases} 0 & \text{if } x_j < \lambda_j \tau^{-1/4},\\ 1 & \text{else if } x_j > \lambda_j(1 - \tau^{-1/4}),\\ x_j/\lambda_j & \text{otherwise,}\end{cases}$$
--   and **plain probabilities** $p_j = x_j/\lambda_j$ (Algorithm 1; last epoch of Algorithm 3).
--   7. **Schedule.** $\tau_u = T^{(5/6)^u}$ is the time remaining at the $u$-th re-solving time $t^*_u = T - \tau_u$, and $K(T) = \lceil \log\log T / \log(6/5) \rceil$.
--   8. **IRT$^{K'}$ and HO$^{K'}$.** For $K' \in \mathbb N$, $v^{\mathrm{IRT}^{K'}}(T, C)$ is the expected revenue of the policy that, at each $t^*_u$, $u = 0, \dots, K'$, re-solves the DLP with right-hand side $C(t^*_u)/\tau_u$ to get $x^u = \mathrm{sel}(C(t^*_u)/\tau_u)$, uses thresholded probabilities on the epochs $[t^*_u, t^*_{u+1})$ of length $\tau_u - \tau_{u+1}$ for $u < K'$, and plain probabilities on the last epoch $[t^*_{K'}, T]$ of length $\tau_{K'}$. Thus $v^{\mathrm{IRT}} = v^{\mathrm{IRT}^{K(T)}}$ is Algorithm 3 and $v^{\mathrm{SPA}} = v^{\mathrm{IRT}^0}$ is Algorithm 1. $v^{\mathrm{HO}^{K'}}(T, C)$ is the value of the policy that follows IRT$^{K'}$ on $[0, t^*_{K'})$ and then earns the hindsight optimum $v^{\mathrm{HO}}(\tau_{K'}, C(t^*_{K'}))$ of the remaining horizon.
--
--   These are the objects of every statement of the mission: the regret of a policy is $v^{\mathrm{HO}} - v^{\pi}$ (Definition 1, p. 9).
--
--   **Formalization Note** Classes are `Fin n`, resources `Fin m`, `A l j` is $a_{lj}$. The LP values use the published `piValue` of `RLPBidPrice.Unbiased.Model`, $\mathrm{piValue}(A, r, x, y_0) = \sup\{r^\top y : Ay \le x, 0 \le y \le y_0\}$, which is the LP maximum when $x, y_0 \ge 0$. Expectations are sums of probability weights times values (`tsum`), with no measure theory. The window uses the standard Poisson representation: the window holds $N \sim$ Poisson$((\sum_j\lambda_j)\ell)$ arrivals, whose classes are i.i.d. with law $\lambda_j/\sum_i \lambda_i$, in order of arrival, each with an independent Bernoulli$(p_j)$ acceptance coin; by superposition and marking of independent Poisson processes this is the law of the arrivals of the model, and the acceptance rule is applied to them in order. The selector is a function of the right-hand side only, as in Algorithms 1 and 3. The re-solve right-hand side is $C(t^*_u)/\tau_u$; Algorithm 3 prints $C(t^*_k)/\tau_k$, a slip for the epoch index $u$. Page 14 defines $t^*_{K+1}=T$, so the last epoch has length $\tau_K$; the interval's open or closed endpoint at $T$ does not affect its value. $K(T)$ uses Lean's `Real.log 0 = 0` and `Nat.ceil` of a non-positive number $= 0$, so $K(T) = 0$ (IRT is SPA) for $1 \le T \le e$, where the printed formula is undefined at $T=1$ and non-positive otherwise. The Poisson mass function clamps a negative mean to $0$, a case that never occurs for $T \ge 1$.
-- source:
--   Bumpensanti, Wang, A Re-solving Heuristic with Uniformly Bounded Loss for Network Revenue Management, arXiv:1802.06192v3, Sec. 2, pp. 7–9, eqs. (2)–(3); Algorithm 1, p. 10; Sec. 4.1 and Algorithm 3, pp. 14–15; IRT^u and HO^u, p. 16

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model

open RLPBidPrice.Unbiased Matrix

namespace ResolvingNRM.IRT

/-- The Poisson probability mass function with mean `μ ≥ 0`:
`P(X = k) = e^{-μ} μ^k / k!`. A negative argument is read as `0` (it never occurs below). This
is Mathlib's `ProbabilityTheory.poissonPMFReal μ.toNNReal k`, restated on `ℝ`. -/
noncomputable def poissonPMF (μ : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-(max μ 0)) * (max μ 0) ^ k / (k.factorial : ℝ)

/-- An optimal-solution selector for the per-unit-time DLP (2), p. 8: for every right-hand side
`b ≥ 0`, `sel b` is feasible (`A (sel b) ≤ b`, `0 ≤ sel b ≤ lam`) and its objective `r ⬝ᵥ sel b`
is at least that of every feasible `y`. It models the paper's "x ← arg max" with an arbitrary
tie-breaking rule. -/
def IsDLPSelector {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (sel : (Fin m → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ b : Fin m → ℝ, 0 ≤ b →
    (A *ᵥ sel b ≤ b ∧ 0 ≤ sel b ∧ sel b ≤ lam) ∧
    ∀ y : Fin n → ℝ, A *ᵥ y ≤ b → 0 ≤ y → y ≤ lam → r ⬝ᵥ y ≤ r ⬝ᵥ sel b

/-- The DLP value (2), p. 8, over a horizon of length `T` with capacity `C`:
`v^DLP(T, C) = T · max { r ⬝ᵥ x : A x ≤ C / T, 0 ≤ x ≤ lam }`. -/
noncomputable def dlpValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (T : ℝ) (C : Fin m → ℝ) : ℝ :=
  T * piValue A r (fun l => C l / T) lam

/-- The hindsight optimum `v^HO = E[V^HO]` (Sec. 2.2.2, p. 9, eq. (3)) over a horizon of length
`T` with capacity `C`: the class-`j` arrival counts `Λ_j(T)` are independent Poisson(`λ_j T`), and
`V^HO = max { r ⬝ᵥ z : A z ≤ C, 0 ≤ z ≤ Λ(T) }` is the value of the (real) hindsight LP. -/
noncomputable def hindsightValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (T : ℝ) (C : Fin m → ℝ) : ℝ :=
  ∑' k : Fin n → ℕ,
    (∏ j, poissonPMF (lam j * T) (k j)) * piValue A r C (fun j => (k j : ℝ))

/-- One run of a probabilistic allocation over a window, on the list of arrivals in order,
each a pair (class `j`, acceptance coin). An arrival of class `j` is accepted iff its coin is
`true` and `A_j ≤ c` componentwise; then `r_j` is collected and `c := c − A_j`. Returns
(revenue collected, final remaining capacity). -/
noncomputable def runWindow {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ) :
    List (Fin n × Bool) → (Fin m → ℝ) → ℝ × (Fin m → ℝ)
  | [], c => (0, c)
  | (j, b) :: rest, c =>
      if b = true ∧ ∀ l, A l j ≤ c l then
        (r j + (runWindow A r rest (fun l => c l - A l j)).1,
          (runWindow A r rest (fun l => c l - A l j)).2)
      else runWindow A r rest c

/-- The expected value of a probabilistic allocation over a window of length `ℓ`, starting with
capacity `c`, accepting each class-`j` arrival with probability `p j` (when `A_j ≤` remaining
capacity), followed by the continuation value `W` of the capacity left at the end of the window.

By superposition and marking of independent Poisson processes, the window holds
`N ~ Poisson((∑_j λ_j) ℓ)` arrivals whose classes are i.i.d. with law `λ_j / ∑_j λ_j`; each arrival
carries an independent Bernoulli(`p_j`) acceptance coin. -/
noncomputable def windowValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (ℓ : ℝ) (p : Fin n → ℝ) (c : Fin m → ℝ) (W : (Fin m → ℝ) → ℝ) : ℝ :=
  ∑' N : ℕ, poissonPMF ((∑ j, lam j) * ℓ) N *
    ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool,
      (∏ i, (lam (cls i) / ∑ j, lam j) * (if coin i then p (cls i) else 1 - p (cls i))) *
        ((runWindow A r (List.ofFn fun i => (cls i, coin i)) c).1 +
          W (runWindow A r (List.ofFn fun i => (cls i, coin i)) c).2)

/-- Acceptance probabilities with thresholds (Algorithm 3, p. 15, epochs `u < K`), for an LP
solution `x` and remaining time `τ`, in the printed order: `0` if `x_j < λ_j τ^{-1/4}`; else `1`
if `x_j > λ_j (1 − τ^{-1/4})`; else `x_j / λ_j`. -/
noncomputable def thresholdProbs {n : ℕ} (lam : Fin n → ℝ) (τ : ℝ) (x : Fin n → ℝ) :
    Fin n → ℝ :=
  fun j =>
    if x j < lam j * τ ^ (-(1 / 4 : ℝ)) then 0
    else if x j > lam j * (1 - τ ^ (-(1 / 4 : ℝ))) then 1
    else x j / lam j

/-- Plain acceptance probabilities `x_j / λ_j` (Algorithm 1, p. 10; last epoch of Algorithm 3). -/
noncomputable def plainProbs {n : ℕ} (lam : Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => x j / lam j

/-- The remaining time at the `u`-th re-solving time: `τ_u = T^{(5/6)^u}` (Algorithm 3, p. 15),
so that `t*_u = T − τ_u`. -/
noncomputable def tau (T : ℝ) (u : ℕ) : ℝ := T ^ ((5 / 6 : ℝ) ^ u)

/-- The number of re-solves of IRT, `K = ⌈log log T / log(6/5)⌉` (Algorithm 3, p. 15), with
Lean's conventions `Real.log 0 = 0` and `Nat.ceil` of a negative number `= 0`. -/
noncomputable def Kirt (T : ℝ) : ℕ := Nat.ceil (Real.log (Real.log T) / Real.log (6 / 5))

/-- Backward recursion of the IRT family. `irtAux sel T d u c` is the expected revenue from the
`u`-th re-solving time `t*_u = T − τ_u` to `T`, with remaining capacity `c` at `t*_u`, when `d`
further re-solves remain. With `d = 0` the epoch `[t*_u, T]` (length `τ_u`) uses plain
probabilities from `x = sel (c / τ_u)`; with `d + 1` the epoch `[t*_u, t*_{u+1})` (length
`τ_u − τ_{u+1}`) uses thresholded probabilities from `x = sel (c / τ_u)` and continues with
`irtAux sel T d (u + 1)`. -/
noncomputable def irtAux {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (sel : (Fin m → ℝ) → (Fin n → ℝ)) (T : ℝ) : ℕ → ℕ → (Fin m → ℝ) → ℝ
  | 0, u, c =>
      windowValue A r lam (tau T u) (plainProbs lam (sel fun l => c l / tau T u)) c (fun _ => 0)
  | d + 1, u, c =>
      windowValue A r lam (tau T u - tau T (u + 1))
        (thresholdProbs lam (tau T u) (sel fun l => c l / tau T u)) c
        (irtAux A r lam sel T d (u + 1))

/-- `v^{IRT^{K'}}(T, C)`: the expected revenue of the policy `IRT^{K'}` (p. 16), which re-solves
at `t*_1, …, t*_{K'}`, thresholds in epochs `0, …, K' − 1` and uses plain probabilities in the
last epoch `[t*_{K'}, T]`. `irtValue … sel (Kirt T) T C` is IRT (Algorithm 3) and
`irtValue … sel 0 T C` is SPA (Algorithm 1). -/
noncomputable def irtValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (sel : (Fin m → ℝ) → (Fin n → ℝ)) (K' : ℕ) (T : ℝ) (C : Fin m → ℝ) : ℝ :=
  irtAux A r lam sel T K' 0 C

/-- Backward recursion of the HO family: as `irtAux`, but when no re-solve remains the
continuation from `t*_u` is the hindsight optimum of the remaining horizon `τ_u`. -/
noncomputable def hoAux {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (sel : (Fin m → ℝ) → (Fin n → ℝ)) (T : ℝ) : ℕ → ℕ → (Fin m → ℝ) → ℝ
  | 0, u, c => hindsightValue A r lam (tau T u) c
  | d + 1, u, c =>
      windowValue A r lam (tau T u - tau T (u + 1))
        (thresholdProbs lam (tau T u) (sel fun l => c l / tau T u)) c
        (hoAux A r lam sel T d (u + 1))

/-- `v^{HO^{K'}}(T, C)`: the expected revenue of `HO^{K'}` (p. 16), which follows IRT in
`[0, t*_{K'})` and then the hindsight optimal policy in `[t*_{K'}, T]`. -/
noncomputable def hoValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (sel : (Fin m → ℝ) → (Fin n → ℝ)) (K' : ℕ) (T : ℝ) (C : Fin m → ℝ) : ℝ :=
  hoAux A r lam sel T K' 0 C

end ResolvingNRM.IRT


