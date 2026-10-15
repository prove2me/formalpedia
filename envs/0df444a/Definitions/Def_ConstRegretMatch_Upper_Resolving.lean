-- Prove2me | Definitions.Def_ConstRegretMatch_Upper_Resolving
-- name    : ConstRegretMatch_Upper_Resolving
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:56.389998+00:00
-- url     : https://prove2.me/theorems/6fe9a43a-e44b-4ff7-9b05-87d72daafc78
-- title:
--   §3, p. 13 and (7), p. 22 — the exhaustive resolving policy with delay τ, its epoch queues Q^{t_k}, and h*
-- statement:
--   **Selections for (3).** Let $\mathcal M_0$ be the redundant matches. A selection $u\mapsto z^*(u)\in\mathbb Z^d_{\ge0}$ is a *resolving selection* if for every queue vector $u$, $z^*(u)$ is an optimal solution of
--   $$\max\ r\cdot z\quad\text{s.t.}\quad Mz\le u,\ z\in\mathbb Z^d_{\ge0},\ z_m=0\ (m\in\mathcal M_0), \tag{3}$$
--   i.e. (3) on the network with the redundant matches removed; ties are broken arbitrarily.
--
--   **The exhaustive resolving policy with inter-action delay $\tau$.** Matches are performed only at the decision epochs $t_k=k\tau$. At epoch $k\ge1$ the policy performs $z^*(Q^{t_k})$, where $Q^{t_k}$ is the pre-match queue vector, and then removes all remaining agents of the under-demanded types $j\in\mathcal Q_+$. Starting from the empty market,
--   $$Q^{t_0}=0,\qquad Q^{t_{k+1}}_i=\big(\text{post-match queue at } t_k\big)_i+A_i(k\tau,(k+1)\tau],$$
--   where the post-match queue is $0$ on $\mathcal Q_+$ and $Q^{t_k}_i-(Mz^*(Q^{t_k}))_i$ on $\mathcal Q_0$. The cumulative match count is $D^t=\sum_{1\le k\le\lfloor t/\tau\rfloor} z^*(Q^{t_k})$.
--
--   **The function $h^*$ of (7).** For a dual vector $\theta$ of (SPP),
--   $$h^*(u)=\min\Big\{\sum_{i\in\mathcal Q_0}\theta_is_i:\ Mz+s=u,\ z\in\mathbb Z^d_{\ge0},\ z_{\mathcal M_0}=0,\ s\in\mathbb Z^n_{\ge0}\Big\},$$
--   the $\theta$-weighted leftover of the over-demanded queues after an optimal integer matching of $u$.
--
--   $h^*$ is the Lyapunov function of §4.3; the theorems bound its expectation at the decision epochs and its stationary mean.
--
--   **Formalization Note** (3) is solved with $z_{\mathcal M_0}=0$, the "alternatively" reading of step 1 on p. 13. The queue $Q^{t_k}$ is the paper's queue *with* the removals of $\mathcal Q_+$ leftovers (p. 13); on $\mathcal Q_0$ it coincides with the actual queue $A^t-MD^{t-1}$ at $t=t_k$, and the match process $D$ is admissible in the unremoved system. The epoch $t_0=0$ acts on an empty market and is omitted. The paper writes (7) after the reduction $\mathcal M_0=\emptyset$ (p. 21), with constraints $z_m+y^ms=y^mu$, $y^js=y^ju$; since $\mathcal B$ is invertible these say exactly $Mz+s=u$ with $z_{\mathcal M_0}=0$, and because $\theta_j=0$ on $\mathcal Q_+$ and $\theta^\top M_m=r_m$ on $\mathcal M_+$, $h^*(u)=\theta\cdot u-\max\{r\cdot z: Mz\le u,\ z_{\mathcal M_0}=0\}$. The minimum runs over the finite box of feasible $z$ (the slack is $s=u-Mz$); the value of $z=0$ is inserted to make the set syntactically nonempty, which does not change the minimum.
-- source:
--   Kerimov, Ashlagi, Gurvich, Dynamic Matching: Characterizing and Achieving Constant Regret, SSRN 3824407 (Sep 14, 2022), p. 13, §3 steps 1–3 and (3); pp. 21–22, (7)

import Mathlib
import Definitions.Def_ConstRegretMatch_Upper_Network
import Definitions.Def_ConstRegretMatch_Upper_SPP
import Definitions.Def_ConstRegretMatch_Upper_Arrivals
import Definitions.Def_ConstRegretMatch_Upper_Policy

namespace ConstRegretMatch.Upper

variable {n d : ℕ}

/-- `sel` is a tie-breaking selection of maximizers of the integer program (3) (§3, p. 13) on the
network with the redundant matches `M0` removed: for every queue vector `u`, `sel u` is feasible
(`M (sel u) ≤ u`), vanishes on `M0`, and maximizes `r · y` over all feasible `y ∈ ℤ^d_{≥0}` that
vanish on `M0`. Ties are broken arbitrarily; statements quantify over every such selection. -/
def IsResolvingSelection (N : MatchingNetwork n d) (r : Fin d → ℝ) (M0 : Finset (Fin d))
    (sel : (Fin n → ℕ) → Fin d → ℕ) : Prop :=
  ∀ u, StaticFeasible N u (sel u) ∧ (∀ m ∈ M0, sel u m = 0) ∧
    ∀ y, StaticFeasible N u y → (∀ m ∈ M0, y m = 0) →
      ∑ m, r m * (y m : ℝ) ≤ ∑ m, r m * (sel u m : ℝ)

/-- One decision epoch of the exhaustive resolving policy (§3, p. 13), applied to the pre-match
queue vector `q`: perform the matches `sel q`, then remove all remaining agents of the
under-demanded types `Qp = 𝒬₊`. The result is the post-match queue vector. -/
def postMatch (N : MatchingNetwork n d) (sel : (Fin n → ℕ) → Fin d → ℕ) (Qp : Finset (Fin n))
    (q : Fin n → ℕ) : Fin n → ℕ :=
  fun i => if i ∈ Qp then 0 else q i - ∑ m, N.inc i m * sel q m

/-- The pre-match queue vector `Q^{t_k}` of the exhaustive resolving policy at the decision epoch
`t_k = kτ`, started empty at time `0` (`𝔼₀`). Between epochs `k` and `k + 1` the arrivals at times
`kτ + 1, …, (k+1)τ` join the post-match queues of epoch `k`. This is the paper's queue with the
removals of `𝒬₊` leftovers (p. 13); on the types outside `Qp` it is the actual queue. -/
def epochQueue (N : MatchingNetwork n d) (sel : (Fin n → ℕ) → Fin d → ℕ) (Qp : Finset (Fin n))
    (τ : ℕ) : ℕ → (ℕ → Fin n) → Fin n → ℕ
  | 0, _ => fun _ => 0
  | k + 1, ω => fun i =>
      postMatch N sel Qp (epochQueue N sel Qp τ k ω) i + arrivalsBetween ω (k * τ) ((k + 1) * τ) i

/-- The exhaustive resolving policy with inter-action delay `τ` (§3, p. 13): matches are performed
only at the decision epochs `t_k = kτ`, `k ≥ 1`, and at epoch `k` the policy performs `sel (Q^{t_k})`.
`D^t` is the total over the epochs `1 ≤ k ≤ ⌊t/τ⌋`. (The epoch `t_0 = 0` acts on an empty market.) -/
def resolvingPolicy (N : MatchingNetwork n d) (sel : (Fin n → ℕ) → Fin d → ℕ) (Qp : Finset (Fin n))
    (τ : ℕ) : Policy n d :=
  fun t ω m => ∑ k ∈ Finset.Icc 1 (t / τ), sel (epochQueue N sel Qp τ k ω) m

open Classical in
/-- The function `h*` of (7) (p. 22), on the network with the redundant matches `ℳ₀ = Mzero z`
removed:
`h*(u) = min {∑_{i ∈ 𝒬₀} θ_i s_i : M y + s = u, y ∈ ℤ^d_{≥0}, y_{ℳ₀} = 0, s ∈ ℤ^n_{≥0}}`,
with `θ` the dual vector of (SPP) (`IsSPPDual`) and `𝒬₀ = Qzero s0`. The slack is determined by `y`
(`s = u - M y`), so the minimum runs over the feasible `y` of the box `{0, …, ∑_i u_i}^d` (every
feasible `y` lies in it); `y = 0` is feasible with value `∑_{i ∈ 𝒬₀} θ_i u_i`, which the `insert`
makes syntactically present (it does not change the minimum). With `θ_j = 0` on `𝒬₊` and
`θᵀM_m = r_m` on `ℳ₊` this equals `θ · u - max {r · y : M y ≤ u, y_{ℳ₀} = 0}`, the form of (7)
after the reduction `ℳ₀ = ∅` of p. 21. -/
noncomputable def hstar (N : MatchingNetwork n d) (z0 : Fin d → ℝ) (s0 : Fin n → ℝ)
    (θ : Fin n → ℝ) (u : Fin n → ℕ) : ℝ :=
  (insert (∑ i ∈ Qzero s0, θ i * (u i : ℝ))
    (((Fintype.piFinset (fun _ : Fin d => Finset.range (∑ i, u i + 1))).filter
        (fun y => StaticFeasible N u y ∧ ∀ m ∈ Mzero z0, y m = 0)).image
      (fun y => ∑ i ∈ Qzero s0, θ i * ((u i : ℝ) - ∑ m, N.M i m * (y m : ℝ))))).min'
    (Finset.insert_nonempty _ _)

end ConstRegretMatch.Upper


