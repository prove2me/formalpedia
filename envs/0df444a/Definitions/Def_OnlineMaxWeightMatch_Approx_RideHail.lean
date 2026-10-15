-- Prove2me | Definitions.Def_OnlineMaxWeightMatch_Approx_RideHail
-- name    : OnlineMaxWeightMatch_Approx_RideHail
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:05.21168+00:00
-- url     : https://prove2.me/theorems/2d92675c-3d72-4783-8b5d-3030d23cb1ed
-- title:
--   The RideHail problem, deterministic online policies, and the optimal online value OPT_on
-- statement:
--   A **RideHail instance** $I$ (online Bayesian bipartite matching) consists of $m$ bins (taxis), indexed by a finite set $\iota$, and $n$ balls (passengers) $t=1,\dots,n$ that are revealed one at a time in this fixed order. Ball $t$ arrives with probability $p_t\in[0,1]$, independently of the other balls, and if it arrives it can be matched, irrevocably and before ball $t+1$ is revealed, to an unmatched bin $i$, for profit $w_{i,t}\ge 0$. A missing edge is an edge of weight $0$.
--
--   An **arrival pattern** is a vector $a\in\{0,1\}^n$; it has probability $\prod_t p_t^{a_t}(1-p_t)^{1-a_t}$.
--
--   A **deterministic online policy** $\pi$ decides, when ball $t$ is processed, which bin (if any) to match $t$ to; its decision may depend on the arrivals $a_1,\dots,a_t$ of balls $1,\dots,t$ only, never on $a_{t+1},\dots,a_n$. Running $\pi$ on $a$ produces a matching $M_\pi(a)$: ball $t$ is matched to the bin $\pi$ names exactly when $t$ arrived and that bin is still unmatched. The expected profit of $\pi$ is
--
--   $$
--   \mathrm{val}_I(\pi)=\sum_{a\in\{0,1\}^n}\Pr[a]\sum_{(i,t)\in M_\pi(a)}w_{i,t},
--   $$
--
--   and the value of the **optimal online algorithm** is
--
--   $$
--   \mathrm{OPT}_{on}(I)=\sup_{\pi}\ \mathrm{val}_I(\pi),
--   $$
--
--   the supremum over all deterministic online policies (a finite set, so the supremum is a maximum).
--
--   This is the benchmark of Theorem 1.2. It is not the offline optimum (the "prophet"), which sees all arrivals in advance and against which no online algorithm beats $1/2$.
--
--   **Formalization Note** Balls are `Fin n` (paper ball $t$ is Lean index $t-1$). A policy is a function of the ball index and the arrival indicators of balls $s\le t$, returning `Option ι`; a choice of an already matched bin, or any choice for a ball that did not arrive, has no effect. Randomized online algorithms are mixtures of deterministic ones, so restricting the supremum to deterministic policies does not change $\mathrm{OPT}_{on}$.
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 1 (§1, model), p. 4 (§2, OPT_on), p. 10 footnote 2

import Mathlib

open Classical

namespace OnlineMaxWeightMatch.Approx

/-- A **RideHail instance** (§1, p. 1): `m` bins (taxis), indexed by a finite type `ι`, and
`n` balls (passengers), indexed by `Fin n` in their fixed order of arrival (paper ball `t` is
Lean index `t - 1`). Ball `t` arrives with probability `p t`, independently of all other balls,
and if it arrives it may be matched to bin `i` for profit `w i t ≥ 0`. A missing edge is an edge
of weight `0`. -/
structure RideHailInstance (ι : Type*) (n : ℕ) where
  /-- the weight `w_{i,t}` of edge `(i, t)` -/
  w : ι → Fin n → ℝ
  /-- the arrival probability `p_t` of ball `t` -/
  p : Fin n → ℝ
  w_nonneg : ∀ i t, 0 ≤ w i t
  p_nonneg : ∀ t, 0 ≤ p t
  p_le_one : ∀ t, p t ≤ 1

variable {ι : Type*} {n : ℕ}

/-- The probability of the arrival pattern `a` (`a t = true` iff ball `t` arrives): the balls
arrive independently, ball `t` with probability `p t`. -/
noncomputable def arrivalProb (I : RideHailInstance ι n) (a : Fin n → Bool) : ℝ :=
  ∏ t, if a t then I.p t else 1 - I.p t

/-- A **deterministic online policy**. When ball `t` is processed, the policy sees the arrival
indicators of balls `s ≤ t` only (in particular whether `t` itself arrived) and names a bin to
match `t` to, or `none`. It never sees the arrivals of balls after `t`: the policy is
non-anticipating. -/
def OnlinePolicy (ι : Type*) (n : ℕ) : Type _ :=
  (t : Fin n) → ({s : Fin n // s ≤ t} → Bool) → Option ι

/-- The edges matched by policy `π` on arrival pattern `a` after processing the first `k` balls.
Ball `t` is matched to the bin `i` the policy names exactly when `t` arrived and `i` is still
unmatched; any other choice has no effect. -/
noncomputable def OnlinePolicy.matchingUpTo (π : OnlinePolicy ι n) (a : Fin n → Bool) :
    ℕ → Finset (ι × Fin n)
  | 0 => ∅
  | k + 1 =>
    if h : k < n then
      match π ⟨k, h⟩ (fun s => a s.1) with
      | some i =>
        if a ⟨k, h⟩ = true ∧ ∀ s, (i, s) ∉ OnlinePolicy.matchingUpTo π a k then
          insert (i, ⟨k, h⟩) (OnlinePolicy.matchingUpTo π a k)
        else OnlinePolicy.matchingUpTo π a k
      | none => OnlinePolicy.matchingUpTo π a k
    else OnlinePolicy.matchingUpTo π a k

/-- The matching output by policy `π` on arrival pattern `a`. -/
noncomputable def OnlinePolicy.matching (π : OnlinePolicy ι n) (a : Fin n → Bool) :
    Finset (ι × Fin n) :=
  π.matchingUpTo a n

/-- The expected profit of policy `π` on instance `I`. -/
noncomputable def policyValue [Fintype ι] (I : RideHailInstance ι n) (π : OnlinePolicy ι n) : ℝ :=
  ∑ a : Fin n → Bool, arrivalProb I a * ∑ e ∈ π.matching a, I.w e.1 e.2

/-- `OPT_on(I)`: the expected profit of the optimal online algorithm, the supremum of the
expected profits of all deterministic online policies (a finite set). Randomized online
algorithms are mixtures of deterministic ones and do not raise the supremum. -/
noncomputable def optOn [Fintype ι] (I : RideHailInstance ι n) : ℝ :=
  ⨆ π : OnlinePolicy ι n, policyValue I π

end OnlineMaxWeightMatch.Approx


