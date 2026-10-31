-- Prove2me | Definitions.Def_FiniteMemPOMDP_superSupp
-- name    : FiniteMemPOMDP_superSupp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:32:53.401627+00:00
-- url     : https://prove2.me/theorems/cbf3395d-6310-4d80-abbb-a22571442431
-- title:
--   Super-support $B_m=(B^1_m,\dots,B^I_m)$
-- statement:
--   For a value class $\mathcal K_i$ and a history $h_m\in\mathcal H_m$,
--
--   $$\mathcal B^i_m(h_m)=\bigcup_{k_1\in\mathcal K_i}\{k\in\mathcal K:\ \mathbb P^{k_1}_\sigma(H_m=h_m)>0,\ \mathbb P^{k_1}_\sigma(K_m=k\mid H_m=h_m)>0\}:$$
--
--   the states reachable at stage $m$ from some state of $\mathcal K_i$ when playing $\sigma$ and observing $h_m$. The tuple $(\mathcal B^1_m(h_m),\dots,\mathcal B^I_m(h_m))$ is the **super-support** after $h_m$.
--
--   `superSupp Γ σ K₀ h` is this set for an arbitrary set $K_0$ of initial states, and `superSuppTuple Γ p σ h c` is the component of the value class $c$.
--
--   **Formalization Note** The two positivity conditions are combined into $\mathbb P^{k_1}_\sigma(H=h,K=k)>0$. Histories are indexed by their length, and components by class values (empty for non-values).
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, Definition 6.2, p.15

import Mathlib
import Definitions.Def_FiniteMemPOMDP_belief
import Definitions.Def_FiniteMemPOMDP_valueClass

namespace FiniteMemPOMDP

variable {K A S : Type} [Fintype K] [DecidableEq K] [Fintype A] [Fintype S] [Nonempty A]
  [Nonempty S]

/-- The states reachable after the history `h` from some initial state in `K₀` under `σ`:
`{k | ∃ k₁ ∈ K₀, P^{k₁}_σ(H = h, K = k) > 0}`. -/
def superSupp (Γ : POMDP K A S) (σ : List (A × S) → A) (K₀ : Set K) (h : List (A × S)) :
    Set K :=
  {k | ∃ k₁ ∈ K₀, 0 < jointProb Γ (pointBelief k₁) σ h k}

/-- **The super-support `B_m(h_m) = (B^1_m(h_m), …, B^I_m(h_m))`.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, Definition 6.2, p.15: "For i ∈ [1 .. I] and
m ≥ 0, define, for all hm ∈ Hm,
B^i_m(hm) := ∪_{k1∈Ki} {k ∈ K : P^{k1}_σ(Hm = hm) > 0, P^{k1}_σ(Km = k|Hm = hm) > 0}. In other
words, B^i_m(hm) is the set of all reachable states at stage m starting from some state in Ki,
playing the strategy σ and obtaining history hm (if Hm = hm is possible). … Bm := (B^1_m, . . . ,
B^I_m) the super-support at stage m."

`superSuppTuple Γ p σ h c` is the component of the super-support after the history `h` that
belongs to the value class `c`: the states `k` such that `P^{k₁}_σ(H = h, K = k) > 0` for some
`k₁ ∈ valueClass Γ p σ c`.

**Formalization Note** `P(H = h) > 0` and `P(K = k | H = h) > 0` together say
`P(H = h, K = k) > 0`, so the joint probability is used. Histories are indexed by their length:
`B^i_m(h_m)` with `h_m ∈ H_m` is `superSuppTuple Γ p σ h_m γ^i_∞` (`|h_m| = m − 1`). The
components are indexed by the class value `c` (see `valueClass`); for a `c` with empty class the
component is empty. -/
def superSuppTuple (Γ : POMDP K A S) (p : stdSimplex ℝ K) (σ : List (A × S) → A)
    (h : List (A × S)) : ℝ → Set K :=
  fun c => superSupp Γ σ ↑(valueClass Γ p σ c) h

end FiniteMemPOMDP


