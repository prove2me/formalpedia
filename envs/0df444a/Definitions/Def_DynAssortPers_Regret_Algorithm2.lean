-- Prove2me | Definitions.Def_DynAssortPers_Regret_Algorithm2
-- name    : DynAssortPers_Regret_Algorithm2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:16:08.374722+00:00
-- url     : https://prove2.me/theorems/bca3ad16-22f7-4d81-909d-cf9eb946ec4b
-- title:
--   Algorithm 2, p. 23, and Definition 1, p. 6 — the trajectory law of $\pi_{\text{nuc-norm}}(C,\lambda)$ and its regret against the $\Theta^\star$-greedy algorithm
-- statement:
--   Fix an instance: $m$ types, $n$ items, a cardinality bound $K$, revenues $W\in\mathbb R^{m\times n}$, a type distribution $\mu^\star$ and preference parameters $\Theta^\star\in\mathbb R^{m\times n}$. In round $t=1,2,\dots$ a customer of type $i_t$ arrives with probability $\mu^\star_{i_t}$, the retailer offers $S_t$, and the customer chooses $j_t$ from the MNL law with parameters $\Theta^\star_{i_t}$.
--
--   **Algorithm 2** $\pi_{\text{nuc-norm}}(C,\lambda)$ keeps a sample $\mathcal O$ of randomized observations, initially empty. At round $t$:
--
--   1. if $|\mathcal O|\le Cr(m+n)\log t$ (**explore**), it draws $S_t$ uniformly from the $\binom nK$ subsets of size $K$, observes $j_t$, and appends $(i_t,j_t,S_t)$ to $\mathcal O$;
--   2. otherwise (**exploit**), it offers some $S_t\in S^\star(W_{i_t},\widehat\Theta_{i_t};K)$, where $\widehat\Theta$ is a solution of (5) for the current sample.
--
--   The module takes the two choices as parameters: a map `est` from samples to matrices (later required to return a solution of (5)), and a map `exploit` from a type and a matrix to an assortment (later required to be optimal). The **law of a $T$-round history** $h=((i_t,S_t,j_t))_{t\le T}$ is
--   $$\mathbb P(h)=\prod_{t=1}^{T}\mu^\star_{i_t}\;\mathbb P(S_t\mid h_{<t},i_t)\;\mathbb P(j_t\mid S_t,\Theta^\star_{i_t}),$$
--   with $\mathbb P(S_t\mid h_{<t},i_t)$ equal to $1/\binom nK$ on sets of size $K$ at exploration rounds, and to the indicator of the exploited set otherwise. The **regret** (Definition 1) against the $\Theta^\star$-greedy algorithm is
--   $$\mathrm{Regret}(T)=T\sum_{i=1}^m\mu^\star_i\max_{|S|\le K}F(S;W_i,\Theta^\star_i)-\sum_h\mathbb P(h)\sum_{t=1}^TF(S_t;W_{i_t},\Theta^\star_{i_t}).$$
--   The module also counts the exploration rounds $|T_{\mathrm{explore}}|$ of a history.
--
--   **Formalization Note** Definition 1 compares expected realized rewards. By the tower property, the expected reward of round $t$ given the type and the offered set is $F(S_t;W_{i_t},\Theta^\star_{i_t})$, and the $\Theta^\star$-greedy algorithm earns $\sum_i\mu^\star_i\max_{|S|\le K}F(S;W_i,\Theta^\star_i)$ per round whatever its tie-breaking; the regret is written in that form. All expectations are finite sums over histories. Rounds are 1-based in the test $\log t$. The estimate used at an exploitation round is `est` applied to the current sample, which only changes at exploration rounds, so it is the estimate of the last exploration round. Types and items are 0-based, and no purchase is `none`. Measurability with respect to the filtration $\mathcal F_t$ is not formalized; Algorithm 2's law is written out explicitly.
-- source:
--   Kallus, Udell, Dynamic Assortment Personalization in High Dimensions, arXiv:1610.05604 (PDF sha256 2b010481…216a), Sec. 2, pp. 5–6 (process, Θ-greedy algorithm, Definition 1); Algorithm 2, p. 23; proof of Theorem 6, p. 48 (T_explore)

import Mathlib
import Definitions.Def_DynAssortPers_Regret_MNL
import Definitions.Def_DynAssortPers_Regret_Estimator

namespace DynAssortPers.Regret

open MatrixCompletion
open scoped Classical

/-- One round of the process (Sec. 2, p. 5): the customer type `i_t`, the offered set `S_t` and
the customer's choice `j_t` (`none` = no purchase). -/
abbrev Step (m n : ℕ) : Type := Fin m × Finset (Fin n) × Option (Fin n)

/-- The observation `(i_t, j_t, S_t)` recorded from a round. -/
def Step.toObs {m n : ℕ} (x : Step m n) : Obs m n := (x.1, x.2.2, x.2.1)

/-- The exploration test of Algorithm 2 (p. 23) at round `t` (1-based) with current sample `𝒪`:
`|𝒪| ≤ C r (m + n) log t`, natural logarithm. -/
def Explores (C : ℝ) (r m n t : ℕ) (O : List (Obs m n)) : Prop :=
  (O.length : ℝ) ≤ C * r * ((m : ℝ) + n) * Real.log t

/-- Run the sample update of Algorithm 2 over a list of rounds, starting at round `t` with
sample `O`: a round at which the test passes appends its observation to the sample. -/
noncomputable def sampleAux {m n : ℕ} (C : ℝ) (r : ℕ) :
    ℕ → List (Obs m n) → List (Step m n) → List (Obs m n)
  | _, O, [] => O
  | t, O, x :: xs =>
      sampleAux C r (t + 1) (if Explores C r m n t O then O ++ [x.toObs] else O) xs

/-- The sample `𝒪` of Algorithm 2 after the rounds `pre` (rounds `1, …, |pre|`, in order),
starting from `𝒪 = ∅` at round `1`. -/
noncomputable def sampleAfter {m n : ℕ} (C : ℝ) (r : ℕ) (pre : List (Step m n)) : List (Obs m n) :=
  sampleAux C r 1 [] pre

/-- The probability that Algorithm 2 `π_nuc-norm(C, λ)` (p. 23) offers `S` at round `|pre| + 1`,
given the earlier rounds `pre` and the current type `i`. With `𝒪` the current sample:
* if `|𝒪| ≤ C r (m + n) log t` (explore), `S` is uniform over the subsets of size `K`;
* otherwise (exploit), `S = exploit i Θ̂` with `Θ̂ = est 𝒪` the estimate computed from the sample
  (the sample, and hence `Θ̂`, changes only at exploration rounds).
`est` and `exploit` are the selections from the argmin of (5) and from `S⋆(W_i, Θ̂_i; K)`. -/
noncomputable def alg2SetProb {m n : ℕ} (C : ℝ) (r K : ℕ)
    (est : List (Obs m n) → RealMatrix m n) (exploit : Fin m → RealMatrix m n → Finset (Fin n))
    (pre : List (Step m n)) (i : Fin m) (S : Finset (Fin n)) : ℝ :=
  if Explores C r m n (pre.length + 1) (sampleAfter C r pre) then
    (if S.card = K then 1 / ((n.choose K : ℕ) : ℝ) else 0)
  else
    (if S = exploit i (est (sampleAfter C r pre)) then 1 else 0)

/-- The probability of a `T`-round history `h` under Algorithm 2 (Sec. 2, p. 5): the product over
rounds of the arrival probability `μ⋆_{i_t}`, the probability of the offered set given the past
and `i_t`, and the MNL choice probability under `Θ⋆_{i_t}`. -/
noncomputable def alg2Weight {m n : ℕ} (μ : Fin m → ℝ) (Θs : RealMatrix m n) (C : ℝ) (r K : ℕ)
    (est : List (Obs m n) → RealMatrix m n) (exploit : Fin m → RealMatrix m n → Finset (Fin n))
    {T : ℕ} (h : Fin T → Step m n) : ℝ :=
  ∏ k : Fin T, μ (h k).1 *
    alg2SetProb C r K est exploit ((List.ofFn h).take k) (h k).1 (h k).2.1 *
    choiceLaw (Θs (h k).1) (h k).2.1 (h k).2.2

/-- The regret (Definition 1, p. 6) of Algorithm 2 at time `T` against the `Θ⋆`-greedy algorithm,
after the tower property: the greedy algorithm earns `∑_i μ⋆_i max_{|S| ≤ K} F(S; W_i, Θ⋆_i)` per
round, and Algorithm 2 earns `F(S_t; W_{i_t}, Θ⋆_{i_t})` in expectation at round `t`. -/
noncomputable def alg2Regret {m n : ℕ} (W : RealMatrix m n) (μ : Fin m → ℝ) (Θs : RealMatrix m n)
    (K : ℕ) (C : ℝ) (r : ℕ)
    (est : List (Obs m n) → RealMatrix m n) (exploit : Fin m → RealMatrix m n → Finset (Fin n))
    (T : ℕ) : ℝ :=
  (T : ℝ) * ∑ i : Fin m, μ i * optVal (W i) (Θs i) K -
    ∑ h : Fin T → Step m n, alg2Weight μ Θs C r K est exploit h *
      ∑ k : Fin T, revenue (h k).2.1 (W (h k).1) (Θs (h k).1)

/-- The number `|T_explore|` of exploration rounds of Algorithm 2 among the rounds `1, …, T` of a
history `h` (p. 48). -/
noncomputable def explorationCount {m n : ℕ} (C : ℝ) (r : ℕ) {T : ℕ} (h : Fin T → Step m n) : ℕ :=
  (Finset.univ.filter (fun k : Fin T =>
    Explores C r m n ((k : ℕ) + 1) (sampleAfter C r ((List.ofFn h).take k)))).card

end DynAssortPers.Regret


