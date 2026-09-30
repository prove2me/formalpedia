-- Prove2me | Definitions.Def_ComplementFreeCA_CFRounding_LP
-- name    : ComplementFreeCA_CFRounding_LP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:12:41.887828+00:00
-- url     : https://prove2.me/theorems/96b51713-4ed4-49fc-9d95-266d90ae0860
-- title:
--   The LP relaxation of the combinatorial auction and its randomized rounding law
-- statement:
--   The **standard LP relaxation** of the combinatorial auction has a variable $x_{i,S}$ for every bidder $i$ and bundle $S\subseteq M$:
--   $$\text{maximize } \sum_{i,S} x_{i,S}\,v_i(S)\quad\text{s.t.}\quad \sum_{i,\,S\ni j} x_{i,S}\le 1\ \ (j\in M),\qquad \sum_S x_{i,S}\le 1\ \ (i\in N),\qquad x_{i,S}\ge 0.$$
--   A point satisfying the three constraint families is **LP-feasible**; its objective value is $\sum_{i,S}x_{i,S}v_i(S)$, and $x$ is **optimal** if it is feasible and its value is at least that of every feasible point. The optimal value is denoted $OPT^*$.
--
--   **Randomized rounding.** Given a feasible $x$, each bidder $i$ independently draws a bundle $S_i$: bundle $S$ with probability $x_{i,S}$, and the empty bundle with the remaining probability $1-\sum_S x_{i,S}$. Thus bidder $i$'s law is
--   $$q_i(S)=x_{i,S}+\mathbf 1[S=\emptyset]\Big(1-\sum_T x_{i,T}\Big),$$
--   and a profile $\sigma=(S_1,\dots,S_n)$ has probability $\prod_i q_i(S_i)$. The probability of an event $E$ (a set of profiles) is $\sum_{\sigma\in E}\prod_i q_i(\sigma_i)$.
--
--   These objects are the starting point of both rounding algorithms of Section 3: the rounded profile, the **preallocation**, has expected welfare $OPT^*$ but may give an item to several bidders.
--
--   **Formalization Note** Probabilities are explicit finite sums over the finitely many profiles `σ : Fin n → Finset (Fin m)`, which makes independence across bidders literal. The empty bundle receives both its own weight $x_{i,\emptyset}$ and the leftover mass, the only reading under which the weights sum to $1$. The rounding probability is meaningful only for feasible $x$; every statement using it assumes feasibility.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 5, §3 (the LP relaxation display and the randomized rounding paragraph)

import Mathlib
import Definitions.Def_ComplementFreeCA_CFRounding_Auction

namespace ComplementFreeCA.CFRounding

/-- Feasibility for the standard LP relaxation of the combinatorial auction (p. 5):
for each item `j`, `∑_{i, S ∋ j} x i S ≤ 1`; for each bidder `i`, `∑_S x i S ≤ 1`;
and `x i S ≥ 0`. Sums range over all bundles `S : Finset (Fin m)`. -/
def IsLPFeasible {n m : ℕ} (x : Fin n → Finset (Fin m) → ℝ) : Prop :=
  (∀ j : Fin m, ∑ i, ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) => j ∈ S), x i S ≤ 1) ∧
  (∀ i : Fin n, ∑ S, x i S ≤ 1) ∧
  (∀ i S, 0 ≤ x i S)

/-- The LP objective `∑_{i,S} x i S · vᵢ(S)` (p. 5). -/
def lpValue {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (x : Fin n → Finset (Fin m) → ℝ) : ℝ :=
  ∑ i, ∑ S, x i S * v i S

/-- `x` is an optimal fractional solution of the LP relaxation; its value is `OPT*`. -/
def IsOptimalLP {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (x : Fin n → Finset (Fin m) → ℝ) :
    Prop :=
  IsLPFeasible x ∧ ∀ y, IsLPFeasible y → lpValue v y ≤ lpValue v x

/-- The law of bidder `i`'s bundle under randomized rounding (p. 5): the bundle `S` is chosen
with probability `x i S`, and the empty bundle additionally receives the leftover mass
`1 - ∑_T x i T`. -/
def roundLaw {n m : ℕ} (x : Fin n → Finset (Fin m) → ℝ) (i : Fin n) (S : Finset (Fin m)) : ℝ :=
  x i S + if S = ∅ then 1 - ∑ T, x i T else 0

open Classical in
/-- The probability, under randomized rounding (bidders choose independently), that the
preallocation `σ` (bidder `i` receives `σ i`) satisfies the event `E`: the finite sum of the
product weights `∏ᵢ roundLaw x i (σ i)` over all profiles `σ` in `E`. -/
noncomputable def roundProb {n m : ℕ} (x : Fin n → Finset (Fin m) → ℝ)
    (E : (Fin n → Finset (Fin m)) → Prop) : ℝ :=
  ∑ σ : Fin n → Finset (Fin m), if E σ then ∏ i, roundLaw x i (σ i) else 0

end ComplementFreeCA.CFRounding


