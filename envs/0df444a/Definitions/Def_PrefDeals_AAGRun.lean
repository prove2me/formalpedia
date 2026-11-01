-- Prove2me | Definitions.Def_PrefDeals_AAGRun
-- name    : PrefDeals_AAGRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:21:56.912994+00:00
-- url     : https://prove2.me/theorems/d0881139-b0dd-4d08-94b8-5237cb8ea4ae
-- title:
--   Runs of the Auction-Adjusted Greedy algorithm
-- statement:
--   The algorithm takes a stream $A$ and a set of buyers $S$ and outputs a priority sequence of deals. A list `out` is an **output of the algorithm on $(A,S)$** when one of the following holds (with $S_0,S_1$ as in Figure 1):
--
--   1. $S_1=\emptyset$, and `out` lists the empty deals $(0,0,\emptyset)$ of the buyers in $S_0$;
--   2. $S_1=\{i\}$, and `out` is $(i,(\mathrm E_A[v_i],1,A))$ followed by the empty deals of $S_0$;
--   3. $|S_1|\ge2$, buyer $i\in S_1$ maximizes $\rho_j$ over $S_1$ (rule (2)), and `out` is $(i,(\rho_i,\mu_i,A))$, followed by an output of the algorithm on $(A\cap\{v_i<\theta_i\},\ S_1\setminus\{i\})$, followed by the empty deals of $S_0$.
--
--   The relation describes every run of the algorithm of Figure 1, for every choice in the $\arg\max$ of (2).
--
--   **Formalization Note** The empty deals of $S_0$ may be listed in any order; they sell nothing. The case $S_1=\emptyset$ is not reached by the paper's algorithm from a stream of positive mass, which stops once the stream is empty (p.28); it returns the empty deals.
-- source:
--   Kim, Mirrokni & Nazerzadeh, Deals or No Deals: Contract Design for Online Advertising, SSRN 2693037, Figure 1 and eq. (2), p.11

import Mathlib
import Definitions.Def_PrefDeals_aagDeal

open MeasureTheory

namespace PrefDeals

/-- **The runs of the Auction-Adjusted Greedy algorithm.**
Kim, Mirrokni & Nazerzadeh, *Deals or No Deals*, SSRN 2693037, Figure 1, p.11:
"Input: Stream of impressions `𝓘` and a set of buyers `S`. Output: Sequence of deals `𝓓`.
Let `S₀ = {j ∈ S | Pr_𝓘[vⱼ = v₍₁₎(S)] = 0}` and `S₁ = S \ S₀`. `𝓓₀ ← {(ρⱼ = 0, µⱼ = 0, 𝓘ⱼ = ∅)}_{j∈S₀}`.
If `(|S₁| = {i})` Return `(ρᵢ = E_𝓘[vᵢ], µᵢ = 1, 𝓘ᵢ = 𝓘) + 𝓓₀`. For each buyer `j ∈ S₁` Choose the
smallest `θⱼ` such that `Pr_𝓘[vⱼ ≥ θⱼ] = Pr_𝓘[vⱼ = v₍₁₎(S₁)]`. `ρⱼ ← E_𝓘[vⱼ|vⱼ ≥ θⱼ]`.
`µⱼ ← Pr_𝓘[vⱼ ≥ θⱼ]`. `𝓘ⱼ ← 𝓘`. Choose a buyer `i ∈ arg max_{j∈S₁} ρⱼ` (2).
`𝓓 ← (ρᵢ, µᵢ, 𝓘ᵢ) + 𝓐𝓐𝓖(𝓘 \ {vᵢ ≥ θᵢ}, S₁ \ {i}) + 𝓓₀`. Return `𝓓`", where (p.10)
"`𝓘 \ {vⱼ ≥ θⱼ}` denotes the set of impressions in `𝓘` where `vⱼ < θⱼ`".

`AAGRun M A S out` says that `out`, a list of (buyer, deal) pairs in priority order, is an output of
the algorithm on the stream `A` with buyers `S`:
1. `none`: if `S₁ = ∅`, `out` is the empty deals `(0, 0, ∅)` for the buyers of `S₀`;
2. `single`: if `S₁ = {i}`, `out` is `(i, (E_A[vᵢ], 1, A))` followed by the empty deals of `S₀`;
3. `step`: if `|S₁| ≥ 2` and `i ∈ S₁` maximizes `ρⱼ` over `S₁`, `out` is `(i, (ρᵢ, µᵢ, A))`, then an
   output of the algorithm on `A ∩ {vᵢ < θᵢ}` with buyers `S₁ \ {i}`, then the empty deals of `S₀`.

**Formalization Note.** The relation is nondeterministic: every maximizer `i` in (2) gives a run, and
the empty deals of `S₀` may be listed in any order (they sell nothing). The case `S₁ = ∅` (all
buyers have zero winning probability, e.g. a null stream) is not reached by the paper's algorithm
("otherwise, the algorithm would have terminated already", p.28); it returns `𝓓₀`. -/
inductive AAGRun {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : ValuationModel P n) : Set Ω → Finset (Fin n) → List (Fin n × Deal Ω) → Prop
  | none (A : Set Ω) (S : Finset (Fin n)) (l : List (Fin n))
      (hS1 : aagS1 M A S = ∅) (hl : l.Nodup) (hl0 : l.toFinset = aagS0 M A S) :
      AAGRun M A S (l.map fun j => (j, Deal.empty))
  | single (A : Set Ω) (S : Finset (Fin n)) (i : Fin n) (l : List (Fin n))
      (hS1 : aagS1 M A S = {i}) (hl : l.Nodup) (hl0 : l.toFinset = aagS0 M A S) :
      AAGRun M A S ((i, aagSingletonDeal M A i) :: l.map fun j => (j, Deal.empty))
  | step (A : Set Ω) (S : Finset (Fin n)) (i : Fin n) (l : List (Fin n))
      (out' : List (Fin n × Deal Ω))
      (hcard : 2 ≤ (aagS1 M A S).card) (hi : i ∈ aagS1 M A S)
      (hmax : ∀ j ∈ aagS1 M A S, aagRho M A S j ≤ aagRho M A S i)
      (hl : l.Nodup) (hl0 : l.toFinset = aagS0 M A S)
      (hrec : AAGRun M (A ∩ {ω | M.v i ω < aagTheta M A S i}) ((aagS1 M A S).erase i) out') :
      AAGRun M A S ((i, aagDeal M A S i) :: (out' ++ l.map fun j => (j, Deal.empty)))

end PrefDeals


