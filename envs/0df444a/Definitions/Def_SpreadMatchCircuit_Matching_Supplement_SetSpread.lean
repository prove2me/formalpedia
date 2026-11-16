-- Prove2me | Definitions.Def_SpreadMatchCircuit_Matching_Supplement_SetSpread
-- name    : SpreadMatchCircuit_Matching_Supplement_SetSpread
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:32:40.65388+00:00
-- url     : https://prove2.me/theorems/83ef31c1-e509-40db-afd7-3867f0066c11
-- title:
--   Spread random vertex sets and the independent-edge random graph
-- statement:
--   Let $Z$ be a random subset of $[n]$ with law $\mu$, where $\mu$ assigns arbitrary nonnegative weights summing to $1$ to the subsets of $[n]$. Write $\mathcal Z$ for the **support** of $Z$, the subsets of positive probability.
--
--   1. For a real number $r$, $Z$ is **$r$-spread** if for every set of vertices $A\subseteq[n]$,
--   $$\Pr[A\subseteq Z]\le r^{-|A|}.$$
--   For $A=\emptyset$ this reads $1\le 1$.
--   2. $Z$ has **size at most $t$** if every $z\in\mathcal Z$ has $|z|\le t$.
--   3. For $p\in[0,1]$, the **random graph** $X_0$ on $[n]$ includes each of the $N=\binom n2$ possible edges independently with probability $p$. The probability of an event $\mathcal A$ is
--   $$\Pr_{X_0}[\mathcal A]=\sum_{x\in\mathcal A}p^{|x|}(1-p)^{N-|x|},$$
--   the sum ranging over the graphs $x$ on $[n]$ in $\mathcal A$.
--
--   These are the objects of the Spread Clique Lemma (Lemma 4). Set spreadness is distinct from the spreadness of random matchings used elsewhere in the mission.
--
--   **Formalization Note** The law $\mu$ is a `PMF` on `Finset (Fin n)`, and probabilities and supports use the published `lawProb` and `lawSupport`. The random graph is given by its explicit product weights, not as a `PMF`. In Lean $r^{-|A|}$ is written $(r^{|A|})^{-1}$; for $r=0$ and $A\neq\emptyset$ Lean's convention $0^{-1}=0$ forces $\Pr[A\subseteq Z]=0$.
-- source:
--   Anup Rao, STOC 2027 submission #299 (October 2026), p. 3 (definition of an r-spread random set and its support), p. 4 (Lemma 4: X_0 includes each edge independently with probability p)

import Mathlib
import Definitions.Def_SpreadMatchCircuit_Matching_Graphs
import Definitions.Def_SpreadMatchCircuit_Matching_SpreadLaw

namespace SpreadMatchCircuit.Matching.Supplement

open Finset

variable {n : ℕ}

/-- The random vertex set `Z ∼ μ` is `r`-spread: `p(A ⊆ Z) ≤ r^{-|A|}` for every set of
vertices `A` (the empty set included, where the bound reads `p(∅ ⊆ Z) = 1 ≤ 1`). -/
def IsSetSpread (μ : PMF (Finset (Fin n))) (r : ℝ) : Prop :=
  ∀ A : Finset (Fin n), lawProb μ (fun z => A ⊆ z) ≤ (r ^ A.card)⁻¹

/-- The random vertex set `Z ∼ μ` has size at most `t`: every set in the support `𝒵` of `μ`
has at most `t` elements. -/
def IsBoundedSetLaw (μ : PMF (Finset (Fin n))) (t : ℝ) : Prop :=
  ∀ z ∈ lawSupport μ, (z.card : ℝ) ≤ t

open scoped Classical in
/-- The probability of the event `A` when `X₀` is the random graph on `[n]` that contains each of
the `n(n-1)/2` possible edges independently with probability `p`: a graph `x` has weight
`p^{|x|} (1-p)^{N-|x|}`, where `N` is the number of possible edges. -/
noncomputable def randomGraphProb (n : ℕ) (p : ℝ) (A : Finset (Edge n) → Prop) : ℝ :=
  ∑ x ∈ univ.filter A, p ^ x.card * (1 - p) ^ (Fintype.card (Edge n) - x.card)

end SpreadMatchCircuit.Matching.Supplement


