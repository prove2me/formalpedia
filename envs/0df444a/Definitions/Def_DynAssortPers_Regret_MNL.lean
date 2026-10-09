-- Prove2me | Definitions.Def_DynAssortPers_Regret_MNL
-- name    : DynAssortPers_Regret_MNL
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:14:59.144284+00:00
-- url     : https://prove2.me/theorems/47508733-1a5f-44b7-8d18-73c9e2581787
-- title:
--   Sec. 2 and Sec. 4, pp. 5, 21, 23 — MNL choice probabilities $p_j(S;\theta)$, revenue $F(S;w,\theta)$, optimal sets $S^\star(w,\theta;K)$ and the gap $\delta(w,\theta;K)$
-- statement:
--   Fix $n$ items, a parameter vector $\theta\in\mathbb R^n$, a revenue vector $w\in\mathbb R^n$ and a cardinality bound $K$. For an assortment $S\subseteq\{1,\dots,n\}$ this module defines:
--
--   1. the **MNL choice probability**
--   $$p_j(S;\theta)=\frac{e^{\theta_j}}{1+\sum_{j'\in S}e^{\theta_{j'}}}\quad(j\in S),\qquad p_j(S;\theta)=0\quad(j\notin S);$$
--   2. the **choice law** of a customer offered $S$: the no-purchase option ("item 0") has probability $1/(1+\sum_{j\in S}e^{\theta_j})$, and item $j$ has probability $p_j(S;\theta)$ — the weights $1$, $0$, $e^{\theta_j}$ of the problem statement, normalized;
--   3. the **expected revenue**
--   $$F(S;w,\theta)=\sum_{j\in S}p_j(S;\theta)\,w_j=\frac{\sum_{j\in S}w_je^{\theta_j}}{1+\sum_{j\in S}e^{\theta_j}},$$
--   written with the published MNL objective with preference weights $e^{\theta_j}$ and no-purchase weight $1$;
--   4. the set of **optimal assortments** $S^\star(w,\theta;K)=\operatorname{argmax}_{|S|\le K}F(S;w,\theta)$, as the predicate "$|S|\le K$ and $F(S';w,\theta)\le F(S;w,\theta)$ for every $|S'|\le K$";
--   5. the **optimal revenue** $\max_{|S|\le K}F(S;w,\theta)$, a maximum over the finite nonempty family of assortments of size at most $K$ (it contains $\emptyset$);
--   6. the **gap condition** "$\delta(w,\theta;K)\ge d$" for the revenue gap
--   $$\delta(w,\theta;K)=\max_{|S|\le K}F(S;w,\theta)-\max_{S\notin S^\star(w,\theta;K),\,|S|\le K}F(S;w,\theta),$$
--   stated as: every assortment $S$ with $|S|\le K$ that is not optimal satisfies $F(S;w,\theta)\le \max_{|S'|\le K}F(S';w,\theta)-d$;
--   7. the sup norm $\|w\|_\infty=\max_j|w_j|$ and the Euclidean distance $\|\theta-\theta'\|_2$.
--
--   These are the single-type objects of the paper: each customer type $i$ has its own MNL model with parameter row $\Theta^\star_i$ and revenue row $W_i$.
--
--   **Formalization Note** Items are `Fin n`, 0-based: Lean item $j$ is the paper's item $j+1$, and the no-purchase option is `none`. The gap $\delta$ is not defined as a number, because the second maximum ranges over an empty set when every feasible assortment is optimal; the gap condition is the hypothesis form, and it holds for every $d$ in that case. $\|\theta-\theta'\|_2$ is $\sqrt{\sum_j(\theta_j-\theta'_j)^2}$.
-- source:
--   Kallus, Udell, Dynamic Assortment Personalization in High Dimensions, arXiv:1610.05604 (PDF sha256 2b010481…216a), Sec. 2, p. 5 (choice weights); Sec. 4, p. 21 (p_j, F, S⋆); Sec. 4.2, p. 23 (δ)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective

namespace DynAssortPers.Regret

/-- The MNL choice probability of Kallus–Udell, Sec. 4, p. 21:
`p_j(S; θ) = e^{θ_j} / (1 + ∑_{j' ∈ S} e^{θ_{j'}})` for `j ∈ S`, and `0` for an item not offered
(Sec. 2, p. 5: `weight(j) = 0` for `j ∉ S`). Items are `Fin n`, 0-based. -/
noncomputable def choiceProb {n : ℕ} (θ : Fin n → ℝ) (S : Finset (Fin n)) (j : Fin n) : ℝ :=
  if j ∈ S then Real.exp (θ j) / (1 + ∑ j' ∈ S, Real.exp (θ j')) else 0

/-- The law of the customer's choice from the offered set `S` (Sec. 2, p. 5, step 3): the
no-purchase option ("item 0", here `none`) has probability `1 / (1 + ∑_{j ∈ S} e^{θ_j})`, and item
`some j` has probability `p_j(S; θ)`. -/
noncomputable def choiceLaw {n : ℕ} (θ : Fin n → ℝ) (S : Finset (Fin n)) : Option (Fin n) → ℝ
  | none => 1 / (1 + ∑ j' ∈ S, Real.exp (θ j'))
  | some j => choiceProb θ S j

/-- The expected revenue `F(S; w, θ) = ∑_{j ∈ S} p_j(S; θ) w_j` of Sec. 4, p. 21, written with the
published MNL objective: `(∑_{j ∈ S} w_j e^{θ_j}) / (∑_{j ∈ S} e^{θ_j} + 1)`. -/
noncomputable def revenue {n : ℕ} (S : Finset (Fin n)) (w θ : Fin n → ℝ) : ℝ :=
  ChoiceCDLP.MNL.mnlObjective (fun j => Real.exp (θ j)) w 1 S

/-- `S ∈ S⋆(w, θ; K) = argmax_{|S| ≤ K} F(S; w, θ)` (Sec. 4, p. 21). -/
def IsOptimal {n : ℕ} (w θ : Fin n → ℝ) (K : ℕ) (S : Finset (Fin n)) : Prop :=
  S.card ≤ K ∧ ∀ S' : Finset (Fin n), S'.card ≤ K → revenue S' w θ ≤ revenue S w θ

/-- The finite family `{S ⊆ {1, …, n} : |S| ≤ K}` of feasible assortments. -/
def feasibleSets (n K : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powerset.filter (fun S => S.card ≤ K)

/-- The family of feasible assortments contains `∅`, so it is nonempty. -/
theorem feasibleSets_nonempty (n K : ℕ) : (feasibleSets n K).Nonempty :=
  ⟨∅, by simp [feasibleSets]⟩

/-- The optimal revenue `max_{|S| ≤ K} F(S; w, θ)` (the first term of `δ(w, θ; K)`, p. 23). -/
noncomputable def optVal {n : ℕ} (w θ : Fin n → ℝ) (K : ℕ) : ℝ :=
  (feasibleSets n K).sup' (feasibleSets_nonempty n K) (fun S => revenue S w θ)

/-- "`δ(w, θ; K) ≥ d`" for the revenue gap of p. 23,
`δ(w, θ; K) = max_{|S| ≤ K} F(S; w, θ) − max_{S ∉ S⋆(w, θ; K), |S| ≤ K} F(S; w, θ)`:
every feasible assortment that is not optimal earns at most the optimum minus `d`. When every
feasible assortment is optimal the condition holds for every `d`. -/
def HasGap {n : ℕ} (w θ : Fin n → ℝ) (K : ℕ) (d : ℝ) : Prop :=
  ∀ S : Finset (Fin n), S.card ≤ K → ¬ IsOptimal w θ K S → revenue S w θ ≤ optVal w θ K - d

/-- The sup norm `‖w‖_∞ = max_j |w_j|` of a vector. -/
noncomputable def supNorm {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  ⨆ j : Fin n, |w j|

/-- The Euclidean distance `‖θ − θ'‖₂ = (∑_j (θ_j − θ'_j)²)^{1/2}`. -/
noncomputable def euclidDist {n : ℕ} (θ θ' : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ j : Fin n, (θ j - θ' j) ^ 2)

end DynAssortPers.Regret


