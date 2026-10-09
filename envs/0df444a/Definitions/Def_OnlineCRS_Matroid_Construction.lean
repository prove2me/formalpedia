-- Prove2me | Definitions.Def_OnlineCRS_Matroid_Construction
-- name    : OnlineCRS_Matroid_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T19:23:01.294378+00:00
-- url     : https://prove2.me/theorems/9994a03e-6715-4d4b-b3e0-344c3228d8d4
-- title:
--   The span probabilities, nested sets and chain family
-- statement:
--   Given a matroid $M$, an activation vector $x$, and a threshold $b$, set $S_0=\varnothing$ and
--   $$S_{i+1}=\left\{e\in N:\Pr\left[e\in\operatorname{span}((R(x)\cup S_i)\setminus\{e\})\right]>b\right\},\qquad S=S_{|N|}.$$
--   The probabilities are finite sums over all possible active sets. Separately, a descending chain $N=N_0\supseteq\cdots\supseteq N_\ell=\varnothing$ defines the family of sets $I$ for which $I\cap(N_i\setminus N_{i+1})$ is independent in $(M/N_{i+1})|N_i$ for every $i<\ell$. The definition also records the probability that $e$ lies in $\operatorname{span}(R(x)\cup S)$, without deleting $e$.
--
--   These are the paper's two distinct span events: the deletion event constructs the chain, while the non-deletion event appears in Lemma 2.4. Keeping them separate prevents a change to that lemma's claim.
-- source:
--   arXiv:1508.00142v2, §2.1, p. 10; §2.1.1, pp. 11–12

import Mathlib
import Definitions.Def_OnlineCRS_Matroid_Basics
import Definitions.Def_OnlineCRS_Matroid_Polytope

open scoped Matroid

namespace OnlineCRS.Matroid

open Classical

/-- §2.1.1, p. 11: probability that `e` is spanned by `(R(x) ∪ T) \ {e}`. -/
noncomputable def spanProb {α : Type} [Fintype α] [DecidableEq α]
    (M : Matroid α) (x : α → ℝ) (T : Finset α) (e : α) : ℝ :=
  ∑ A : Finset α,
    activeProb x A * if e ∈ M.closure (((A ∪ T : Finset α) : Set α) \ {e}) then 1 else 0

/-- §2.1.1, p. 11: the simultaneous sequence `S₀ = ∅`, `Sᵢ₊₁ = {e : Pr[e ∈ span((R(x) ∪ Sᵢ) \ {e})] > b}`. -/
noncomputable def Sseq {α : Type} [Fintype α] [DecidableEq α]
    (M : Matroid α) (x : α → ℝ) (b : ℝ) : ℕ → Finset α
  | 0 => ∅
  | i + 1 => Finset.univ.filter fun e => b < spanProb M x (Sseq M x b i) e

/-- §2.1.1, p. 11: `S = S_|N|`, the first set in the constructed chain. -/
noncomputable def Sfin {α : Type} [Fintype α] [DecidableEq α]
    (M : Matroid α) (x : α → ℝ) (b : ℝ) : Finset α :=
  Sseq M x b (Fintype.card α)

/-- §2.1, p. 10: the family associated with a descending chain of matroid minors. -/
noncomputable def chainFamily {α : Type} [Fintype α] [DecidableEq α]
    (M : Matroid α) (Nch : ℕ → Finset α) (ℓ : ℕ) : Finset (Finset α) :=
  Finset.univ.filter fun I =>
    ∀ i < ℓ,
      ((M ／ (Nch (i+1) : Set α)) ↾ (Nch i : Set α)).Indep
        (((I ∩ (Nch i \ Nch (i+1)) : Finset α)) : Set α)

/-- Lemma 2.4, p. 11: the probability that `e` lies in the span of `R(x) ∪ S`. -/
noncomputable def spanWithProb {α : Type} [Fintype α] [DecidableEq α]
    (M : Matroid α) (x : α → ℝ) (S : Finset α) (e : α) : ℝ :=
  ∑ A : Finset α,
    activeProb x A * if e ∈ M.closure ((A ∪ S : Finset α) : Set α) then 1 else 0

end OnlineCRS.Matroid


