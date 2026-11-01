-- Prove2me | Definitions.Def_DRSubmodHull_IsPermFinderOutput
-- name    : DRSubmodHull_IsPermFinderOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:26:53.28024+00:00
-- url     : https://prove2.me/theorems/1f1c8316-c210-4fcd-8d35-46e3c1bb6513
-- title:
--   Algorithm 1 (Valid_Candidates) and the outputs of Algorithm 2 (Permutation_Finder)
-- statement:
--   **Algorithm 1** (p.15). For a partial permutation $\delta'$ of $\mathcal V'$, $\Delta$ is the set of $i\in\mathcal V\setminus\mathcal V'$ for which none of the following holds:
--   1. some $j\in R^+(i)\setminus(\{i\}\cup\mathcal V')$ has $u_j=u_i$;
--   2. $i\in\Psi$, $u_i<1$ and $\mathrm{ch}(i)\notin\mathcal V'$;
--   3. $i\in\Psi$, some $j\in R^-(i)\cap\mathcal V'$ has $u_j=\lfloor u_i\rfloor$, and $\mathrm{ch}(i)\notin\mathcal V'$.
--
--   **Algorithm 2** (p.19), on input $\bar z\in\mathrm{conv}(\mathcal Z(\mathcal G,u))$, starts from the empty partial permutation and for $k=1,\dots,|\mathcal V|$ appends to $\delta^{k-1}$ an element $i^*\in\Delta=\text{Valid\_Candidates}(\delta^{k-1})$ maximizing $t((\delta^{k-1},i),\bar z)_k$ over $i\in\Delta$, breaking ties arbitrarily. A permutation $\delta$ is **an output of Algorithm 2 on $\bar z$** if at every step $k$ its entry $\delta(k)$ lies in $\Delta$ for the prefix $(\delta(1),\dots,\delta(k-1))$ and has the largest $t$-value among the elements of that $\Delta$.
--
--   These permutations give the convex combinations of Proposition 5.22 and the DR inequalities that are tight at $\bar z$.
--
--   **Formalization Note** Because ties are broken arbitrarily, Algorithm 2 is encoded as a relation between $\bar z$ and $\delta$, covering every tie-break; statements about "the output" are statements about every output.
-- source:
--   Yu, Küçükyavuz, On Constrained Mixed-Integer DR-Submodular Minimization, arXiv:2211.07726v2 (preprint, 5 Sep 2023), https://arxiv.org/abs/2211.07726v2, §5, p.15 (Algorithm 1), p.19 (Algorithm 2)

import Mathlib
import Definitions.Def_DRSubmodHull_drRHS

set_option autoImplicit false

open Classical

noncomputable section

namespace DRSubmodHull

/-- **Algorithm 1 `Valid_Candidates`** (arXiv:2211.07726v2, §5, p.15). Given a partial permutation
`δ′ ∈ 𝔖(𝒱′)` (the list `L`, `𝒱′` its set of entries), the output `Δ` consists of the `i ∈ 𝒱 \ 𝒱′`
that are not removed by
* line 4: some `j ∈ R⁺(i) \ ({i} ∪ 𝒱′)` has `u_j = u_i`;
* line 8: `i ∈ Ψ`, `u_i < 1` and `ch(i) ∉ 𝒱′`;
* line 11: `i ∈ Ψ`, some `j ∈ R⁻(i) ∩ 𝒱′` has `u_j = ⌊u_i⌋`, and `ch(i) ∉ 𝒱′`. -/
def validCandidates {V : Type*} (A : V → V → Prop) (N : Set V) (u : V → ℝ) (L : List V) :
    Set V :=
  {i | i ∉ L ∧
    ¬ (∃ j : V, Relation.ReflTransGen A i j ∧ j ≠ i ∧ j ∉ L ∧ u j = u i) ∧
    ¬ (i ∈ Psi A N u ∧ u i < 1 ∧ child A i ∉ L) ∧
    ¬ (i ∈ Psi A N u ∧ (∃ j : V, Relation.ReflTransGen A j i ∧ j ∈ L ∧
        u j = (Int.floor (u i) : ℝ)) ∧ child A i ∉ L)}

/-- **`δ` is an output of Algorithm 2 `Permutation_Finder` on `z̄`** (arXiv:2211.07726v2, §5, p.19).
The algorithm starts from the empty partial permutation and, for `k = 1, …, |𝒱|`, appends to
`δ^{k−1}` an `i* ∈ Δ = Valid_Candidates(𝒢, u, δ^{k−1})` maximizing
`t((δ^{k−1}(1), …, δ^{k−1}(k − 1), i), z̄)_k` over `i ∈ Δ`, breaking ties arbitrarily.

**Formalization Note.** Because ties are broken arbitrarily, the algorithm is a relation: `δ` is
an output iff for every step (Lean index `k`, the paper's step `k + 1`) the entry `δ k` lies in
`Δ` for the prefix `(δ(1), …, δ(k))` and its `t`-value is at least that of every other element
of `Δ`. Every statement about "the output" is a statement about every output. -/
def IsPermFinderOutput {V : Type*} [Fintype V] (A : V → V → Prop) (N : Set V) (u : V → ℝ)
    (zbar : V → ℝ) (δ : Fin (Fintype.card V) ≃ V) : Prop :=
  ∀ k : Fin (Fintype.card V),
    δ k ∈ validCandidates A N u ((List.ofFn δ).take k) ∧
    ∀ i ∈ validCandidates A N u ((List.ofFn δ).take k),
      tCore A N u (Tset δ k) i zbar ≤ tCore A N u (Tset δ k) (δ k) zbar

end DRSubmodHull


