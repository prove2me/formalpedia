-- Prove2me | Definitions.Def_SubmodSparsify_Supplement_cappedShare
-- name    : SubmodSparsify_Supplement_cappedShare
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:07:58.052199+00:00
-- url     : https://prove2.me/theorems/70cfe85a-e99a-437c-b5cb-80a93fccf2ff
-- title:
--   Capped parametric decomposition (29) and its shares (32)
-- statement:
--   Let $E$ be a finite ground set, $h_1,\dots,h_m : 2^E \to \mathbb R_{\ge 0}$ normalized monotone submodular functions with sum $h = \sum_i h_i$, and $K \ge 1$ an integer. Put
--
--   $$\kappa(C) = \min\{K,\ |E \setminus C|\}, \qquad P(t) = \operatorname*{argmin}_{C \subseteq E}\ \bigl\{h(C) + t\,\kappa(C)\bigr\} \quad (t \ge 0),$$
--
--   where ties are broken by taking the inclusion-wise largest minimizer (here: the union of all minimizers). The distinct sets attained by $P(t)$, $t \ge 0$, are listed by increasing cardinality as $P_0, P_1, \dots, P_L$; when $h \not\equiv 0$ they form the chain $P_0 \subsetneq \dots \subsetneq P_L = E$ of Lemma 5.4. With
--
--   $$\tau_j = \frac{h(P_j) - h(P_{j-1})}{\kappa(P_{j-1}) - \kappa(P_j)}, \qquad s_i = \sum_{j=1}^{L} \frac{h_i(P_j) - h_i(P_{j-1})}{\tau_j},$$
--
--   `cappedShare hs K E i` is the share $s_i$ of (32). When $h \equiv 0$ on $2^E$ (in particular when $E = \emptyset$) the only attained set is $E$ and all shares are $0$, as in Lemma 5.4 and Algorithm 4.
--
--   These capped shares give Algorithm 3's inside-terminal scores with total at most $K = 2k-1$; with $K \ge |E|$ the cap is inactive and they are the ordinary shares used for the outside-block scores.
--
--   **Formalization Note** Set functions are `Finset α → ℝ`, of which only values on subsets of `E` are read. The minimizer union is the paper's $P(t)$ because minimizers of a submodular objective are closed under union; no such property is assumed in the definition. Outside the paper's hypotheses (if the attained sets are not a chain) the value is junk.
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6793d37e5008919a4795e2e18da7fa5049f06ad4d1b929ac6d7fbc634), (29), p.29; Claim 5.2, p.29; Algorithm 4, p.30; Lemma 5.4, (31)–(32), p.31

import Mathlib
import Definitions.Def_SubmodSparsify_chain

namespace SubmodSparsify.Supplement

/-!
# The capped parametric decomposition and its shares ((29), Claim 5.2, Lemma 5.4 (31)–(32))

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), (29) p.29, Claim 5.2 p.29,
Algorithm 4 p.30, Lemma 5.4 p.31.

"Let h1, . . . , hm : 2^E → R≥0 be normalized, monotone submodular functions, write h = Σᵢ hᵢ,
and let K ≥ 1. Put κ(C) = min{K, |E \ C|}, P(t) = argmin_{C⊆E} {h(C) + tκ(C)} (t ≥ 0). (29)
Ties are broken by taking the inclusion-wise largest minimizer." (p.29) "If h is not identically
zero, the distinct sets attained by P(t) form a chain P0 ⊊ P1 ⊊ · · · ⊊ PL = E. […]
τj = (h(Pj) − h(Pj−1))/(κ(Pj−1) − κ(Pj)) […] The shares si = Σ_{j=1}^L (hi(Pj) − hi(Pj−1))/τj
(32) […] For h ≡ 0, all shares are zero and P(t) = E." (p.31) Algorithm 4 returns zero shares
when `E = ∅`.

**Formalization Note.**
* The ground set is a `Finset E` of an arbitrary type `α`; set functions are `Finset α → ℝ`, of
  which only the values on subsets of `E` are read. The cap `K` is a natural number.
* "Inclusion-wise largest minimizer" is the union (`Finset.sup id`) of all minimizers of
  `h(C) + tκ(C)` over `C ⊆ E` (the minimum over the finite nonempty family `2^E` is attained).
  For submodular `h` the minimizers are closed under union (§5.4, p.39), so this is the paper's
  `P(t)`; no such property is assumed.
* The distinct sets attained by `P(t)`, `t ≥ 0`, are collected as a finite set and listed in
  order of increasing cardinality. For normalized monotone submodular `hᵢ` they form the chain
  `P₀ ⊊ ⋯ ⊊ P_L = E` of Lemma 5.4, so the list is `(P₀, …, P_L)`; `cappedShare` is (32) summed
  over consecutive pairs. When `h ≡ 0` on `2^E` (in particular when `E = ∅`) the only attained
  set is `E`, the list is `(E)` and every share is `0`, as in Lemma 5.4 and Algorithm 4.
* With `K ≥ |E|` the cap is inactive (`κ(C) = |E \ C|`), the case used for the outside-block
  shares `t^{(X)}` of (37).
-/

variable {α : Type} [DecidableEq α]

/-- `κ(C) = min{K, |E \ C|}` of (29). -/
noncomputable def kappa (K : ℕ) (E C : Finset α) : ℝ :=
  min (K : ℝ) ((E \ C).card : ℝ)

/-- The capped objective `h(C) + t κ(C)` of (29). -/
noncomputable def cappedObj (h : Finset α → ℝ) (K : ℕ) (E : Finset α) (t : ℝ) (C : Finset α) :
    ℝ :=
  h C + t * kappa K E C

/-- `P(t)` of (29): the inclusion-wise largest minimizer of `h(C) + tκ(C)` over `C ⊆ E` (the
union of all minimizers). -/
noncomputable def cappedMinimizer (h : Finset α → ℝ) (K : ℕ) (E : Finset α) (t : ℝ) :
    Finset α := by
  classical exact
    (E.powerset.filter (fun C => ∀ D ∈ E.powerset,
      cappedObj h K E t C ≤ cappedObj h K E t D)).sup id

/-- The distinct sets attained by `P(t)` for `t ≥ 0`. -/
noncomputable def cappedChainSets (h : Finset α → ℝ) (K : ℕ) (E : Finset α) :
    Finset (Finset α) := by
  classical exact
    E.powerset.filter (fun C => ∃ t : ℝ, 0 ≤ t ∧ cappedMinimizer h K E t = C)

/-- The attained sets listed by increasing cardinality: `(P₀, P₁, …, P_L)` when they form a
chain. -/
noncomputable def cappedChain (h : Finset α → ℝ) (K : ℕ) (E : Finset α) : List (Finset α) :=
  (cappedChainSets h K E).toList.mergeSort (fun X Y => decide (X.card ≤ Y.card))

/-- The capped shares (32) of the family `hs` with sum `h = Σᵢ hs i`:
`s_i = Σ_{j=1}^L (h_i(P_j) − h_i(P_{j−1}))/τ_j` with
`τ_j = (h(P_j) − h(P_{j−1}))/(κ(P_{j−1}) − κ(P_j))`. -/
noncomputable def cappedShare {ι : Type} [Fintype ι] (hs : ι → Finset α → ℝ) (K : ℕ)
    (E : Finset α) (i : ι) : ℝ :=
  let l := cappedChain (sumFn hs) K E
  ((l.zip l.tail).map (fun p => (hs i p.2 - hs i p.1) /
    ((sumFn hs p.2 - sumFn hs p.1) / (kappa K E p.1 - kappa K E p.2)))).sum

end SubmodSparsify.Supplement


