-- Prove2me | Definitions.Def_SubmodSparsify_chain
-- name    : SubmodSparsify_chain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:21:38.569575+00:00
-- url     : https://prove2.me/theorems/067c7b8c-d2e2-44a4-b852-52c991b99af3
-- title:
--   (14)–(15) — greedy minimum-ratio chain, prices $b_h$, ground state $x^*$ and shares $s_i$
-- statement:
--   Let $E$ be a finite ground set, $h_1, \dots, h_m : 2^E \to \mathbb R_{\ge 0}$ set functions and $h := \sum_{i=1}^m h_i$. The **ground-state decomposition** of the family is built from a chain $P_0 \subsetneq P_1 \subsetneq \dots \subsetneq P_L = E$:
--
--   1. $P_0$ is the inclusion-wise largest zero set of $h$ in $E$ (the union of all $C \subseteq E$ with $h(C) = 0$).
--   2. While $P_{j-1} \subsetneq E$, let
--   $$\tau_j := \min_{\emptyset \ne B \subseteq E \setminus P_{j-1}} \frac{h(P_{j-1} \cup B) - h(P_{j-1})}{|B|} \qquad (14)$$
--   and let $B_j$ be the inclusion-wise largest minimizer (the union of all minimizers); set $P_j := P_{j-1} \cup B_j$. The chain stops at the first $L$ with $P_L = E$ ($L = 0$ if $P_0 = E$).
--
--   From the chain one defines the **coordinate price vector** $b_h$, the **ground-state vector** $x^*$ and the **component shares** $s_1, \dots, s_m$:
--
--   $$b_h(v) := \begin{cases} 0, & v \in P_0,\\ \tau_j, & v \in B_j,\end{cases} \qquad x^*(v) := \begin{cases} 0, & v \in P_0,\\ 1/\tau_j, & v \in B_j,\end{cases} \qquad s_i := \sum_{j=1}^L \frac{h_i(P_j) - h_i(P_{j-1})}{\tau_j}. \qquad (15)$$
--
--   The prices depend on $h$ only; the shares split the total $\sum_i s_i = |E \setminus P_0|$ among the components. Algorithm 1 takes the shares of $2n$ such decompositions as sampling weights, and the prices define the influences of the analysis.
--
--   **Formalization Note** The ground set is a `Finset E` of any type $\alpha$ and set functions are `Finset α → ℝ`, of which only subsets of $E$ are read; vectors of $\mathbb R^E$ are functions $\alpha \to \mathbb R$ with value $0$ outside $E$. "Largest" is the union of all zero sets (resp. minimizers); for nonnegative monotone submodular families the union is itself a zero set (resp. minimizer), which is not assumed in the definition. The minimum $\tau$ is an infimum over a finite nonempty type, hence attained, so the chain grows at every step and reaches $E$ after $L \le |E|$ steps for every $h$; `chainLength` is the first $L$ with $P_L = E$. `chain h E j` is $P_j$, and $\tau_j$, $B_j$ are `tau h E (chain h E (j-1))` and `chain h E j \ chain h E (j-1)`. `finMax C b` is the maximum of $b$ over $C$, zero over the empty set (the paper's convention in (19) and (25)).
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6…), §4.1, (14)–(15), p.19 (PDF p.21)

import Mathlib

namespace SubmodSparsify

/-!
# The greedy minimum-ratio chain, prices, ground state and shares (§4.1, (14)–(15), p.19)

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), §4.1, p.19.

"Let E be a finite ground set, and let h1, . . . , hm : 2^E → R≥0 be nonnegative monotone
submodular functions satisfying hi(∅) = 0. Write h := Σ_{i=1}^m hi for their sum […]
1. Let P0 ⊆ E be the inclusion-wise largest zero set of h, i.e., the largest subset with
h(P0) = 0. […]
2. For j = 1, 2, . . . , L, while Pj−1 ⊊ E, choose a nonempty subset Bj ⊆ E \ Pj−1 that
minimizes the average marginal increment
τj := min_{∅≠B⊆E\Pj−1} (h(Pj−1 ∪ B) − h(Pj−1))/|B|, (14)
breaking ties by taking the inclusion-wise largest minimizer, and set Pj := Pj−1 ∪ Bj. Repeat
until PL = E (if P0 = E, the chain has L = 0 blocks).
From this chain, we define the coordinate price vector bh […], the ground-state vector x∗ […],
and the component shares s1, . . . , sm […] by
bh(v) := 0 (v ∈ P0), τj (v ∈ Bj),  x∗(v) := 0 (v ∈ P0), 1/τj (v ∈ Bj),
si := Σ_{j=1}^L (hi(Pj) − hi(Pj−1))/τj (i ∈ [m]), (15)
where si = 0 if P0 = E."

**Formalization Note.**
* The ground set is a `Finset E` of an arbitrary type `α`; set functions are
  `Finset α → ℝ` of which only the values on subsets of `E` are read; vectors of `ℝ^E` are
  functions `α → ℝ` (value `0` outside `E`).
* "Inclusion-wise largest zero set / minimizer" is the union (`Finset.sup id`) of all zero sets
  of `h` in `E` (resp. of all minimizers of (14)). For nonnegative submodular `h` the union is
  itself a zero set (p.19) resp. a minimizer (proof of Lemma 4.2, p.20), so this is the paper's
  set; no such property is assumed.
* The minimum `τ` in (14) is the infimum over the finite, nonempty (while `P ⊊ E`) subtype of
  nonempty `B ⊆ E \ P`, hence attained. Consequently every step of the chain adds a nonempty
  block, the chain reaches `E` after `L ≤ |E|` steps for every `h`, and afterwards stays at `E`
  (`nextPrefix h E E = E`). `chainLength` is the first index `L` with `P_L = E`.
* Indices: `chain h E j` is `P_j`; the paper's `B_j` and `τ_j` (`1 ≤ j ≤ L`) are
  `chain h E j \ chain h E (j-1)` and `tau h E (chain h E (j-1))`.
-/

variable {α : Type} [DecidableEq α]

/-- The maximum of `b` over a finite set `C`, with the paper's convention that the maximum over
the empty set is zero ((19), p.20; (25), p.24). -/
noncomputable def finMax {β : Type} (C : Finset β) (b : β → ℝ) : ℝ :=
  if hC : C.Nonempty then C.sup' hC b else 0

/-- The sum `h := Σᵢ hᵢ` of a finite family of set functions. -/
def sumFn {ι : Type} [Fintype ι] (hs : ι → Finset α → ℝ) (C : Finset α) : ℝ :=
  ∑ i, hs i C

/-- `P₀`: the inclusion-wise largest zero set of `h` in `E` (the union of all `C ⊆ E` with
`h C = 0`). -/
noncomputable def zeroSet (h : Finset α → ℝ) (E : Finset α) : Finset α := by
  classical exact (E.powerset.filter (fun C => h C = 0)).sup id

/-- The average marginal increment `(h(P ∪ B) − h(P))/|B|` of (14). -/
noncomputable def ratio (h : Finset α → ℝ) (P B : Finset α) : ℝ :=
  (h (P ∪ B) - h P) / (B.card : ℝ)

/-- `τ` of (14) at the current prefix `P`: the minimum of `ratio h P B` over nonempty
`B ⊆ E \ P` (junk value `0` when `P ⊇ E`, where the chain has stopped). -/
noncomputable def tau (h : Finset α → ℝ) (E P : Finset α) : ℝ :=
  ⨅ B : {B : Finset α // B ⊆ E \ P ∧ B.Nonempty}, ratio h P B.1

/-- The next block `B_j`: the inclusion-wise largest minimizer of (14), i.e. the union of all
nonempty `B ⊆ E \ P` with `ratio h P B = tau h E P` (empty when `P ⊇ E`). -/
noncomputable def nextBlock (h : Finset α → ℝ) (E P : Finset α) : Finset α := by
  classical exact
    ((E \ P).powerset.filter (fun B => B.Nonempty ∧ ratio h P B = tau h E P)).sup id

/-- One step of the chain: `P_j := P_{j−1} ∪ B_j`. -/
noncomputable def nextPrefix (h : Finset α → ℝ) (E P : Finset α) : Finset α :=
  P ∪ nextBlock h E P

/-- The greedy minimum-ratio chain: `chain h E j = P_j`, starting from `P₀ = zeroSet h E`. -/
noncomputable def chain (h : Finset α → ℝ) (E : Finset α) (j : ℕ) : Finset α :=
  (nextPrefix h E)^[j] (zeroSet h E)

/-- The number `L` of blocks: the first index with `P_L = E`. -/
noncomputable def chainLength (h : Finset α → ℝ) (E : Finset α) : ℕ :=
  sInf {j : ℕ | chain h E j = E}

/-- The coordinate price vector `b_h` of (15): `0` on `P₀`, `τ_j` on `B_j` (and `0` outside
`E`). -/
noncomputable def price (h : Finset α → ℝ) (E : Finset α) (v : α) : ℝ := by
  classical exact
    ∑ j ∈ Finset.range (chainLength h E),
      if v ∈ chain h E (j + 1) \ chain h E j then tau h E (chain h E j) else 0

/-- The ground-state vector `x*` of (15): `0` on `P₀`, `1/τ_j` on `B_j` (and `0` outside
`E`). -/
noncomputable def groundState (h : Finset α → ℝ) (E : Finset α) (v : α) : ℝ := by
  classical exact
    ∑ j ∈ Finset.range (chainLength h E),
      if v ∈ chain h E (j + 1) \ chain h E j then 1 / tau h E (chain h E j) else 0

/-- The component shares of (15): `s_i = Σ_{j=1}^L (h_i(P_j) − h_i(P_{j−1}))/τ_j`, for the
family `hs` with sum `h = Σᵢ hs i` (so `s_i = 0` when `P₀ = E`, i.e. `L = 0`). -/
noncomputable def share {ι : Type} [Fintype ι] (hs : ι → Finset α → ℝ) (E : Finset α)
    (i : ι) : ℝ :=
  ∑ j ∈ Finset.range (chainLength (sumFn hs) E),
    (hs i (chain (sumFn hs) E (j + 1)) - hs i (chain (sumFn hs) E j)) /
      tau (sumFn hs) E (chain (sumFn hs) E j)

end SubmodSparsify


