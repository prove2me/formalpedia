-- Prove2me | Definitions.Def_MultiCorrectPAC_Demo_Dimensions
-- name    : MultiCorrectPAC_Demo_Dimensions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:44:46.797399+00:00
-- url     : https://prove2.me/theorems/37a3d2be-57a9-450b-8b6d-a0a05451cfd5
-- title:
--   The generalized Natarajan, joint DS, disjoint-neighbor and packed dimensions $d^\cap_{\mathrm N}$, $d^\cap_{\mathrm{DS}}$, $d_{\mathrm{pair}}$, $d^\cap_{\mathrm{pack},\rho}$
-- statement:
--   A finite family of sets has **empty intersection** if no label lies in all members; it is a **minimal empty-intersection family** if moreover every proper subfamily has nonempty intersection. Let $S=(x_1,\dots,x_n)$ and, for a pattern $v$, let $v_{-i}$ delete the $i$-th coordinate.
--
--   * $S$ (distinct inputs) is **product-shattered** if there are finite nonempty families $\mathcal A_1,\dots,\mathcal A_n\subseteq\mathcal A$ with $\bigcap_{A\in\mathcal A_i}A=\emptyset$ for each $i$ and $\mathcal A_1\times\dots\times\mathcal A_n\subseteq\mathcal H|_S$; $d^\cap_{\mathrm N}(\mathcal H)$ is the largest size of a product-shattered sequence (Definition 3).
--   * A finite nonempty $V\subseteq\mathcal H|_S$ is a **DS witness** if $\bigcap_{w\in e_{i,v_{-i}}}w_i=\emptyset$ for all $v\in V$, $i\in[n]$, where $e_{i,u}=\{w\in V:w_{-i}=u\}$; it is a **disjoint-neighbor witness** if every $v\in V$ and $i$ have $w\in V$ with $w_{-i}=v_{-i}$ and $w_i\cap v_i=\emptyset$ (Definitions 4, 5).
--   * A **$\rho$-packed witness** is a nonempty list $v^1,\dots,v^M\in\mathcal H|_S$ (repetitions allowed) with, for every direction $i$, pairwise disjoint **conflict blocks** $B\subseteq[M]$, $2\le|B|\le\ell+1$, $v^a_j=v^b_j$ for $a,b\in B$, $j\ne i$, $\bigcap_{a\in B}v^a_i=\emptyset$, covering $|\bigcup_{B\in\mathcal B_i}B|\ge\rho M$ (Definition 7).
--
--   $d^\cap_{\mathrm{DS}}$, $d_{\mathrm{pair}}$, $d^\cap_{\mathrm{pack},\rho}$ are the largest $n$ for which some sequence of $n$ distinct inputs carries such a witness; every dimension is $0$ if no witness of positive size exists and $\infty$ if witnesses of every size exist:
--   $$d(\mathcal H)=\sup\{n:\text{some }S\in\mathcal X^n\text{ of distinct inputs carries a witness}\}\in\mathbb N_0\cup\{\infty\}.$$
--
--   **Formalization Note** Values in `ℕ∞` as `⨆ n (_ : …), (n : ℕ∞)`. Distinctness is `Function.Injective S`; indices are `Fin n`, `Fin M`. The coverage parameter `ρ : ℝ` is an argument of `packDim ℓ ρ`; the paper's $\gamma$ of (9) and its comparison parameters $\rho\in(0,1]$ are both instances. The condition $\mathcal A_i\subseteq\mathcal A$ is not repeated in `ProductShattered`: for a class it follows from $\mathcal A_1\times\dots\times\mathcal A_n\subseteq\mathcal H|_S$ with nonempty families.
-- source:
--   Hanneke, Mansouri, Pour, Shaeiri, Wang, PAC Learning with Multiple Correct Answers, STOC 2027 submission (manuscript sha256 2844bd34…), pp. 28–30 (PDF 30–32), (8), Definitions 3, 4, 5, 7

import Mathlib
import Definitions.Def_MultiCorrectPAC_Demo_Hypotheses

namespace MultiCorrectPAC.Demo

/-! Hanneke, Mansouri, Pour, Shaeiri, Wang, *PAC Learning with Multiple Correct Answers*,
§5.4 (printed pp. 28–30, PDF 30–32): Definitions 3, 4, 5, 7 and minimal empty-intersection
families (p. 30). Sequences `S = (x₁, …, xₙ)` are `S : Fin n → X`; "distinct inputs" is
`Function.Injective S`. Each dimension is the `ℕ∞`-valued supremum of the sizes `n` of
sequences of distinct inputs carrying a finite witness (`0` if there is none of positive size,
`⊤` if there are witnesses of every size). -/

/-- A family of sets has an empty intersection: every label is missing from some member. -/
def EmptyInter {Y : Type*} (𝒜 : Set (Finset Y)) : Prop :=
  ∀ y, ∃ A ∈ 𝒜, y ∉ A

/-- A minimal empty-intersection family (p. 30): a finite family with empty intersection every
proper subfamily of which has a nonempty intersection. -/
def IsMinimalEmptyInter {Y : Type*} (𝒜 : Finset (Finset Y)) : Prop :=
  EmptyInter (𝒜 : Set (Finset Y)) ∧ ∀ 𝒜' ⊂ 𝒜, ¬ EmptyInter (𝒜' : Set (Finset Y))

/-- `S` is product-shattered by `H` (Definition 3): there are finite nonempty families
`𝒜₁, …, 𝒜ₙ`, each with empty intersection, with `𝒜₁ × ⋯ × 𝒜ₙ ⊆ H|S`. -/
def ProductShattered {X Y : Type*} (H : Set (Hyp X Y)) {n : ℕ} (S : Fin n → X) : Prop :=
  ∃ 𝒜 : Fin n → Finset (Finset Y), (∀ i, (𝒜 i).Nonempty) ∧
    (∀ i, EmptyInter (𝒜 i : Set (Finset Y))) ∧
    ∀ v : Fin n → Finset Y, (∀ i, v i ∈ 𝒜 i) → v ∈ patterns H S

/-- The generalized Natarajan dimension `d∩_N(H)` (Definition 3). -/
noncomputable def natDim {X Y : Type*} (H : Set (Hyp X Y)) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : ∃ S : Fin n → X, Function.Injective S ∧ ProductShattered H S), (n : ℕ∞)

/-- `V ⊆ H|S` is a DS witness (Definition 4): `V` is finite and nonempty, and every hyperedge
`e_{i, v₋ᵢ} = {w ∈ V : w₋ᵢ = v₋ᵢ}` of its one-inclusion hypergraph (8) has empty intersection
in its direction `i`. -/
def IsDSWitness {X Y : Type*} (H : Set (Hyp X Y)) {n : ℕ} (S : Fin n → X)
    (V : Finset (Fin n → Finset Y)) : Prop :=
  V.Nonempty ∧ (↑V ⊆ patterns H S) ∧
    ∀ v ∈ V, ∀ i : Fin n, ∀ y : Y, ∃ w ∈ V, (∀ j, j ≠ i → w j = v j) ∧ y ∉ w i

/-- The joint DS dimension `d∩_DS(H)` (Definition 4). -/
noncomputable def dsDim {X Y : Type*} (H : Set (Hyp X Y)) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : ∃ (S : Fin n → X) (V : Finset (Fin n → Finset Y)),
    Function.Injective S ∧ IsDSWitness H S V), (n : ℕ∞)

/-- `V ⊆ H|S` is a disjoint-neighbor witness (Definition 5): finite, nonempty, and every
`v ∈ V` has in every direction `i` a `w ∈ V` with `w₋ᵢ = v₋ᵢ` and `wᵢ ∩ vᵢ = ∅`. -/
def IsPairWitness {X Y : Type*} (H : Set (Hyp X Y)) {n : ℕ} (S : Fin n → X)
    (V : Finset (Fin n → Finset Y)) : Prop :=
  V.Nonempty ∧ (↑V ⊆ patterns H S) ∧
    ∀ v ∈ V, ∀ i : Fin n, ∃ w ∈ V, (∀ j, j ≠ i → w j = v j) ∧ Disjoint (w i) (v i)

/-- The disjoint-neighbor dimension `d_pair(H)` (Definition 5). -/
noncomputable def pairDim {X Y : Type*} (H : Set (Hyp X Y)) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : ∃ (S : Fin n → X) (V : Finset (Fin n → Finset Y)),
    Function.Injective S ∧ IsPairWitness H S V), (n : ℕ∞)

/-- A `ρ`-packed witness on `S` (Definition 7): a nonempty indexed list `v¹, …, v^M ∈ H|S`
(`M ≥ 1`, repetitions allowed, indices `Fin M`) and, for every direction `i`, a collection
`Bᵢ` of pairwise disjoint conflict blocks `B ⊆ [M]` with `2 ≤ |B| ≤ ℓ + 1`, `vᵃⱼ = vᵇⱼ` for
`a, b ∈ B` and `j ≠ i`, `⋂_{a∈B} vᵃᵢ = ∅`, and `|⋃_{B∈Bᵢ} B| ≥ ρM`. -/
def IsPackedWitness {X Y : Type*} (ℓ : ℕ) (ρ : ℝ) (H : Set (Hyp X Y)) {n : ℕ} (S : Fin n → X)
    (M : ℕ) (v : Fin M → Fin n → Finset Y) (B : Fin n → Finset (Finset (Fin M))) : Prop :=
  0 < M ∧ (∀ a, v a ∈ patterns H S) ∧
    ∀ i : Fin n,
      (B i : Set (Finset (Fin M))).PairwiseDisjoint id ∧
      (∀ b ∈ B i, 2 ≤ b.card ∧ b.card ≤ ℓ + 1 ∧
        (∀ a ∈ b, ∀ a' ∈ b, ∀ j, j ≠ i → v a j = v a' j) ∧
        ∀ y : Y, ∃ a ∈ b, y ∉ v a i) ∧
      ρ * M ≤ (((B i).biUnion id).card : ℝ)

/-- The packed dimension `d∩_{pack,ρ}(H)` (Definition 7), for a coverage parameter `ρ`
(Definition 7 takes `0 < γ < 1/(ℓ+1)`, and any `0 < ρ ≤ 1` for comparisons). -/
noncomputable def packDim {X Y : Type*} (ℓ : ℕ) (ρ : ℝ) (H : Set (Hyp X Y)) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : ∃ (S : Fin n → X) (M : ℕ) (v : Fin M → Fin n → Finset Y)
    (B : Fin n → Finset (Finset (Fin M))), Function.Injective S ∧ IsPackedWitness ℓ ρ H S M v B),
    (n : ℕ∞)

end MultiCorrectPAC.Demo


