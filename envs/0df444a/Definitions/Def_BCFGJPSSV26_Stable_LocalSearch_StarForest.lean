-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_StarForest
-- name    : BCFGJPSSV26_Stable_LocalSearch_StarForest
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:46.255346+00:00
-- url     : https://prove2.me/theorems/d026f0e4-fa86-4c14-8fb3-256d4ede7194
-- title:
--   BCFGJPSSV26.Stable.LocalSearch.StarForest — Swap families on star forests
-- statement:
--   This is module `BCFGJPSSV26.Stable.LocalSearch.StarForest` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   A variant of [BCFGJPSSV26b, Lemma 6.2]: a bipartite graph on finite sets `L` (left) and `R`
--   (right) in which every edge has an endpoint of degree at most `1`
--   (`BCFGJPSSV26.Stable.BiGraph.IsStarLike`), with `|R| ≤ |L|`, has families of **swaps**
--   `(Ls ⊆ L, Rs ⊆ R)` that are good for the refined local-search bound
--   (`BCFGJPSSV26.Stable.BiGraph.Good`): small swaps with `|Rs| ≤ |Ls| ≤ 24 N`, closed under the
--   neighbours of their left vertices, covering every right vertex and every left vertex that is not a
--   big hub (degree `≥ 2N`), using hubs on the left and leaves on the right at most once; and on
--   average over the families every left vertex of degree `≤ 1` is used at most `1 + 8/N` times
--   (`BCFGJPSSV26.Stable.BiGraph.exists_swap_families`).
--
--   The proof is a variant of the construction of [BCFGJPSSV26b, Section 6.3] that allows isolated
--   vertices and `|R| < |L|`: single edges are swapped alone. The other left vertices are hubs (degree
--   `≥ 2`) and leaves `LF` (leaves of right stars and isolated vertices); the other right vertices are
--   hubs and leaves `RF`.
--
--   * **Few left leaves** (`|LF| < 12 N`): one more swap of everything; it has at most
--     `2 |LF| < 24 N` left vertices, since every left hub has two leaves of its own in `RF` and
--     `|RF| + |hubs on the right| ≤ |hubs on the left| + |LF|`.
--   * **Many left leaves**: the right leaves are cut into pieces of at most `3 N` leaves keeping
--     small left stars (degree `< 2N`) together (`StarForestAux.exists_pieces`, `|RF| / N + 1`
--     pieces). The left leaves are put in a cyclic order with the leaves of each right star
--     consecutive; the first leaf of each star has weight `0`, the others weight `1`. For every
--     offset `r` of the cycle, piece `Z` with small hubs `H(Z)` gets the next block `Y` of weight
--     `|Z| - |H(Z)| + 1`, and the swap is `(Y ∪ H(Z), Z ∪ hubs(Y))`: a block meets at most one
--     more star than it has leaves of weight `0`, so `|hubs(Y)| ≤ |Y| - |Z| + |H(Z)|`. Blocks of
--     weight `1` are added until the walk has gone once around the cycle
--     (`StarForestAux.exists_cycle_blocks`). Since `|R| ≤ |L|`, the total weight exceeds that of
--     the cycle by at most the number of big hubs plus the number of pieces, `O(|LF| / N)`, so over
--     the `|LF|` offsets every left leaf is in at most `(1 + 8 / N) |LF|` swaps.
--
--   **Contents.** The module is published as a whole: 57 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Stable.BiGraph.exists_swap_families` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_StarForest`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/LocalSearch/StarForest.lean

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_StarForestAux

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.LocalSearch.StarForest` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Swap families on star forests

A variant of [BCFGJPSSV26b, Lemma 6.2]: a bipartite graph on finite sets `L` (left) and `R`
(right) in which every edge has an endpoint of degree at most `1`
(`BCFGJPSSV26.Stable.BiGraph.IsStarLike`), with `|R| ≤ |L|`, has families of **swaps**
`(Ls ⊆ L, Rs ⊆ R)` that are good for the refined local-search bound
(`BCFGJPSSV26.Stable.BiGraph.Good`): small swaps with `|Rs| ≤ |Ls| ≤ 24 N`, closed under the
neighbours of their left vertices, covering every right vertex and every left vertex that is not a
big hub (degree `≥ 2N`), using hubs on the left and leaves on the right at most once; and on
average over the families every left vertex of degree `≤ 1` is used at most `1 + 8/N` times
(`BCFGJPSSV26.Stable.BiGraph.exists_swap_families`).

The proof is a variant of the construction of [BCFGJPSSV26b, Section 6.3] that allows isolated
vertices and `|R| < |L|`: single edges are swapped alone. The other left vertices are hubs (degree
`≥ 2`) and leaves `LF` (leaves of right stars and isolated vertices); the other right vertices are
hubs and leaves `RF`.

* **Few left leaves** (`|LF| < 12 N`): one more swap of everything; it has at most
  `2 |LF| < 24 N` left vertices, since every left hub has two leaves of its own in `RF` and
  `|RF| + |hubs on the right| ≤ |hubs on the left| + |LF|`.
* **Many left leaves**: the right leaves are cut into pieces of at most `3 N` leaves keeping
  small left stars (degree `< 2N`) together (`StarForestAux.exists_pieces`, `|RF| / N + 1`
  pieces). The left leaves are put in a cyclic order with the leaves of each right star
  consecutive; the first leaf of each star has weight `0`, the others weight `1`. For every
  offset `r` of the cycle, piece `Z` with small hubs `H(Z)` gets the next block `Y` of weight
  `|Z| - |H(Z)| + 1`, and the swap is `(Y ∪ H(Z), Z ∪ hubs(Y))`: a block meets at most one
  more star than it has leaves of weight `0`, so `|hubs(Y)| ≤ |Y| - |Z| + |H(Z)|`. Blocks of
  weight `1` are added until the walk has gone once around the cycle
  (`StarForestAux.exists_cycle_blocks`). Since `|R| ≤ |L|`, the total weight exceeds that of
  the cycle by at most the number of big hubs plus the number of pieces, `O(|LF| / N)`, so over
  the `|LF|` offsets every left leaf is in at most `(1 + 8 / N) |LF|` swaps.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

/-- A bipartite graph on finite sets of left and right vertices. -/
structure BiGraph (α β : Type*) where
  /-- The left vertices. -/
  L : Finset α
  /-- The right vertices. -/
  R : Finset β
  /-- The edges. -/
  adj : α → β → Bool

/-- A swap: a set of left vertices and a set of right vertices. -/
structure Swap (α β : Type*) where
  /-- The left vertices. -/
  Ls : Finset α
  /-- The right vertices. -/
  Rs : Finset β

namespace BiGraph

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (G : BiGraph α β)

/-- The degree of a left vertex. -/
def degL (u : α) : ℕ := (G.R.filter fun v ↦ G.adj u v).card

/-- The degree of a right vertex. -/
def degR (v : β) : ℕ := (G.L.filter fun u ↦ G.adj u v).card

/-- **Star-like**: every edge has an endpoint of degree at most `1`. -/
def IsStarLike : Prop :=
  ∀ u ∈ G.L, ∀ v ∈ G.R, G.adj u v = true → G.degL u ≤ 1 ∨ G.degR v ≤ 1

/-- A **good** list of swaps for the refined local-search bound, with swap size `24 N`. -/
structure Good (N : ℕ) (𝒮 : List (Swap α β)) : Prop where
  subset : ∀ σ ∈ 𝒮, σ.Ls ⊆ G.L ∧ σ.Rs ⊆ G.R
  card : ∀ σ ∈ 𝒮, σ.Rs.card ≤ σ.Ls.card ∧ σ.Ls.card ≤ 24 * N
  closed : ∀ σ ∈ 𝒮, ∀ u ∈ σ.Ls, ∀ v ∈ G.R, G.adj u v = true → v ∈ σ.Rs
  coverR : ∀ v ∈ G.R, ∃ σ ∈ 𝒮, v ∈ σ.Rs
  coverL : ∀ u ∈ G.L, G.degL u < 2 * N → ∃ σ ∈ 𝒮, u ∈ σ.Ls
  hubL : ∀ u ∈ G.L, 2 ≤ G.degL u → 𝒮.countP (fun σ ↦ u ∈ σ.Ls) ≤ 1
  leafR : ∀ v ∈ G.R, G.degR v ≤ 1 → 𝒮.countP (fun σ ↦ v ∈ σ.Rs) ≤ 1
  length : 𝒮.length ≤ G.L.card + 2

end BiGraph

namespace BiGraph

open StarForestAux

variable {α β : Type*}

/-- Counting along the list of a finite set. -/
private theorem countP_toList {γ : Type*} (s : Finset γ) (p : γ → Prop) [DecidablePred p] :
    s.toList.countP (fun x ↦ decide (p x)) = #{x ∈ s | p x} := by
  rw [← Multiset.coe_countP, coe_toList, Multiset.countP_eq_card_filter]
  rfl

/-- Counting along `List.range`. -/
private theorem countP_range (s : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (List.range s).countP (fun x ↦ decide (p x)) = #{x ∈ range s | p x} := by
  rw [← Multiset.coe_countP, ← Multiset.range, Multiset.countP_eq_card_filter]
  rfl

/-- The right neighbours of a left vertex. -/
private def nbR (G : BiGraph α β) (u : α) : Finset β := G.R.filter fun v ↦ G.adj u v

/-- The left neighbours of a right vertex. -/
private def nbL (G : BiGraph α β) (v : β) : Finset α := G.L.filter fun u ↦ G.adj u v

/-- Left vertices of single-edge components. -/
private def E1L (G : BiGraph α β) : Finset α :=
  G.L.filter fun u ↦ ∃ v ∈ G.R, G.adj u v ∧ G.degL u = 1 ∧ G.degR v = 1

/-- Right vertices of single-edge components. -/
private def E1R (G : BiGraph α β) : Finset β :=
  G.R.filter fun v ↦ ∃ u ∈ G.L, G.adj u v ∧ G.degL u = 1 ∧ G.degR v = 1

/-- Left hubs. -/
private def HL (G : BiGraph α β) : Finset α := G.L.filter fun u ↦ 2 ≤ G.degL u

/-- Right hubs. -/
private def HR (G : BiGraph α β) : Finset β := G.R.filter fun v ↦ 2 ≤ G.degR v

/-- Left leaves of right stars, and isolated left vertices. -/
private def LF (G : BiGraph α β) : Finset α :=
  G.L.filter fun u ↦ G.degL u ≤ 1 ∧ ∀ v ∈ G.R, G.adj u v → 2 ≤ G.degR v

/-- Right leaves of left stars, and isolated right vertices. -/
private def RF (G : BiGraph α β) : Finset β :=
  G.R.filter fun v ↦ G.degR v ≤ 1 ∧ ∀ u ∈ G.L, G.adj u v → 2 ≤ G.degL u

variable {G : BiGraph α β}

private theorem mem_nbR {u : α} {v : β} : v ∈ G.nbR u ↔ v ∈ G.R ∧ G.adj u v = true := mem_filter

private theorem mem_nbL {u : α} {v : β} : u ∈ G.nbL v ↔ u ∈ G.L ∧ G.adj u v = true := mem_filter

private theorem degL_eq (u : α) : G.degL u = (G.nbR u).card := rfl

private theorem degR_eq (v : β) : G.degR v = (G.nbL v).card := rfl

private theorem one_le_degL {u : α} {v : β} (hv : v ∈ G.R) (h : G.adj u v = true) : 1 ≤ G.degL u :=
  card_pos.2 ⟨v, mem_filter.2 ⟨hv, h⟩⟩

private theorem one_le_degR {u : α} {v : β} (hu : u ∈ G.L) (h : G.adj u v = true) : 1 ≤ G.degR v :=
  card_pos.2 ⟨u, mem_filter.2 ⟨hu, h⟩⟩

private theorem eq_of_degR_le {u u' : α} {v : β} (hd : G.degR v ≤ 1) (hu : u ∈ G.L) (hu' : u' ∈ G.L)
    (h : G.adj u v = true) (h' : G.adj u' v = true) : u = u' :=
  card_le_one.1 hd u (mem_filter.2 ⟨hu, h⟩) u' (mem_filter.2 ⟨hu', h'⟩)

private theorem eq_of_degL_le {u : α} {v v' : β} (hd : G.degL u ≤ 1) (hv : v ∈ G.R) (hv' : v' ∈ G.R)
    (h : G.adj u v = true) (h' : G.adj u v' = true) : v = v' :=
  card_le_one.1 hd v (mem_filter.2 ⟨hv, h⟩) v' (mem_filter.2 ⟨hv', h'⟩)

private theorem mem_HL {u : α} : u ∈ G.HL ↔ u ∈ G.L ∧ 2 ≤ G.degL u := mem_filter

private theorem mem_HR {v : β} : v ∈ G.HR ↔ v ∈ G.R ∧ 2 ≤ G.degR v := mem_filter

private theorem mem_LF {u : α} : u ∈ G.LF ↔ u ∈ G.L ∧ G.degL u ≤ 1 ∧
    ∀ v ∈ G.R, G.adj u v = true → 2 ≤ G.degR v := mem_filter

private theorem mem_RF {v : β} : v ∈ G.RF ↔ v ∈ G.R ∧ G.degR v ≤ 1 ∧
    ∀ u ∈ G.L, G.adj u v = true → 2 ≤ G.degL u := mem_filter

private theorem mem_E1L {u : α} : u ∈ G.E1L ↔ u ∈ G.L ∧
    ∃ v ∈ G.R, G.adj u v = true ∧ G.degL u = 1 ∧ G.degR v = 1 := mem_filter

private theorem mem_E1R {v : β} : v ∈ G.E1R ↔ v ∈ G.R ∧
    ∃ u ∈ G.L, G.adj u v = true ∧ G.degL u = 1 ∧ G.degR v = 1 := mem_filter

/-- The leaves of a left hub are right leaves. -/
private theorem nbR_subset_RF (hG : G.IsStarLike) {u : α} (hu : u ∈ G.HL) : G.nbR u ⊆ G.RF := by
  intro v hv
  rw [mem_nbR] at hv
  rw [mem_HL] at hu
  have hd : G.degR v ≤ 1 := (hG u hu.1 v hv.1 hv.2).resolve_left (by omega)
  refine mem_RF.2 ⟨hv.1, hd, fun u' hu' h' ↦ ?_⟩
  rw [eq_of_degR_le hd hu' hu.1 h' hv.2]
  exact hu.2

/-- Distinct left hubs have disjoint leaves. -/
private theorem disjoint_nbR (hG : G.IsStarLike) {u u' : α} (hu : u ∈ G.HL) (hu' : u' ∈ G.HL)
    (h : u ≠ u') : Disjoint (G.nbR u) (G.nbR u') := by
  refine disjoint_left.2 fun v hv hv' ↦ h ?_
  have hd := (mem_RF.1 (nbR_subset_RF hG hu hv)).2.1
  exact eq_of_degR_le hd (mem_HL.1 hu).1 (mem_HL.1 hu').1 (mem_nbR.1 hv).2 (mem_nbR.1 hv').2

/-- The leaves of a right hub are left leaves. -/
private theorem nbL_subset_LF (hG : G.IsStarLike) {x : β} (hx : x ∈ G.HR) : G.nbL x ⊆ G.LF := by
  intro u hu
  rw [mem_nbL] at hu
  rw [mem_HR] at hx
  have hd : G.degL u ≤ 1 := (hG u hu.1 x hx.1 hu.2).resolve_right (by omega)
  refine mem_LF.2 ⟨hu.1, hd, fun v hv h ↦ ?_⟩
  rw [eq_of_degL_le hd hv hx.1 h hu.2]
  exact hx.2

/-- The neighbour of a left leaf is a right hub. -/
private theorem LF_adj {u : α} {v : β} (hu : u ∈ G.LF) (hv : v ∈ G.R) (h : G.adj u v = true) :
    v ∈ G.HR :=
  mem_HR.2 ⟨hv, (mem_LF.1 hu).2.2 v hv h⟩

private theorem LF_not_E1L {u : α} (hu : u ∈ G.LF) : u ∉ G.E1L := by
  intro h
  obtain ⟨-, v, hv, hadj, -, hd⟩ := mem_E1L.1 h
  have := (mem_LF.1 hu).2.2 v hv hadj
  omega

private theorem HL_not_E1L {u : α} (hu : u ∈ G.HL) : u ∉ G.E1L := by
  intro h
  obtain ⟨-, v, -, -, hd, -⟩ := mem_E1L.1 h
  have := (mem_HL.1 hu).2
  omega

private theorem RF_not_E1R {v : β} (hv : v ∈ G.RF) : v ∉ G.E1R := by
  intro h
  obtain ⟨-, u, hu, hadj, hd, -⟩ := mem_E1R.1 h
  have := (mem_RF.1 hv).2.2 u hu hadj
  omega

private theorem HR_not_E1R {v : β} (hv : v ∈ G.HR) : v ∉ G.E1R := by
  intro h
  obtain ⟨-, u, -, -, -, hd⟩ := mem_E1R.1 h
  have := (mem_HR.1 hv).2
  omega

private theorem LF_not_HL {u : α} (hu : u ∈ G.LF) : u ∉ G.HL := by
  intro h
  have := (mem_LF.1 hu).2.1
  have := (mem_HL.1 h).2
  omega

/-- The left vertices: single edges, hubs and leaves. -/
private theorem card_L : G.L.card = G.E1L.card + G.HL.card + G.LF.card := by
  classical
  have hU : G.L = G.E1L ∪ G.HL ∪ G.LF := by
    ext u
    simp only [mem_union]
    constructor
    · intro hu
      by_cases h2 : 2 ≤ G.degL u
      · exact Or.inl (Or.inr (mem_HL.2 ⟨hu, h2⟩))
      by_cases he : u ∈ G.E1L
      · exact Or.inl (Or.inl he)
      refine Or.inr (mem_LF.2 ⟨hu, by omega, fun v hv h ↦ ?_⟩)
      have h1 := one_le_degL hv h
      have h1' := one_le_degR hu h
      by_contra h3
      exact he (mem_E1L.2 ⟨hu, v, hv, h, by omega, by omega⟩)
    · rintro ((h | h) | h)
      · exact (mem_E1L.1 h).1
      · exact (mem_HL.1 h).1
      · exact (mem_LF.1 h).1
  rw [hU, card_union_of_disjoint, card_union_of_disjoint]
  · exact disjoint_left.2 fun u h1 h2 ↦ HL_not_E1L h2 h1
  · refine disjoint_left.2 fun u h1 h2 ↦ ?_
    rcases mem_union.1 h1 with h1 | h1
    · exact LF_not_E1L h2 h1
    · exact LF_not_HL h2 h1

/-- The right vertices: single edges, hubs and leaves. -/
private theorem card_R : G.R.card = G.E1R.card + G.HR.card + G.RF.card := by
  classical
  have hU : G.R = G.E1R ∪ G.HR ∪ G.RF := by
    ext v
    simp only [mem_union]
    constructor
    · intro hv
      by_cases h2 : 2 ≤ G.degR v
      · exact Or.inl (Or.inr (mem_HR.2 ⟨hv, h2⟩))
      by_cases he : v ∈ G.E1R
      · exact Or.inl (Or.inl he)
      refine Or.inr (mem_RF.2 ⟨hv, by omega, fun u hu h ↦ ?_⟩)
      have h1 := one_le_degL hv h
      have h1' := one_le_degR hu h
      by_contra h3
      exact he (mem_E1R.2 ⟨hv, u, hu, h, by omega, by omega⟩)
    · rintro ((h | h) | h)
      · exact (mem_E1R.1 h).1
      · exact (mem_HR.1 h).1
      · exact (mem_RF.1 h).1
  rw [hU, card_union_of_disjoint, card_union_of_disjoint]
  · exact disjoint_left.2 fun v h1 h2 ↦ HR_not_E1R h2 h1
  · refine disjoint_left.2 fun v h1 h2 ↦ ?_
    rcases mem_union.1 h1 with h1 | h1
    · exact RF_not_E1R h2 h1
    · have := (mem_RF.1 h2).2.1
      have := (mem_HR.1 h1).2
      omega

/-- Single edges have as many left as right vertices (double counting). -/
private theorem card_E1 : G.E1L.card = G.E1R.card := by
  classical
  have key : ∑ u ∈ G.L, ∑ v ∈ G.R,
      (if G.adj u v = true ∧ G.degL u = 1 ∧ G.degR v = 1 then 1 else 0) =
      ∑ v ∈ G.R, ∑ u ∈ G.L,
      (if G.adj u v = true ∧ G.degL u = 1 ∧ G.degR v = 1 then 1 else 0) := sum_comm
  have hL : ∀ u ∈ G.L, ∑ v ∈ G.R,
      (if G.adj u v = true ∧ G.degL u = 1 ∧ G.degR v = 1 then 1 else 0) =
      if u ∈ G.E1L then 1 else 0 := by
    intro u hu
    rw [← card_filter]
    split_ifs with h
    · obtain ⟨-, v, hv, hadj, hd, hd'⟩ := mem_E1L.1 h
      refine le_antisymm ?_ (card_pos.2 ⟨v, mem_filter.2 ⟨hv, hadj, hd, hd'⟩⟩)
      rw [← hd, degL_eq]
      exact card_le_card fun v' hv' ↦ mem_nbR.2 ⟨(mem_filter.1 hv').1, (mem_filter.1 hv').2.1⟩
    · refine card_eq_zero.2 (filter_eq_empty_iff.2 fun v hv hP ↦ h ?_)
      exact mem_E1L.2 ⟨hu, v, hv, hP⟩
  have hR : ∀ v ∈ G.R, ∑ u ∈ G.L,
      (if G.adj u v = true ∧ G.degL u = 1 ∧ G.degR v = 1 then 1 else 0) =
      if v ∈ G.E1R then 1 else 0 := by
    intro v hv
    rw [← card_filter]
    split_ifs with h
    · obtain ⟨-, u, hu, hadj, hd, hd'⟩ := mem_E1R.1 h
      refine le_antisymm ?_ (card_pos.2 ⟨u, mem_filter.2 ⟨hu, hadj, hd, hd'⟩⟩)
      rw [← hd', degR_eq]
      exact card_le_card fun u' hu' ↦ mem_nbL.2 ⟨(mem_filter.1 hu').1, (mem_filter.1 hu').2.1⟩
    · refine card_eq_zero.2 (filter_eq_empty_iff.2 fun u hu hP ↦ h ?_)
      exact mem_E1R.2 ⟨hv, u, hu, hP⟩
  rw [sum_congr rfl hL, sum_congr rfl hR, ← card_filter, ← card_filter, filter_mem_eq_inter,
    filter_mem_eq_inter, inter_eq_right.2 (show G.E1L ⊆ G.L from filter_subset _ _),
    inter_eq_right.2 (show G.E1R ⊆ G.R from filter_subset _ _)] at key
  exact key

/-- Left hubs have disjoint sets of leaves among the right leaves. -/
private theorem sum_degL_le (hG : G.IsStarLike) {X : Finset α} (hX : X ⊆ G.HL) :
    ∑ u ∈ X, G.degL u ≤ G.RF.card := by
  classical
  change ∑ u ∈ X, (G.nbR u).card ≤ _
  rw [← card_biUnion fun u hu u' hu' h ↦ disjoint_nbR hG (hX hu) (hX hu') h]
  exact card_le_card (biUnion_subset.2 fun u hu ↦ nbR_subset_RF hG (hX hu))

/-- Every left vertex is in a single edge, a hub or a leaf. -/
private theorem mem_L_cases {u : α} (hu : u ∈ G.L) : u ∈ G.E1L ∨ u ∈ G.HL ∨ u ∈ G.LF := by
  by_cases h2 : 2 ≤ G.degL u
  · exact Or.inr (Or.inl (mem_HL.2 ⟨hu, h2⟩))
  by_cases he : u ∈ G.E1L
  · exact Or.inl he
  refine Or.inr (Or.inr (mem_LF.2 ⟨hu, by omega, fun v hv h ↦ ?_⟩))
  have h1 := one_le_degL hv h
  have h1' := one_le_degR hu h
  by_contra h3
  exact he (mem_E1L.2 ⟨hu, v, hv, h, by omega, by omega⟩)

/-- Every right vertex is in a single edge, a hub or a leaf. -/
private theorem mem_R_cases {v : β} (hv : v ∈ G.R) : v ∈ G.E1R ∨ v ∈ G.HR ∨ v ∈ G.RF := by
  by_cases h2 : 2 ≤ G.degR v
  · exact Or.inr (Or.inl (mem_HR.2 ⟨hv, h2⟩))
  by_cases he : v ∈ G.E1R
  · exact Or.inl he
  refine Or.inr (Or.inr (mem_RF.2 ⟨hv, by omega, fun u hu h ↦ ?_⟩))
  have h1 := one_le_degL hv h
  have h1' := one_le_degR hu h
  by_contra h3
  exact he (mem_E1R.2 ⟨hv, u, hu, h, by omega, by omega⟩)

/-- Every left hub has two leaves of its own. -/
private theorem two_mul_card_HL_le (hG : G.IsStarLike) : 2 * G.HL.card ≤ G.RF.card := by
  have h1 := sum_degL_le hG (subset_refl G.HL)
  have h2 : 2 * G.HL.card ≤ ∑ u ∈ G.HL, G.degL u := by
    rw [mul_comm, ← smul_eq_mul, ← sum_const]
    exact sum_le_sum fun u hu ↦ (mem_HL.1 hu).2
  omega

/-- `|R| ≤ |L|` outside single edges. -/
private theorem card_RF_add_le (hc : G.R.card ≤ G.L.card) :
    G.RF.card + G.HR.card ≤ G.HL.card + G.LF.card := by
  have hL := G.card_L
  have hR := G.card_R
  have hE := G.card_E1
  omega

variable (G) in
/-- The swaps of the single-edge components. -/
private noncomputable def e1 : List (Swap α β) := G.E1L.toList.map fun u ↦ ⟨{u}, G.nbR u⟩

private theorem mem_e1 {σ : Swap α β} : σ ∈ G.e1 ↔ ∃ u ∈ G.E1L, σ = ⟨{u}, G.nbR u⟩ := by
  simp only [e1, List.mem_map, mem_toList]
  constructor <;> rintro ⟨u, hu, rfl⟩ <;> exact ⟨u, hu, rfl⟩

private theorem length_e1 : G.e1.length = G.E1L.card := by simp [e1]

/-- A left vertex is in the single-edge swap of its edge only. -/
private theorem countP_e1_L [DecidableEq α] (u : α) :
    G.e1.countP (fun σ ↦ decide (u ∈ σ.Ls)) = if u ∈ G.E1L then 1 else 0 := by
  rw [e1, List.countP_map]
  change G.E1L.toList.countP (fun u' ↦ decide (u ∈ ({u'} : Finset α))) = _
  rw [countP_toList]
  split_ifs with h
  · refine card_eq_one.2 ⟨u, ?_⟩
    ext u'
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨-, rfl⟩
      rfl
    · rintro rfl
      exact ⟨h, rfl⟩
  · refine card_eq_zero.2 (filter_eq_empty_iff.2 fun u' hu' h' ↦ h ?_)
    rw [mem_singleton] at h'
    rwa [h']

/-- The single-edge swaps containing a right vertex. -/
private theorem countP_e1_R [DecidableEq β] (v : β) :
    G.e1.countP (fun σ ↦ decide (v ∈ σ.Rs)) = #{u ∈ G.E1L | v ∈ G.nbR u} := by
  rw [e1, List.countP_map]
  exact countP_toList _ _

/-- Counting along a list indexed by `List.range`. -/
private theorem countP_map_range {γ : Type*} (s : ℕ) (f : ℕ → γ) (p : γ → Prop) [DecidablePred p] :
    ((List.range s).map f).countP (fun x ↦ decide (p x)) = #{q ∈ range s | p (f q)} := by
  rw [List.countP_map]
  exact countP_range s (fun q ↦ p (f q))

/-- Goodness of the single-edge swaps followed by swaps avoiding single-edge components. -/
private theorem good_e1_append [DecidableEq α] [DecidableEq β] {N : ℕ} (hN : 1 ≤ N)
    (rest : List (Swap α β))
    (r1 : ∀ σ ∈ rest, σ.Ls ⊆ G.L \ G.E1L ∧ σ.Rs ⊆ G.R \ G.E1R)
    (r2 : ∀ σ ∈ rest, σ.Rs.card ≤ σ.Ls.card ∧ σ.Ls.card ≤ 24 * N)
    (r3 : ∀ σ ∈ rest, ∀ u ∈ σ.Ls, ∀ v ∈ G.R, G.adj u v = true → v ∈ σ.Rs)
    (r4 : ∀ v ∈ G.R \ G.E1R, ∃ σ ∈ rest, v ∈ σ.Rs)
    (r5 : ∀ u ∈ G.L \ G.E1L, G.degL u < 2 * N → ∃ σ ∈ rest, u ∈ σ.Ls)
    (r6 : ∀ u ∈ G.L, 2 ≤ G.degL u → rest.countP (fun σ ↦ u ∈ σ.Ls) ≤ 1)
    (r7 : ∀ v ∈ G.R, G.degR v ≤ 1 → rest.countP (fun σ ↦ v ∈ σ.Rs) ≤ 1)
    (r8 : rest.length ≤ G.HL.card + G.LF.card + 2) :
    G.Good N (G.e1 ++ rest) where
  subset σ hσ := by
    rcases List.mem_append.1 hσ with h | h
    · obtain ⟨u, hu, rfl⟩ := mem_e1.1 h
      exact ⟨singleton_subset_iff.2 (mem_E1L.1 hu).1, filter_subset _ _⟩
    · exact ⟨(r1 σ h).1.trans sdiff_subset, (r1 σ h).2.trans sdiff_subset⟩
  card σ hσ := by
    rcases List.mem_append.1 hσ with h | h
    · obtain ⟨u, hu, rfl⟩ := mem_e1.1 h
      obtain ⟨-, v, -, -, hd, -⟩ := mem_E1L.1 hu
      have : (G.nbR u).card = 1 := hd
      simp only [card_singleton, this]
      omega
    · exact r2 σ h
  closed σ hσ u hu v hv h := by
    rcases List.mem_append.1 hσ with h' | h'
    · obtain ⟨u', hu', rfl⟩ := mem_e1.1 h'
      rw [mem_singleton] at hu
      subst hu
      exact mem_nbR.2 ⟨hv, h⟩
    · exact r3 σ h' u hu v hv h
  coverR v hv := by
    by_cases he : v ∈ G.E1R
    · obtain ⟨-, u, hu, hadj, hd, hd'⟩ := mem_E1R.1 he
      exact ⟨⟨{u}, G.nbR u⟩, List.mem_append_left _
        (mem_e1.2 ⟨u, mem_E1L.2 ⟨hu, v, hv, hadj, hd, hd'⟩, rfl⟩), mem_nbR.2 ⟨hv, hadj⟩⟩
    · obtain ⟨σ, hσ, h⟩ := r4 v (mem_sdiff.2 ⟨hv, he⟩)
      exact ⟨σ, List.mem_append_right _ hσ, h⟩
  coverL u hu hd := by
    by_cases he : u ∈ G.E1L
    · exact ⟨⟨{u}, G.nbR u⟩, List.mem_append_left _ (mem_e1.2 ⟨u, he, rfl⟩),
        mem_singleton_self u⟩
    · obtain ⟨σ, hσ, h⟩ := r5 u (mem_sdiff.2 ⟨hu, he⟩) hd
      exact ⟨σ, List.mem_append_right _ hσ, h⟩
  hubL u hu hd := by
    have he := HL_not_E1L (mem_HL.2 ⟨hu, hd⟩)
    rw [List.countP_append, countP_e1_L]
    simp only [he, ↓reduceIte, zero_add]
    exact r6 u hu hd
  leafR v hv hd := by
    rw [List.countP_append, countP_e1_R]
    by_cases he : v ∈ G.E1R
    · have h0 : rest.countP (fun σ ↦ v ∈ σ.Rs) = 0 := List.countP_eq_zero.2 fun σ hσ ↦ by
        simpa using fun h ↦ (mem_sdiff.1 ((r1 σ hσ).2 h)).2 he
      rw [h0, add_zero]
      refine le_trans (card_le_card fun u hu ↦ ?_) hd
      rw [mem_filter] at hu
      exact mem_nbL.2 ⟨(mem_E1L.1 hu.1).1, (mem_nbR.1 hu.2).2⟩
    · have h0 : #{u ∈ G.E1L | v ∈ G.nbR u} = 0 := by
        refine card_eq_zero.2 (filter_eq_empty_iff.2 fun u hu hvu ↦ he ?_)
        obtain ⟨huL, v', -, -, hdu, -⟩ := mem_E1L.1 hu
        have hadj := (mem_nbR.1 hvu).2
        have := one_le_degR huL hadj
        exact mem_E1R.2 ⟨hv, u, huL, hadj, hdu, by omega⟩
      rw [h0, zero_add]
      exact r7 v hv hd
  length := by
    rw [List.length_append, length_e1]
    have := G.card_L
    omega

/-- **The small case**: few left leaves; one swap of everything outside single edges. -/
private theorem small_case [DecidableEq α] [DecidableEq β] (hG : G.IsStarLike)
    (hc : G.R.card ≤ G.L.card) {N : ℕ} (hN : 200 ≤ N) (hsmall : G.LF.card < 12 * N) :
    ∃ (b : ℕ) (_ : 0 < b) (𝒮 : Fin b → List (Swap α β)), (∀ r, G.Good N (𝒮 r)) ∧
      ∀ u ∈ G.L, G.degL u ≤ 1 →
        (∑ r, ((𝒮 r).countP fun σ ↦ u ∈ σ.Ls : ℝ)) ≤ (1 + 8 / N) * b := by
  have hL := G.card_L
  have hR := G.card_R
  have hE := G.card_E1
  have h2 := two_mul_card_HL_le hG
  have hLs : (G.L \ G.E1L).card = G.HL.card + G.LF.card := by
    rw [card_sdiff_of_subset (show G.E1L ⊆ G.L from filter_subset _ _)]
    omega
  have hRs : (G.R \ G.E1R).card = G.HR.card + G.RF.card := by
    rw [card_sdiff_of_subset (show G.E1R ⊆ G.R from filter_subset _ _)]
    omega
  refine ⟨1, one_pos, fun _ ↦ G.e1 ++ [⟨G.L \ G.E1L, G.R \ G.E1R⟩], fun _ ↦ ?_, ?_⟩
  · refine good_e1_append (by omega) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by simp)
    · intro σ hσ
      rw [List.mem_singleton] at hσ
      subst hσ
      exact ⟨subset_refl _, subset_refl _⟩
    · intro σ hσ
      rw [List.mem_singleton] at hσ
      subst hσ
      dsimp only
      omega
    · intro σ hσ u hu v hv h
      rw [List.mem_singleton] at hσ
      subst hσ
      refine mem_sdiff.2 ⟨hv, fun he ↦ ?_⟩
      obtain ⟨-, u', hu', hadj', hd', hd''⟩ := mem_E1R.1 he
      have := eq_of_degR_le hd''.le (mem_sdiff.1 hu).1 hu' h hadj'
      subst this
      exact (mem_sdiff.1 hu).2 (mem_E1L.2 ⟨hu', v, hv, hadj', hd', hd''⟩)
    · intro v hv
      exact ⟨_, List.mem_singleton_self _, hv⟩
    · intro u hu _
      exact ⟨_, List.mem_singleton_self _, hu⟩
    · intro u _ _
      rw [List.countP_singleton]
      split_ifs <;> omega
    · intro v _ _
      rw [List.countP_singleton]
      split_ifs <;> omega
  · intro u hu _
    have hcnt : (G.e1 ++ ([⟨G.L \ G.E1L, G.R \ G.E1R⟩] : List (Swap α β))).countP
        (fun σ ↦ decide (u ∈ σ.Ls)) = 1 := by
      rw [List.countP_append, countP_e1_L, List.countP_singleton]
      by_cases he : u ∈ G.E1L <;> simp [he, hu]
    rw [Fin.sum_univ_one, hcnt]
    have : (0 : ℝ) ≤ 8 / N := by positivity
    simp only [Nat.cast_one]
    linarith

/-- The arithmetic of the overflow of the walk around the cycle. -/
private theorem numeric_bound {N M RF HB p X : ℕ} (hM : 12 * N ≤ M) (hRF : RF ≤ 2 * M)
    (hHB : 2 * N * HB ≤ RF) (hp : N * (p - 1) ≤ RF) (hX : X ≤ HB + p + 1) :
    N * (2 * X) ≤ 8 * M := by
  have h1 : N * X ≤ N * (HB + (p - 1) + 2) := Nat.mul_le_mul_left _ (by omega)
  have h2 : N * (HB + (p - 1) + 2) = N * HB + N * (p - 1) + 2 * N := by
    rw [Nat.mul_add, Nat.mul_add]
    omega
  have h3 : 2 * N * HB = 2 * (N * HB) := by rw [Nat.mul_assoc]
  have h4 : N * (2 * X) = 2 * (N * X) := by rw [Nat.mul_left_comm]
  omega

/-- **The large case**: many left leaves; the cyclic construction. -/
private theorem large_case [DecidableEq α] [DecidableEq β] (hG : G.IsStarLike)
    (hc : G.R.card ≤ G.L.card) {N : ℕ} (hN : 200 ≤ N) (hlarge : 12 * N ≤ G.LF.card) :
    ∃ (b : ℕ) (_ : 0 < b) (𝒮 : Fin b → List (Swap α β)), (∀ r, G.Good N (𝒮 r)) ∧
      ∀ u ∈ G.L, G.degL u ≤ 1 →
        (∑ r, ((𝒮 r).countP fun σ ↦ u ∈ σ.Ls : ℝ)) ≤ (1 + 8 / N) * b := by
  obtain ⟨M, hM⟩ : ∃ M, M = G.LF.card := ⟨_, rfl⟩
  have hMpos : 0 < M := by omega
  have hRFadd := card_RF_add_le hc
  have h2HL := two_mul_card_HL_le hG
  obtain ⟨HS, hHS⟩ : ∃ HS : Finset α, HS = G.HL.filter fun u ↦ G.degL u < 2 * N := ⟨_, rfl⟩
  obtain ⟨HB, hHB⟩ : ∃ HB : Finset α, HB = G.HL.filter fun u ↦ ¬ G.degL u < 2 * N :=
    ⟨_, rfl⟩
  have memHS : ∀ u, u ∈ HS ↔ u ∈ G.HL ∧ G.degL u < 2 * N := fun u ↦ by rw [hHS, mem_filter]
  have hHSB : HS.card + HB.card = G.HL.card := by
    rw [hHS, hHB]
    exact card_filter_add_card_filter_not _
  have hHSHL : HS ⊆ G.HL := fun u hu ↦ ((memHS u).1 hu).1
  have h2NHB : 2 * N * HB.card ≤ G.RF.card := by
    have h1 := sum_degL_le hG (show HB ⊆ G.HL by rw [hHB]; exact filter_subset _ _)
    have h2 : 2 * N * HB.card ≤ ∑ u ∈ HB, G.degL u := by
      rw [mul_comm, ← smul_eq_mul, ← sum_const]
      exact sum_le_sum fun u hu ↦ by
        rw [hHB, mem_filter] at hu
        omega
    omega
  -- the pieces
  obtain ⟨φR, φH, hφR, hφRH, hφcard⟩ := exists_pieces (N := N) (by omega) G.RF HS G.nbR
    (fun u hu u' hu' h ↦ disjoint_nbR hG (hHSHL hu) (hHSHL hu') h)
    (fun u hu ↦ ((memHS u).1 hu).2)
  obtain ⟨p, hp⟩ : ∃ p, p = G.RF.card / N + 1 := ⟨_, rfl⟩
  have hNp : N * (p - 1) ≤ G.RF.card := by
    rw [hp, Nat.add_sub_cancel, mul_comm]
    exact Nat.div_mul_le_self _ _
  obtain ⟨Zq, hZq⟩ : ∃ Zq : ℕ → Finset β, Zq = fun q ↦ G.RF.filter fun v ↦ φR v = q :=
    ⟨_, rfl⟩
  obtain ⟨Hq, hHq⟩ : ∃ Hq : ℕ → Finset α, Hq = fun q ↦ HS.filter fun u ↦ φH u = q := ⟨_, rfl⟩
  have memZq : ∀ q v, v ∈ Zq q ↔ v ∈ G.RF ∧ φR v = q := fun q v ↦ by rw [hZq, mem_filter]
  have memHq : ∀ q u, u ∈ Hq q ↔ u ∈ HS ∧ φH u = q := fun q u ↦ by rw [hHq, mem_filter]
  have hZcard : ∀ q, (Zq q).card ≤ 3 * N := fun q ↦ by rw [hZq]; exact hφcard q
  have hnbR : ∀ u ∈ HS, 2 ≤ (G.nbR u).card := fun u hu ↦ (mem_HL.1 (hHSHL hu)).2
  have hφH : ∀ u ∈ HS, φH u ≤ G.RF.card / N := by
    intro u hu
    obtain ⟨v, hv⟩ : (G.nbR u).Nonempty := card_pos.1 (by have := hnbR u hu; omega)
    rw [← hφRH u hu v hv]
    exact hφR v (nbR_subset_RF hG (hHSHL hu) hv)
  have hHZ : ∀ q, (Hq q).card ≤ (Zq q).card := by
    intro q
    have h1 : (Hq q).biUnion G.nbR ⊆ Zq q := biUnion_subset.2 fun u hu v hv ↦ by
      obtain ⟨huS, huq⟩ := (memHq q u).1 hu
      exact (memZq q v).2 ⟨nbR_subset_RF hG (hHSHL huS) hv, (hφRH u huS v hv).trans huq⟩
    have h2 := card_le_card h1
    rw [card_biUnion fun u hu u' hu' h ↦ disjoint_nbR hG (hHSHL ((memHq q u).1 hu).1)
      (hHSHL ((memHq q u').1 hu').1) h] at h2
    have h3 : (Hq q).card ≤ ∑ u ∈ Hq q, (G.nbR u).card := by
      rw [card_eq_sum_ones]
      exact sum_le_sum fun u hu ↦ by have := hnbR u ((memHq q u).1 hu).1; omega
    omega
  have hZempty : ∀ q, p ≤ q → Zq q = ∅ := fun q hq ↦
    eq_empty_of_forall_notMem fun v hv ↦ by
      obtain ⟨hv, h⟩ := (memZq q v).1 hv
      have := hφR v hv
      omega
  have hHempty : ∀ q, p ≤ q → Hq q = ∅ := fun q hq ↦
    eq_empty_of_forall_notMem fun u hu ↦ by
      obtain ⟨hu, h⟩ := (memHq q u).1 hu
      have := hφH u hu
      omega
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℕ, ∀ q, w q = (Zq q).card - (Hq q).card + 1 := ⟨_, fun _ ↦ rfl⟩
  have hsumZ : ∑ q ∈ range p, (Zq q).card = G.RF.card := by
    rw [hZq]
    exact (card_eq_sum_card_fiberwise fun v hv ↦ mem_range.2 (by have := hφR v hv; omega)).symm
  have hsumH : ∑ q ∈ range p, (Hq q).card = HS.card := by
    rw [hHq]
    exact (card_eq_sum_card_fiberwise fun u hu ↦ mem_range.2 (by have := hφH u hu; omega)).symm
  obtain ⟨D0, hD0def⟩ : ∃ D0, D0 = ∑ q ∈ range p, w q := ⟨_, rfl⟩
  have hD0 : D0 + HS.card = G.RF.card + p := by
    rw [hD0def, ← hsumZ, ← hsumH, ← sum_add_distrib]
    have : ∀ q ∈ range p, w q + (Hq q).card = (Zq q).card + 1 := fun q _ ↦ by
      have := hHZ q
      rw [hw]
      omega
    rw [sum_congr rfl this, sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one]
  -- the cyclic blocks
  obtain ⟨E, hME, hEM, hcyc⟩ := exists_cycle_blocks G.LF G.HR (fun u x ↦ G.adj u x = true)
    (fun u hu x hx x' hx' h h' ↦ eq_of_degL_le (mem_LF.1 hu).2.1 (mem_HR.1 hx).1
      (mem_HR.1 hx').1 h h')
    (fun x hx ↦ by
      obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 (show 1 < (G.nbL x).card from
        (mem_HR.1 hx).2)
      exact ⟨a, nbL_subset_LF hG hx ha, b, nbL_subset_LF hG hx hb, hab, (mem_nbL.1 ha).2,
        (mem_nbL.1 hb).2⟩)
    (by omega)
  rw [← hM] at hME hEM hcyc
  obtain ⟨s, hs⟩ : ∃ s, s = p + (E + 1 - D0) := ⟨_, rfl⟩
  have hW : ∑ q ∈ range s, w q = D0 + (E + 1 - D0) := by
    rw [hs, sum_range_add, ← hD0def]
    congr 1
    have h1 : ∀ x ∈ range (E + 1 - D0), w (p + x) = 1 := fun x _ ↦ by
      rw [hw, hZempty (p + x) (by omega), hHempty (p + x) (by omega)]
      simp
    rw [sum_congr rfl h1, sum_const, card_range, smul_eq_mul, mul_one]
  have hwle : ∀ q, w q ≤ 3 * N + 1 := fun q ↦ by
    have := hZcard q
    rw [hw]
    omega
  obtain ⟨Y, hY1, hY2, hY3, hY4, hY5⟩ := hcyc w s (fun q _ ↦ by have := hwle q; omega)
    (by omega)
  obtain ⟨HY, hHY⟩ : ∃ HY : ℕ → ℕ → Finset β,
      HY = fun r q ↦ G.HR.filter fun x ↦ ∃ u ∈ Y r q, G.adj u x = true := ⟨_, rfl⟩
  have memHY : ∀ r q x, x ∈ HY r q ↔ x ∈ G.HR ∧ ∃ u ∈ Y r q, G.adj u x = true :=
    fun r q x ↦ by rw [hHY, mem_filter]
  refine ⟨M, hMpos, fun r ↦ G.e1 ++
    (List.range s).map fun q ↦ ⟨Y r q ∪ Hq q, Zq q ∪ HY r q⟩, fun r ↦ ?_, ?_⟩
  · refine good_e1_append (by omega) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hσ
      refine ⟨union_subset (fun u hu ↦ ?_) (fun u hu ↦ ?_),
        union_subset (fun v hv ↦ ?_) (fun v hv ↦ ?_)⟩
      · have := hY1 r q hu
        exact mem_sdiff.2 ⟨(mem_LF.1 this).1, LF_not_E1L this⟩
      · have := hHSHL ((memHq q u).1 hu).1
        exact mem_sdiff.2 ⟨(mem_HL.1 this).1, HL_not_E1L this⟩
      · have := ((memZq q v).1 hv).1
        exact mem_sdiff.2 ⟨(mem_RF.1 this).1, RF_not_E1R this⟩
      · have := ((memHY r q v).1 hv).1
        exact mem_sdiff.2 ⟨(mem_HR.1 this).1, HR_not_E1R this⟩
    · intro σ hσ
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hσ
      rw [List.mem_range] at hq
      have hdisj : Disjoint (Y r q) (Hq q) := disjoint_left.2 fun u h1 h2 ↦
        LF_not_HL (hY1 r q h1) (hHSHL ((memHq q u).1 h2).1)
      change (Zq q ∪ HY r q).card ≤ (Y r q ∪ Hq q).card ∧ (Y r q ∪ Hq q).card ≤ 24 * N
      rw [card_union_of_disjoint hdisj]
      have h1 := card_union_le (Zq q) (HY r q)
      have h2 := hY2 r q hq (HY r q) fun x hx ↦ (memHY r q x).1 hx
      have h3 := hY3 r q hq
      have h4 := hHZ q
      have h5 := hZcard q
      have h6 := hw q
      constructor <;> omega
    · intro σ hσ u hu v hv h
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hσ
      rcases mem_union.1 hu with hu | hu
      · exact mem_union_right _ ((memHY r q v).2 ⟨LF_adj (hY1 r q hu) hv h, u, hu, h⟩)
      · obtain ⟨huS, huq⟩ := (memHq q u).1 hu
        have hvn : v ∈ G.nbR u := mem_nbR.2 ⟨hv, h⟩
        exact mem_union_left _ ((memZq q v).2
          ⟨nbR_subset_RF hG (hHSHL huS) hvn, (hφRH u huS v hvn).trans huq⟩)
    · intro v hv
      obtain ⟨hvR, hvE⟩ := mem_sdiff.1 hv
      rcases mem_R_cases hvR with h | h | h
      · exact absurd h hvE
      · obtain ⟨u, hu⟩ : (G.nbL v).Nonempty := card_pos.1 (by
          have := (mem_HR.1 h).2
          rw [degR_eq] at this
          omega)
        obtain ⟨q, hq, huY⟩ := hY4 r u (nbL_subset_LF hG h hu)
        exact ⟨_, List.mem_map.2 ⟨q, List.mem_range.2 hq, rfl⟩,
          mem_union_right _ ((memHY r q v).2 ⟨h, u, huY, (mem_nbL.1 hu).2⟩)⟩
      · have := hφR v h
        exact ⟨_, List.mem_map.2 ⟨φR v, List.mem_range.2 (by omega), rfl⟩,
          mem_union_left _ ((memZq _ v).2 ⟨h, rfl⟩)⟩
    · intro u hu hd
      obtain ⟨huL, huE⟩ := mem_sdiff.1 hu
      rcases mem_L_cases huL with h | h | h
      · exact absurd h huE
      · have huS : u ∈ HS := (memHS u).2 ⟨h, hd⟩
        have := hφH u huS
        exact ⟨_, List.mem_map.2 ⟨φH u, List.mem_range.2 (by omega), rfl⟩,
          mem_union_right _ ((memHq _ u).2 ⟨huS, rfl⟩)⟩
      · obtain ⟨q, hq, huY⟩ := hY4 r u h
        exact ⟨_, List.mem_map.2 ⟨q, List.mem_range.2 hq, rfl⟩, mem_union_left _ huY⟩
    · intro u hu hd
      rw [countP_map_range]
      refine card_le_one.2 fun q hq q' hq' ↦ ?_
      simp only [mem_filter] at hq hq'
      have hnY : ∀ q, u ∉ Y r q := fun q h ↦ by
        have := (mem_LF.1 (hY1 r q h)).2.1
        omega
      rcases mem_union.1 hq.2 with h | h
      · exact absurd h (hnY q)
      rcases mem_union.1 hq'.2 with h' | h'
      · exact absurd h' (hnY q')
      exact ((memHq q u).1 h).2.symm.trans ((memHq q' u).1 h').2
    · intro v hv hd
      rw [countP_map_range]
      refine card_le_one.2 fun q hq q' hq' ↦ ?_
      simp only [mem_filter] at hq hq'
      have hnH : ∀ q, v ∉ HY r q := fun q h ↦ by
        have := (mem_HR.1 ((memHY r q v).1 h).1).2
        omega
      rcases mem_union.1 hq.2 with h | h
      · rcases mem_union.1 hq'.2 with h' | h'
        · exact ((memZq q v).1 h).2.symm.trans ((memZq q' v).1 h').2
        · exact absurd h' (hnH q')
      · exact absurd h (hnH q)
    · rw [List.length_map, List.length_range]
      have := Nat.div_le_self G.RF.card N
      omega
  · intro u hu hd
    beta_reduce
    have hRF2M : G.RF.card ≤ 2 * M := by omega
    have hX : ∑ q ∈ range s, w q - E ≤ HB.card + p + 1 := by omega
    have hnum := numeric_bound (by omega) hRF2M h2NHB hNp hX
    have hN' : (0 : ℝ) < N := by positivity
    have hnumR : (N : ℝ) * (2 * (∑ q ∈ range s, w q - E : ℕ)) ≤ 8 * M := by
      exact_mod_cast hnum
    rcases mem_L_cases hu with h | h | h
    · have hcnt : ∀ r : Fin M, ((G.e1 ++ (List.range s).map fun q ↦
          (⟨Y r q ∪ Hq q, Zq q ∪ HY r q⟩ : Swap α β)).countP fun σ ↦ decide (u ∈ σ.Ls)) = 1 := by
        intro r
        rw [List.countP_append, countP_e1_L, countP_map_range]
        have : #{q ∈ range s | u ∈ Y r q ∪ Hq q} = 0 := card_eq_zero.2
          (filter_eq_empty_iff.2 fun q _ hq ↦ by
            rcases mem_union.1 hq with h' | h'
            · exact LF_not_E1L (hY1 _ _ h') h
            · exact HL_not_E1L (hHSHL ((memHq q u).1 h').1) h)
        simp only [h, ↓reduceIte]
        rw [this]
      simp only [hcnt, Nat.cast_one, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]
      have : (0 : ℝ) ≤ 8 / N := by positivity
      nlinarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    · have := (mem_HL.1 h).2
      omega
    · have hcnt : ∀ r : Fin M, ((G.e1 ++ (List.range s).map fun q ↦
          (⟨Y r q ∪ Hq q, Zq q ∪ HY r q⟩ : Swap α β)).countP fun σ ↦ decide (u ∈ σ.Ls)) =
          #{q ∈ range s | u ∈ Y r q} := by
        intro r
        rw [List.countP_append, countP_e1_L, countP_map_range]
        simp only [LF_not_E1L h, ↓reduceIte, zero_add]
        exact congrArg card (filter_congr fun q _ ↦ ⟨fun h' ↦ (mem_union.1 h').resolve_right
          fun h'' ↦ LF_not_HL h (hHSHL ((memHq q u).1 h'').1), fun h' ↦ mem_union_left _ h'⟩)
      have hsumN : ∑ r : Fin M, #{q ∈ range s | u ∈ Y r q} ≤
          M + 2 * (∑ q ∈ range s, w q - E) := by
        rw [Fin.sum_univ_eq_sum_range (fun r ↦ #{q ∈ range s | u ∈ Y r q}) M]
        exact hY5 u h
      have hsumR : ∑ r : Fin M, (#{q ∈ range s | u ∈ Y r q} : ℝ) ≤
          M + 2 * (∑ q ∈ range s, w q - E : ℕ) := by
        have := (Nat.cast_le (α := ℝ)).2 hsumN
        simpa [Nat.cast_sum] using this
      simp only [hcnt]
      have h8 : (2 * (∑ q ∈ range s, w q - E : ℕ) : ℝ) ≤ 8 / N * M := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hN']
        linarith
      linarith

end BiGraph

namespace BiGraph

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (G : BiGraph α β)

end BiGraph

end BCFGJPSSV26.Stable


