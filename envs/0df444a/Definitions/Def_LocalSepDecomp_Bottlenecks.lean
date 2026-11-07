-- Prove2me | Definitions.Def_LocalSepDecomp_Bottlenecks
-- name    : LocalSepDecomp_Bottlenecks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:41:34.627632+00:00
-- url     : https://prove2.me/theorems/a46eaa27-5dcd-4369-b9e3-4741bb9fce72
-- title:
--   Tri-stars, bottlenecks, $r$-local bottlenecks and the nested sets $N^k(G)$, $N^k_r(G)$ of Constructions 3.6 and 7.16
-- statement:
--   1. A **tri-star** is a set of three distinct oriented separations $(A_i,B_i)$ with $B_i=A_j\cup A_k$ for $\{i,j,k\}=[3]$. With $X_i=A_i\cap B_i$, centre $Z=\bigcap X_i$ and links $X_{ij}=(X_i\cap X_j)\setminus Z$, it is **relevant with base** $\{A_1,B_1\}$ if $\{A_1,B_1\}$ is tight; for every $x\in X_{23}$ and $i\in\{2,3\}$ there is an $x$–$X_{1i}$ edge or a vertex $y\in X_{1i}\cup Z$ and a component $K$ of $G[A_i\setminus B_i]$ with $x,y\in N(K)$; and no edge joins $X_{12}$ and $X_{13}$.
--   2. A **bottleneck of order $k$** is a non-empty set $\beta$ of tight $k$-separations such that whenever $\beta$ contains the base of a relevant tri-star of order $\le k$, it contains one of its other two constituents.
--   3. An **$r$-local tri-star** is a set of three oriented $r$-local separations $(E_i,X_i,F_i)$ whose $E_i$ near-partition $\partial(\bigcup X_i)$, such that every vertex of an $X_i$ lies in another $X_j$ and every $r$-local component at $\bigcup X_i$ lies in some $E_i$. Relevance and **$r$-local bottlenecks** are defined as above, with "a component $K$ of $G[A_i\setminus B_i]$" replaced by "an $r$-local component $F\subseteq E_i$ at $X$ with an edge at $x$ and an edge at $X_{1i}\cup Z$".
--   4. **Construction 3.6 / 7.16.** Given a set $\mathcal B$ of (r-local) bottlenecks, let $\mathcal B^k$ be its $k$-bottlenecks and $S_k=\bigcup\mathcal B^k$. Recursively, with $N^{<k}=\bigcup_{j<k}N^j$ and $x_k(s)$ the number of elements of $S_k$ crossed by $s$,
--   $$N^k(G,\beta)=\{s\in\beta:\ s\text{ nested with }N^{<k},\ x_k(s)\text{ minimal among those}\},\qquad N^k(G)=\bigcup_{\beta\in\mathcal B^k}N^k(G,\beta),$$
--   and $N(G)=\bigcup_kN^k(G)$, $N^{\le k}=N^{<k}\cup N^k$. In §9, $N^{\le k}_r(G)$ is built from the set of all $r$-local bottlenecks of order $\le k$.
--
--   Bottlenecks axiomatise the minimum-order separations between two tangles using only separations of order $\le k$; this is what makes the order-by-order construction possible.
--
--   **Formalization Note** Tri-stars are indexed by $\mathrm{Fin}\,3$ with the base at index $0$. The two constructions are one recursion over an abstract crossing relation; crossing numbers are cardinals in $\mathbb N_\infty$.
-- source:
--   Jacobs, Knappe, Kurkofka, Canonical Graph Decompositions via Local Separations, preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), §3.1–3.2 (pp.18–21), §7.1 (p.42), §7.3 (pp.45–46), §9 (p.56)

import Mathlib
import Definitions.Def_LocalSepDecomp_Crossing

set_option autoImplicit false

namespace LocalSepDecomp

/-! # Tri-stars, bottlenecks (global and r-local) and the nested sets of Constructions 3.6 and
7.16

R. W. Jacobs, P. Knappe, J. Kurkofka, *Canonical Graph Decompositions via Local Separations*,
preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), §3.1–3.2 (pp.18–21),
§7.1 (p.42), §7.3 (pp.45–46).

**Formalization Note.**
1. A (local) tri-star `σ = {s₁, s₂, s₃}` relevant with base `s₁` is indexed as `σ : Fin 3 → _`
   (injective: three distinct elements), with the base at index `0`; the paper's indices
   `1, 2, 3` are `0, 1, 2`. Axiom (B)/(Bᵣ) quantifies over all such indexed tri-stars, which
   covers every tri-star with every choice of base.
2. Constructions 3.6 and 7.16 are one recursion, `belowN`, for an abstract crossing relation and
   a family `k ↦ B^k` of sets of `k`-bottlenecks: `belowN k = N^{<k}`, `stepN k (N^{<k}) = N^k`,
   `stepAtN … β = N^k(G, β)`. The crossing number `x_k(s)` is a cardinal in `ℕ∞` (the paper
   assumes it finite; "well-defined" means finite). -/

open SimpleGraph

variable {V : Type*}

/-! ## Global tri-stars and bottlenecks (§3.1) -/

/-- The separator `Xᵢ = Aᵢ ∩ Bᵢ` of the `i`-th element of an indexed triple of separations. -/
def triSep (σ : Fin 3 → Set V × Set V) (i : Fin 3) : Set V := (σ i).1 ∩ (σ i).2

/-- The centre `Z = ⋂ᵢ Xᵢ` of a tri-star (p.18). -/
def triCentre (σ : Fin 3 → Set V × Set V) : Set V := ⋂ i, triSep σ i

/-- The `ij`-link `Xᵢⱼ = (Xᵢ ∩ Xⱼ) ∖ Z` of a tri-star (p.18). -/
def triLink (σ : Fin 3 → Set V × Set V) (i j : Fin 3) : Set V :=
  (triSep σ i ∩ triSep σ j) \ triCentre σ

/-- A **tri-star** of `G` (p.18): three distinct oriented separations `(Aᵢ, Bᵢ)` with
`Bᵢ = Aⱼ ∪ A_k` whenever `{i, j, k} = [3]`. -/
def IsTriStar (G : SimpleGraph V) (σ : Fin 3 → Set V × Set V) : Prop :=
  Function.Injective σ ∧ (∀ i, IsSep G (σ i)) ∧
    ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k → (σ i).2 = (σ j).1 ∪ (σ k).1

/-- A tri-star is **relevant with base `{A₁, B₁}`** (pp.18–19; base at index `0`):
`{A₁, B₁}` is tight; for every `x ∈ X₂₃` and `i ∈ {2, 3}` there is an `x`–`X₁ᵢ` edge, or there are
`y ∈ X₁ᵢ ∪ Z` and a component `K` of `G[Aᵢ ∖ Bᵢ]` with `x, y ∈ N(K)`; and there is no edge between
the links `X₁₂` and `X₁₃`. -/
def IsRelevantTriStar (G : SimpleGraph V) (σ : Fin 3 → Set V × Set V) : Prop :=
  IsTriStar G σ ∧ IsTightSep G (σ 0) ∧
    (∀ x ∈ triLink σ 1 2, ∀ i : Fin 3, i ≠ 0 →
      (∃ y ∈ triLink σ 0 i, G.Adj x y) ∨
        ∃ y ∈ triLink σ 0 i ∪ triCentre σ, ∃ K, IsCompOn G ((σ i).1 \ (σ i).2) K ∧
          x ∈ nbhd G K ∧ y ∈ nbhd G K) ∧
    ∀ x ∈ triLink σ 0 1, ∀ y ∈ triLink σ 0 2, ¬ G.Adj x y

/-- A **bottleneck of order `k`** (`k`-bottleneck) in `G` (p.20): a non-empty set `β` of tight
unoriented `k`-separations such that (B): whenever `β` contains the base of a relevant tri-star
of order `≤ k`, it contains one of the other two constituents. -/
def IsBottleneck (G : SimpleGraph V) (k : ℕ) (β : Set (Sym2 (Set V))) : Prop :=
  β.Nonempty ∧ (∀ u ∈ β, IsTightUSep G u ∧ usepOrder u = k) ∧
    ∀ σ : Fin 3 → Set V × Set V, IsRelevantTriStar G σ → (∀ i, sepOrder (σ i) ≤ k) →
      unorientSep (σ 0) ∈ β → unorientSep (σ 1) ∈ β ∨ unorientSep (σ 2) ∈ β

/-- A set `B` of bottlenecks is **`Γ`-invariant** (p.21): the action of `Γ` on bottlenecks
(inherited from separations) leaves `B` invariant. -/
def IsInvariantBottleneckSet (G : SimpleGraph V) (Γ : Subgroup (G ≃g G))
    (B : Set (Set (Sym2 (Set V)))) : Prop :=
  ∀ φ ∈ Γ, ∀ β ∈ B, usepMap φ '' β ∈ B

/-! ## r-local tri-stars and r-local bottlenecks (§7.1, §7.3) -/

/-- The union `X = ⋃ᵢ Xᵢ` of the separators of an indexed triple of `r`-local separations. -/
def ltriUnion (σ : Fin 3 → LSep V) : Set V := ⋃ i, (σ i).X

/-- The centre `Z = ⋂ᵢ Xᵢ` (p.42). -/
def ltriCentre (σ : Fin 3 → LSep V) : Set V := ⋂ i, (σ i).X

/-- The `ij`-link `Xᵢⱼ = (Xᵢ ∩ Xⱼ) ∖ Z` (p.42). -/
def ltriLink (σ : Fin 3 → LSep V) (i j : Fin 3) : Set V :=
  ((σ i).X ∩ (σ j).X) \ ltriCentre σ

/-- An **`r`-local tri-star** in `G` (p.42): three distinct oriented `r`-local separations
`(Eᵢ, Xᵢ, Fᵢ)` such that (LY1) the `Eᵢ` near-partition `∂(⋃ Xᵢ)`, (LY2) every vertex of some
`Xᵢ` lies in at least one other `Xⱼ`, and (LY3) every `r`-local component at `⋃ Xᵢ` is included
in some `Eᵢ`. -/
def IsLTriStar (G : SimpleGraph V) (r : ℕ) (σ : Fin 3 → LSep V) : Prop :=
  Function.Injective σ ∧ (∀ i, IsLSep G r (σ i)) ∧
    ((∀ i j, i ≠ j → Disjoint (σ i).E₁ (σ j).E₁) ∧
      (⋃ i, (σ i).E₁) = boundary G (ltriUnion σ)) ∧
    (∀ i, ∀ v ∈ (σ i).X, ∃ j, j ≠ i ∧ v ∈ (σ j).X) ∧
    ∀ F, IsRLocalComponent G r (ltriUnion σ) F → ∃ i, F ⊆ (σ i).E₁

/-- An `r`-local tri-star is **relevant with base `{E₁, X₁, F₁}`** (p.42; base at index `0`):
`{E₁, X₁, F₁}` is tight; for every `x ∈ X₂₃` and `i ∈ {2, 3}` there is an `x`–`X₁ᵢ` edge, or an
`r`-local component `F ⊆ Eᵢ` at `X` containing an edge at `x` and an edge at `X₁ᵢ ∪ Z`; and there
is no edge between `X₁₂` and `X₁₃`. -/
def IsRelevantLTriStar (G : SimpleGraph V) (r : ℕ) (σ : Fin 3 → LSep V) : Prop :=
  IsLTriStar G r σ ∧ IsTightLSep G r (σ 0) ∧
    (∀ x ∈ ltriLink σ 1 2, ∀ i : Fin 3, i ≠ 0 →
      (∃ y ∈ ltriLink σ 0 i, G.Adj x y) ∨
        ∃ F, IsRLocalComponent G r (ltriUnion σ) F ∧ F ⊆ (σ i).E₁ ∧ (∃ e ∈ F, x ∈ e) ∧
          ∃ e ∈ F, ∃ y ∈ ltriLink σ 0 i ∪ ltriCentre σ, y ∈ e) ∧
    ∀ x ∈ ltriLink σ 0 1, ∀ y ∈ ltriLink σ 0 2, ¬ G.Adj x y

/-- An **`r`-local bottleneck of order `k`** in `G` (p.45): a non-empty set `β` of tight
`r`-local `k`-separations such that (Bᵣ): whenever `β` contains the base of a relevant `r`-local
tri-star of order `≤ k`, it contains one of the other two constituents. -/
def IsLocalBottleneck (G : SimpleGraph V) (r k : ℕ) (β : Set (ULSep V)) : Prop :=
  β.Nonempty ∧ (∀ u ∈ β, IsTightULSep G r u ∧ u.order = k) ∧
    ∀ σ : Fin 3 → LSep V, IsRelevantLTriStar G r σ → (∀ i, (σ i).X.encard ≤ k) →
      (σ 0).unorient ∈ β → (σ 1).unorient ∈ β ∨ (σ 2).unorient ∈ β

/-- A set `B_r` of `r`-local bottlenecks is **`Γ`-invariant** (p.46). -/
def IsInvariantLBottleneckSet (G : SimpleGraph V) (Γ : Subgroup (G ≃g G))
    (B : Set (Set (ULSep V))) : Prop :=
  ∀ φ ∈ Γ, ∀ β ∈ B, ULSep.map φ '' β ∈ B

/-- The image `β_r = {s_r : s ∈ β}` of a set of separations (Correspondence 7.13, p.46). -/
def bottleneckToLocal (G : SimpleGraph V) (β : Set (Sym2 (Set V))) : Set (ULSep V) :=
  usepToULSep G '' β

/-! ## The recursion of Constructions 3.6 and 7.16 -/

section Construction

variable {α : Type*}

/-- `x_k(s)`: the number of elements of `S` that `s` crosses, in `ℕ∞`. -/
noncomputable def crossCount (crosses : α → α → Prop) (S : Set α) (s : α) : ℕ∞ :=
  {t ∈ S | crosses s t}.encard

/-- `N^k(G, β)`: the elements `s ∈ β` nested with `P = N^{<k}` that, among those, have minimal
`x_k(s)`, where `x_k` counts crossings within `S_k = ⋃ B^k`. -/
def stepAtN (crosses : α → α → Prop) (Bk : ℕ → Set (Set α)) (k : ℕ) (P β : Set α) : Set α :=
  {s | s ∈ β ∧ (∀ t ∈ P, ¬ crosses s t) ∧
    ∀ s' ∈ β, (∀ t ∈ P, ¬ crosses s' t) →
      crossCount crosses (⋃₀ Bk k) s ≤ crossCount crosses (⋃₀ Bk k) s'}

/-- `N^k(G) = ⋃ { N^k(G, β) : β ∈ B^k }`, given `P = N^{<k}`. -/
def stepN (crosses : α → α → Prop) (Bk : ℕ → Set (Set α)) (k : ℕ) (P : Set α) : Set α :=
  ⋃ β ∈ Bk k, stepAtN crosses Bk k P β

/-- `N^{<k}(G) = ⋃_{j<k} N^j(G)`, by recursion on `k`. -/
def belowN (crosses : α → α → Prop) (Bk : ℕ → Set (Set α)) : ℕ → Set α
  | 0 => ∅
  | k + 1 => belowN crosses Bk k ∪ stepN crosses Bk k (belowN crosses Bk k)

end Construction

/-! ### Construction 3.6 (global) -/

/-- `B^k(G)`: the `k`-bottlenecks in `B` (p.21). -/
def globalBk (G : SimpleGraph V) (B : Set (Set (Sym2 (Set V)))) (k : ℕ) :
    Set (Set (Sym2 (Set V))) :=
  {β | β ∈ B ∧ IsBottleneck G k β}

/-- `x_k(s)` of Construction 3.6: the number of separations in `S_k = ⋃ B^k(G)` crossed by `s`. -/
noncomputable def xk (G : SimpleGraph V) (B : Set (Set (Sym2 (Set V)))) (k : ℕ)
    (s : Sym2 (Set V)) : ℕ∞ :=
  crossCount USepCrosses (⋃₀ globalBk G B k) s

/-- `N^{<k}(G)` of Construction 3.6 for the set `B` of bottlenecks. -/
def Nlt (G : SimpleGraph V) (B : Set (Set (Sym2 (Set V)))) (k : ℕ) : Set (Sym2 (Set V)) :=
  belowN USepCrosses (globalBk G B) k

/-- `N^k(G, β)` of Construction 3.6. -/
def NkAt (G : SimpleGraph V) (B : Set (Set (Sym2 (Set V)))) (k : ℕ) (β : Set (Sym2 (Set V))) :
    Set (Sym2 (Set V)) :=
  stepAtN USepCrosses (globalBk G B) k (Nlt G B k) β

/-- `N^k(G)` of Construction 3.6. -/
def Nk (G : SimpleGraph V) (B : Set (Set (Sym2 (Set V)))) (k : ℕ) : Set (Sym2 (Set V)) :=
  stepN USepCrosses (globalBk G B) k (Nlt G B k)

/-- `N(G) = ⋃_k N^k(G)` of Construction 3.6. -/
def Nall (G : SimpleGraph V) (B : Set (Set (Sym2 (Set V)))) : Set (Sym2 (Set V)) :=
  ⋃ k, Nk G B k

/-! ### Construction 7.16 (r-local) -/

/-- `B^k_r(G)`: the `r`-local `k`-bottlenecks in `B_r` (p.46). -/
def localBk (G : SimpleGraph V) (r : ℕ) (B : Set (Set (ULSep V))) (k : ℕ) :
    Set (Set (ULSep V)) :=
  {β | β ∈ B ∧ IsLocalBottleneck G r k β}

/-- `x^k_r(s)` of Construction 7.16. -/
noncomputable def lxk (G : SimpleGraph V) (r : ℕ) (B : Set (Set (ULSep V))) (k : ℕ)
    (s : ULSep V) : ℕ∞ :=
  crossCount (ULCrosses G r) (⋃₀ localBk G r B k) s

/-- `N^{<k}_r(G)` of Construction 7.16 for the set `B_r`. -/
def LNlt (G : SimpleGraph V) (r : ℕ) (B : Set (Set (ULSep V))) (k : ℕ) : Set (ULSep V) :=
  belowN (ULCrosses G r) (localBk G r B) k

/-- `N^k_r(G, β)` of Construction 7.16. -/
def LNkAt (G : SimpleGraph V) (r : ℕ) (B : Set (Set (ULSep V))) (k : ℕ) (β : Set (ULSep V)) :
    Set (ULSep V) :=
  stepAtN (ULCrosses G r) (localBk G r B) k (LNlt G r B k) β

/-- `N^k_r(G)` of Construction 7.16. -/
def LNk (G : SimpleGraph V) (r : ℕ) (B : Set (Set (ULSep V))) (k : ℕ) : Set (ULSep V) :=
  stepN (ULCrosses G r) (localBk G r B) k (LNlt G r B k)

/-- `N^{≤k}_r(G) = N^{<k}_r(G) ∪ N^k_r(G)` (p.12). -/
def LNle (G : SimpleGraph V) (r : ℕ) (B : Set (Set (ULSep V))) (k : ℕ) : Set (ULSep V) :=
  LNlt G r B k ∪ LNk G r B k

/-- The set of all `r`-local bottlenecks of `G` (of any order). -/
def allLBottlenecks (G : SimpleGraph V) (r : ℕ) : Set (Set (ULSep V)) :=
  {β | ∃ k, IsLocalBottleneck G r k β}

/-- The set of all `r`-local bottlenecks of `G` of order `≤ k` (§9, p.56). -/
def lBottlenecksLe (G : SimpleGraph V) (r k : ℕ) : Set (Set (ULSep V)) :=
  {β | ∃ j ≤ k, IsLocalBottleneck G r j β}

/-- `N^{≤k}_r(G)` as in §9 (p.56): Construction 7.16 with `B_r` the set of all `r`-local
bottlenecks of order `≤ k`. -/
def NleSec9 (G : SimpleGraph V) (r k : ℕ) : Set (ULSep V) :=
  LNle G r (lBottlenecksLe G r k) k

end LocalSepDecomp


