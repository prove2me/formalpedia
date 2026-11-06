-- Prove2me | Definitions.Def_LogStarBinPacking_ThreeItem
-- name    : LogStarBinPacking_ThreeItem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:30:17.643113+00:00
-- url     : https://prove2.me/theorems/37627fb9-8ca0-4116-be44-bc4115a22725
-- title:
--   The three-item instance $J$: item classes, scores (2.3)–(2.4) and sizes (2.5)
-- statement:
--   Fix the data of Lemma 2.1: an instance $I$ with $n$ items, an integer $b\ge1$, a finite state set $V$ with $|V|\ge n+b$, loads $h:V\to[0,1]\cap\mathbb Q$ and a rational $\varepsilon>0$. Put $M=|V|+b$ and $f=|V|-n-b$. The instance $J$ has eight pairwise disjoint classes of items:
--   $$
--   S^+_v,\ S^-_v\ (v\in V),\quad X_i\ (i\in I),\quad X^0_r\ (1\le r\le f),\quad E^-_{j,1},E^-_{j,2},E^+_{j,1},E^+_{j,2}\ (1\le j\le b).
--   $$
--   Each item $u$ has a **type score** $p_1(u)\in\mathbb Z$ and a **load score** $p_2(u)\in\mathbb Q$:
--
--   | item | $S^+_v$ | $S^-_v$ | $X_i$ | $X^0_r$ | $E^-_{j,1}$ | $E^-_{j,2}$ | $E^+_{j,1}$ | $E^+_{j,2}$ |
--   |---|---|---|---|---|---|---|---|---|
--   | $p_1$ | $-4$ | $-1$ | $5$ | $5$ | $-3$ | $4$ | $1$ | $3$ |
--   | $p_2$ | $h(v)$ | $-h(v)$ | $s_I(i)$ | $0$ | $0$ | $0$ | $0$ | $-1$ |
--
--   With $\lambda=\min\{\varepsilon/6,\,1/100\}$ the sizes are
--   $$
--   s_J(u)=\frac13+\lambda\Big(p_1(u)+\frac{p_2(u)}4\Big).
--   $$
--   The **class pattern** of $U\subseteq J$ is the multiset of the classes of its items; the patterns (2.8) are $S^+S^-X$, $S^+S^-X^0$, $S^-E^-_1E^-_2$, $S^+E^+_1E^+_2$. For a state path $\pi=(v_0,i_1,\dots,i_k,v_k)$ and $1\le j\le b$,
--   $$
--   T_j(\pi)=\big\{\{S^-_{v_0},E^-_{j,1},E^-_{j,2}\},\{S^+_{v_k},E^+_{j,1},E^+_{j,2}\}\big\}\cup\big\{\{S^+_{v_{\ell-1}},X_{i_\ell},S^-_{v_\ell}\}:1\le\ell\le k\big\}.
--   $$
--   For a packing of $J$, $B^*$ is the set of its bins with exactly three items and type score $0$.
--
--   The scores are chosen so that $p_1(J)=0$ and the intended triples are exactly the feasible triples of type score zero; this lets a packing with few extra bins be decoded into a packing of $I$.
--
--   **Formalization Note** `ThreeItem V n f b` has one constructor per class with 0-based indices. `jInstance` is $J$ as a bin packing instance, listing its items through `Fintype.equivFin` (OPT and LP do not depend on the order); it takes $\varepsilon>0$ and $h(V)\subseteq[0,1]$ as arguments, which make every size lie in $(0,1]$. The bundle holds the scores, sizes, patterns, the triples $T_j(\pi)$ and the bins $B^*$ of a packing.
-- source:
--   I. Doron-Arad, Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin, manuscript (sha256 1d88425d…), proof of Lemma 2.1, (2.3)–(2.5), (2.8)–(2.9), pp.4–5; proof of Claim 2.5, p.7

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_LogStarBinPacking_StatePath

namespace LogStarBinPacking

open OAI.BinPackingGap

/-- **The items of the three-item instance `J`.** Doron-Arad, *Additive Ω(log∗ OPT) Gap for Bin
Packing with Three Items per Bin*, manuscript (sha256 1d88425d…), proof of Lemma 2.1, p.4. The
eight pairwise disjoint classes are `S⁺ = {S⁺_v : v ∈ V}`, `S⁻ = {S⁻_v : v ∈ V}`,
`X = {X_i : i ∈ I}`, `X⁰ = {X⁰_r : 1 ≤ r ≤ f}` and `E^δ_ℓ = {E^δ_{j,ℓ} : 1 ≤ j ≤ b}` for
`δ ∈ {−, +}`, `ℓ ∈ {1, 2}`.

**Formalization Note** `ThreeItem V n f b` has one constructor per class: `sPlus v = S⁺_v`,
`sMinus v = S⁻_v`, `src i = X_i` (`i : Fin n`, the items of `I`), `filler r = X⁰_{r+1}`
(`r : Fin f`), `eMinus1 j = E⁻_{j+1,1}`, `eMinus2 j = E⁻_{j+1,2}`, `ePlus1 j = E⁺_{j+1,1}`,
`ePlus2 j = E⁺_{j+1,2}` (`j : Fin b`). Indices are `0`-based. The bundle also holds the scores
(2.3)–(2.4), the sizes (2.5), the class patterns (2.8), the triples `T_j(π)` (2.9) and the
instance `J` built from them. -/
inductive ThreeItem (V : Type*) (n f b : ℕ) where
  | sPlus (v : V)
  | sMinus (v : V)
  | src (i : Fin n)
  | filler (r : Fin f)
  | eMinus1 (j : Fin b)
  | eMinus2 (j : Fin b)
  | ePlus1 (j : Fin b)
  | ePlus2 (j : Fin b)
  deriving DecidableEq

namespace ThreeItem

variable {V : Type*} {n f b : ℕ}

/-- The sum-type form of an item, used to give `ThreeItem` a `Fintype` structure. -/
def toSum : ThreeItem V n f b →
    (V ⊕ V) ⊕ (Fin n ⊕ Fin f) ⊕ ((Fin b ⊕ Fin b) ⊕ (Fin b ⊕ Fin b))
  | sPlus v => .inl (.inl v)
  | sMinus v => .inl (.inr v)
  | src i => .inr (.inl (.inl i))
  | filler r => .inr (.inl (.inr r))
  | eMinus1 j => .inr (.inr (.inl (.inl j)))
  | eMinus2 j => .inr (.inr (.inl (.inr j)))
  | ePlus1 j => .inr (.inr (.inr (.inl j)))
  | ePlus2 j => .inr (.inr (.inr (.inr j)))

/-- Inverse of `toSum`. -/
def ofSum : (V ⊕ V) ⊕ (Fin n ⊕ Fin f) ⊕ ((Fin b ⊕ Fin b) ⊕ (Fin b ⊕ Fin b)) →
    ThreeItem V n f b
  | .inl (.inl v) => sPlus v
  | .inl (.inr v) => sMinus v
  | .inr (.inl (.inl i)) => src i
  | .inr (.inl (.inr r)) => filler r
  | .inr (.inr (.inl (.inl j))) => eMinus1 j
  | .inr (.inr (.inl (.inr j))) => eMinus2 j
  | .inr (.inr (.inr (.inl j))) => ePlus1 j
  | .inr (.inr (.inr (.inr j))) => ePlus2 j

/-- `ThreeItem V n f b` is the disjoint union of its eight classes. -/
def equivSum : ThreeItem V n f b ≃
    (V ⊕ V) ⊕ (Fin n ⊕ Fin f) ⊕ ((Fin b ⊕ Fin b) ⊕ (Fin b ⊕ Fin b)) where
  toFun := toSum
  invFun := ofSum
  left_inv u := by cases u <;> rfl
  right_inv s := by
    rcases s with (v | v) | (i | r) | ((j | j) | (j | j)) <;> rfl

instance instFintype [Fintype V] : Fintype (ThreeItem V n f b) :=
  Fintype.ofEquiv _ equivSum.symm

/-- The eight item classes `S⁺, S⁻, X, X⁰, E⁻₁, E⁻₂, E⁺₁, E⁺₂`. -/
inductive Cls where
  | sPlus | sMinus | src | filler | eMinus1 | eMinus2 | ePlus1 | ePlus2
  deriving DecidableEq

/-- The class of an item. -/
def cls : ThreeItem V n f b → Cls
  | sPlus _ => .sPlus
  | sMinus _ => .sMinus
  | src _ => .src
  | filler _ => .filler
  | eMinus1 _ => .eMinus1
  | eMinus2 _ => .eMinus2
  | ePlus1 _ => .ePlus1
  | ePlus2 _ => .ePlus2

/-- **Type score `p₁`** (2.3)–(2.4), p.4–5: `p₁(S⁺_v) = −4`, `p₁(S⁻_v) = −1`, `p₁(X_i) = 5`,
`p₁(g) = 5` for `g ∈ X⁰`, `p₁(E⁻_{j,1}) = −3`, `p₁(E⁻_{j,2}) = 4`, `p₁(E⁺_{j,1}) = 1`,
`p₁(E⁺_{j,2}) = 3`. -/
def typeScore : ThreeItem V n f b → ℤ
  | sPlus _ => -4
  | sMinus _ => -1
  | src _ => 5
  | filler _ => 5
  | eMinus1 _ => -3
  | eMinus2 _ => 4
  | ePlus1 _ => 1
  | ePlus2 _ => 3

/-- **Load score `p₂`** (2.3)–(2.4), p.4–5: `p₂(S⁺_v) = h(v)`, `p₂(S⁻_v) = −h(v)`,
`p₂(X_i) = s_I(i)`, `p₂(g) = 0` for `g ∈ X⁰`, `p₂(E⁻_{j,1}) = p₂(E⁻_{j,2}) = p₂(E⁺_{j,1}) = 0`,
`p₂(E⁺_{j,2}) = −1`. -/
def loadScore (sI : Fin n → ℚ) (h : V → ℚ) : ThreeItem V n f b → ℚ
  | sPlus v => h v
  | sMinus v => -h v
  | src i => sI i
  | filler _ => 0
  | eMinus1 _ => 0
  | eMinus2 _ => 0
  | ePlus1 _ => 0
  | ePlus2 _ => -1

/-- The scale `λ = min{ε/6, 1/100}` of (2.5), p.5. -/
def scale (ε : ℚ) : ℚ := min (ε / 6) (1 / 100)

/-- **Item size (2.5)**, p.5: `s_J(u) = 1/3 + λ (p₁(u) + p₂(u)/4)` with `λ = min{ε/6, 1/100}`. -/
def size (sI : Fin n → ℚ) (h : V → ℚ) (ε : ℚ) (u : ThreeItem V n f b) : ℚ :=
  1 / 3 + scale ε * ((typeScore u : ℚ) + loadScore sI h u / 4)

theorem typeScore_bounds (u : ThreeItem V n f b) : -4 ≤ typeScore u ∧ typeScore u ≤ 5 := by
  cases u <;> simp [typeScore]

theorem loadScore_bounds (sI : Fin n → ℚ) (h : V → ℚ) (hs0 : ∀ i, 0 ≤ sI i)
    (hs1 : ∀ i, sI i ≤ 1) (h0 : ∀ v, 0 ≤ h v) (h1 : ∀ v, h v ≤ 1)
    (u : ThreeItem V n f b) : -1 ≤ loadScore sI h u ∧ loadScore sI h u ≤ 1 := by
  cases u <;> simp [loadScore]
  all_goals first
    | exact ⟨by linarith [h0 ‹_›, h1 ‹_›], by linarith [h0 ‹_›, h1 ‹_›]⟩
    | exact ⟨by linarith [hs0 ‹_›], hs1 ‹_›⟩

theorem size_pos_le_one (sI : Fin n → ℚ) (h : V → ℚ) (ε : ℚ) (hε : 0 < ε)
    (hs0 : ∀ i, 0 ≤ sI i) (hs1 : ∀ i, sI i ≤ 1) (h0 : ∀ v, 0 ≤ h v) (h1 : ∀ v, h v ≤ 1)
    (u : ThreeItem V n f b) : 0 < size sI h ε u ∧ size sI h ε u ≤ 1 := by
  have hl0 : 0 < scale ε := lt_min (by linarith) (by norm_num)
  have hl1 : scale ε ≤ 1 / 100 := min_le_right _ _
  obtain ⟨t0, t1⟩ := typeScore_bounds u
  obtain ⟨l0, l1⟩ := loadScore_bounds sI h hs0 hs1 h0 h1 u
  have t0' : (-4 : ℚ) ≤ typeScore u := by exact_mod_cast t0
  have t1' : (typeScore u : ℚ) ≤ 5 := by exact_mod_cast t1
  unfold size
  constructor <;> nlinarith

end ThreeItem

/-- The number `f = |V| − n − b` of filler items (proof of Lemma 2.1, p.4). Natural subtraction;
every theorem assumes `|V| ≥ n + b`, as Lemma 2.1 does. -/
def fillerCount (V : Type*) [Fintype V] (n b : ℕ) : ℕ := Fintype.card V - n - b

/-- The item type of `J` for the data `(I, b, V)`. -/
abbrev JItem (I : Instance) (V : Type*) [Fintype V] (b : ℕ) : Type _ :=
  ThreeItem V I.n (fillerCount V I.n b) b

/-- **The three-item instance `J`** of the proof of Lemma 2.1, p.4–5, as a bin packing instance:
its items are `JItem I V b` with the sizes (2.5) computed from `s_I`, `h` and `ε`.

**Formalization Note** The items are listed in the order of `Fintype.equivFin`; `OPT` and `LP`
do not depend on the order. The hypotheses `ε > 0` and `h(V) ⊆ [0, 1]` make every size lie in
`(0, 1]`. -/
noncomputable def jInstance (I : Instance) (V : Type*) [Fintype V] [DecidableEq V] (b : ℕ)
    (h : V → ℚ) (ε : ℚ) (hε : 0 < ε) (h0 : ∀ v, 0 ≤ h v) (h1 : ∀ v, h v ≤ 1) : Instance where
  n := Fintype.card (JItem I V b)
  size k := ThreeItem.size I.size h ε ((Fintype.equivFin (JItem I V b)).symm k)
  size_pos _ := (ThreeItem.size_pos_le_one I.size h ε hε (fun i => (I.size_pos i).le)
    I.size_le_one h0 h1 _).1
  size_le_one _ := (ThreeItem.size_pos_le_one I.size h ε hε (fun i => (I.size_pos i).le)
    I.size_le_one h0 h1 _).2

/-- The class pattern of a set `U ⊆ J`: the multiset of the classes of its items (p.5). -/
def pattern {V : Type*} {n f b : ℕ} (U : Finset (ThreeItem V n f b)) : Multiset ThreeItem.Cls :=
  U.val.map ThreeItem.cls

/-- **The patterns (2.8)**, p.5: `S⁺S⁻X`, `S⁺S⁻X⁰`, `S⁻E⁻₁E⁻₂`, `S⁺E⁺₁E⁺₂`. -/
def zeroPatterns : List (Multiset ThreeItem.Cls) :=
  [{.sPlus, .sMinus, .src}, {.sPlus, .sMinus, .filler},
   {.sMinus, .eMinus1, .eMinus2}, {.sPlus, .ePlus1, .ePlus2}]

/-- **The triples `T_j(π)` (2.9)**, p.5: for `π = (v₀, i₁, v₁, …, i_k, v_k)` and `1 ≤ j ≤ b`,
`T_j(π) = {{S⁻_{v₀}, E⁻_{j,1}, E⁻_{j,2}}, {S⁺_{v_k}, E⁺_{j,1}, E⁺_{j,2}}} ∪
{{S⁺_{v_{ℓ−1}}, X_{i_ℓ}, S⁻_{v_ℓ}} : 1 ≤ ℓ ≤ k}`.

**Formalization Note** `j : Fin b` is the paper's `j + 1`. -/
def pathTriples (I : Instance) {V : Type*} [Fintype V] [DecidableEq V] {h : V → ℚ} (b : ℕ)
    (π : StatePath I V h) (j : Fin b) : Finset (Finset (JItem I V b)) :=
  insert {ThreeItem.sMinus π.first, ThreeItem.eMinus1 j, ThreeItem.eMinus2 j}
    (insert {ThreeItem.sPlus π.last, ThreeItem.ePlus1 j, ThreeItem.ePlus2 j}
      (Finset.univ.image fun ℓ : Fin π.len =>
        ({ThreeItem.sPlus (π.state ℓ.castSucc), ThreeItem.src (π.item ℓ),
          ThreeItem.sMinus (π.state ℓ.succ)} : Finset (JItem I V b))))

/-- The bin of item `u` in a packing `P` of `J` (items indexed through `Fintype.equivFin`). -/
noncomputable def binOf {I : Instance} {V : Type*} [Fintype V] [DecidableEq V] {b : ℕ} {h : V → ℚ} {ε : ℚ}
    {hε : 0 < ε} {h0 : ∀ v, 0 ≤ h v} {h1 : ∀ v, h v ≤ 1} {B : ℕ}
    (P : Packing (jInstance I V b h ε hε h0 h1) B) (u : JItem I V b) : Fin B :=
  P.assignment (Fintype.equivFin (JItem I V b) u)

/-- The content `U ⊆ J` of bin `β` of a packing `P` of `J`. -/
noncomputable def binContent {I : Instance} {V : Type*} [Fintype V] [DecidableEq V] {b : ℕ}
    {h : V → ℚ} {ε : ℚ} {hε : 0 < ε} {h0 : ∀ v, 0 ≤ h v} {h1 : ∀ v, h v ≤ 1} {B : ℕ}
    (P : Packing (jInstance I V b h ε hε h0 h1) B) (β : Fin B) : Finset (JItem I V b) :=
  Finset.univ.filter fun u => binOf P u = β

/-- **The subfamily `B∗` of Claim 2.5**, p.7: the bins of `P` with exactly three items and type
score `p₁(U) = 0`. -/
noncomputable def zeroTypeBins {I : Instance} {V : Type*} [Fintype V] [DecidableEq V] {b : ℕ}
    {h : V → ℚ} {ε : ℚ} {hε : 0 < ε} {h0 : ∀ v, 0 ≤ h v} {h1 : ∀ v, h v ≤ 1} {B : ℕ}
    (P : Packing (jInstance I V b h ε hε h0 h1) B) : Finset (Fin B) :=
  Finset.univ.filter fun β =>
    (binContent P β).card = 3 ∧ ∑ u ∈ binContent P β, ThreeItem.typeScore u = 0

end LogStarBinPacking


