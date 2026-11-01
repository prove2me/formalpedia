-- Prove2me | Definitions.Def_SubmodPerfect_StarSeparations
-- name    : SubmodPerfect_StarSeparations
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:50:48.295998+00:00
-- url     : https://prove2.me/theorems/49583c12-3d50-454a-9c79-5d3701988eab
-- title:
--   Separations, central bags, canonical star separations, $\le_A$, the star-free bag, forcers, core bag and the even set representation
-- statement:
--   Let $G$ be a finite graph and $w$ a weight function.
--
--   1. A **separation** of $G[U]$ is a triple $(A,C,B)$ of pairwise disjoint sets with union $U$ and $A$ anticomplete to $B$; it is a **star separation with center $v$** if $v\in C\subseteq N[v]$. Two separations are **loosely non-crossing** if $A(S_1)\cap C(S_2)=\emptyset=A(S_2)\cap C(S_1)$, and a sequence is **loosely laminar** if any two of its members are.
--   2. The **central bag** of a sequence $\mathcal S$ is $\beta_{\mathcal S}=\bigcap_{S\in\mathcal S}(B(S)\cup C(S))$, and for $\mathcal S=(S_1,\dots,S_k)$ with anchors $v_i$ the weight $w_{\mathcal S}(v_i)=w(v_i)+w(A_i\setminus\bigcup_{j<i}A_j)$, $w_{\mathcal S}(v)=w(v)$ otherwise.
--   3. A **canonical star separation** for $v$ is $S_v=(A_v,C_v,B_v)$ with $B_v$ a largest-weight component of $G\setminus N[v]$, $C_v$ equal to $v$ together with the neighbours of $v$ having a neighbour in $B_v$, and $A_v=V(G)\setminus(B_v\cup C_v)$. Vertices $u,v$ are **star twins** if $B_u=B_v$, $C_u\setminus\{u\}=C_v\setminus\{v\}$, $A_u\setminus\{v\}=A_v\setminus\{u\}$.
--   4. For an ordering $O$, $x\le_A y$ if $x=y$, or $x,y$ are star twins with $O(x)<O(y)$, or they are not star twins and $y\in A_x$. The **$O$-star covering** $X$ is the set of $\le_A$-minimal vertices, the **dimension** of $\{S_x:x\in X\}$ is the least number of loosely laminar sequences partitioning it, and the **star-free bag** is $\beta=\bigcap_{x\in X}(B_x\cup C_x)$.
--   5. A graph $F$ is a **forcer** for $G$ if every $F$-copy $Y$ in $G$ (a set with $G[Y]\cong F$) has a vertex $v$ that breaks $Y\setminus\{v\}$.
--   6. For a bipartition $(X_1,X_2)$ of $\beta$ into independent sets, the **intermediate bag** is $\gamma=\bigcap_{x\in X_2}(B_x\cup C_x)$ and the **core bag** is $R=\beta\cup\bigcup_{x\in X_2}C_x$.
--   7. For a linear extension $\ell$ of $\le_A$ and $D_x=A_x\cap R$, let $\ell_x:D_x\to\{1,\dots,|D_x|\}$ be the ranking by $\ell$, $L'_i=\bigcup_{x\in X_1}\ell_x^{-1}(i)$, $L_i=L'_i\setminus(L_{i+1}\cup\dots\cup L_{\delta^2})$ for $1\le i\le\delta^2$, and $\mathrm{Pre}(L_i)=L_1\cup\dots\cup L_{i-1}$. Then $(L_1,\dots,L_{\delta^2})$ is the **even set representation** of $R\setminus\beta$.
--
--   These are the decomposition objects of Sections 3–4 and 6–7, from which the even set separator of Lemma 8.1 is assembled.
--
--   **Formalization Note** A sequence of separations is a list of pairs (separation, anchor). Canonical star separations are not chosen by a function: the lemmas take a family $S$ with $S_v$ canonical for every $v$. $O$ and $\ell$ are injective maps into $\mathbb N$. $L_i$ is written in the equivalent closed form $L'_i\setminus\bigcup_{i<j\le\delta^2}L'_j$.
-- source:
--   Abrishami, Chudnovsky, Dibek, Vušković, Submodular functions and perfect graphs, arXiv:2110.00108v2 [math.CO] (preprint, 7 Jan 2024), https://arxiv.org/abs/2110.00108v2, §3, p.8 (separations, loosely non-crossing, central bag), p.9 (anchors, w_S); §4, p.10 (star separation, canonical star separation, star twins), p.11 (≤A, O-star covering, dimension), p.12 (star-free bag), p.14 (forcer); §6, p.20 (bipartition, intermediate bag γ, core bag R); §7.2, p.24 (even set representation, Pre)

import Mathlib
import Definitions.Def_SubmodPerfect_Graphs
import Definitions.Def_SubmodPerfect_Wheels

set_option autoImplicit false
open Classical
open scoped BigOperators

noncomputable section

namespace SubmodPerfect

/-! # Separations, central bags, canonical star separations, the star-free bag and the core bag

Abrishami, Chudnovsky, Dibek, Vušković, *Submodular functions and perfect graphs*,
arXiv:2110.00108v2: separations and central bags (§3, pp.8–9), star separations, canonical
star separations, star twins, `≤A`, the `O`-star covering, its dimension and the star-free bag
(§4, pp.10–12), forcers (p.14), the intermediate and core bags (§6, p.20), and the even set
representation (§7.2, p.24).

**Formalization Note.**
1. A sequence of separations with anchors is a list of pairs `(S, v)`; the list order is the
   sequence order.
2. Canonical star separations are not chosen: the lemmas take a family `S : V → Sep V` and
   assume that `S v` is *a* canonical star separation for `v` for every `v` (under the paper's
   hypotheses it is unique, Lemma 4.1). The anchor of `S v` is its center `v`.
3. The ordering `O` and the linear extension `ℓ` are injective maps `V → ℕ`; only the order
   they induce is used.
4. The star-free bag, the dimension, the intermediate and the core bag do not depend on the
   order of the `O`-star covering sequence, so they are written with the covering set `X`. -/

variable {V : Type*} [Fintype V]

/-- A triple `(A, C, B)` of vertex sets. -/
structure Sep (V : Type*) where
  A : Finset V
  C : Finset V
  B : Finset V

/-- `(A, C, B)` is a separation of `G[U]` (p.8): pairwise disjoint (possibly empty) sets with
union `U`, and `A` anticomplete to `B`. -/
def IsSeparationIn (G : SimpleGraph V) (U : Finset V) (S : Sep V) : Prop :=
  Disjoint S.A S.C ∧ Disjoint S.A S.B ∧ Disjoint S.C S.B ∧ S.A ∪ S.C ∪ S.B = U ∧
    ∀ a ∈ S.A, ∀ b ∈ S.B, ¬ G.Adj a b

/-- `S` is a star separation of `G[U]` with center `v` (p.10): a separation with `v ∈ C` and
`C ⊆ N[v]`. -/
def IsStarSepCenteredIn (G : SimpleGraph V) (U : Finset V) (S : Sep V) (v : V) : Prop :=
  IsSeparationIn G U S ∧ v ∈ S.C ∧ ∀ x ∈ S.C, x = v ∨ G.Adj v x

/-- `S₁` and `S₂` are loosely non-crossing (p.8): `A(S₁) ∩ C(S₂) = ∅ = A(S₂) ∩ C(S₁)`. -/
def LooselyNonCrossing (S₁ S₂ : Sep V) : Prop :=
  Disjoint S₁.A S₂.C ∧ Disjoint S₂.A S₁.C

/-- A sequence of anchored separations is loosely laminar (p.8): any two of its separations
are loosely non-crossing. -/
def IsLooselyLaminar (l : List (Sep V × V)) : Prop :=
  ∀ p ∈ l, ∀ q ∈ l, LooselyNonCrossing p.1 q.1

/-- The central bag `β_𝒮 = ⋂_{S ∈ 𝒮} (B(S) ∪ C(S))` of a sequence of separations of `G[U]`
(p.8). -/
def centralBag (U : Finset V) (l : List (Sep V × V)) : Finset V :=
  U.filter (fun v => ∀ p ∈ l, v ∈ p.1.B ∨ v ∈ p.1.C)

/-- The weight function `w_𝒮` on the central bag (p.9): for `𝒮 = (S₁, …, S_k)` with
`Sᵢ = (Aᵢ, Cᵢ, Bᵢ)` and anchors `vᵢ`, `w_𝒮(v) = w(v) + w(Aᵢ \ ⋃_{j<i} Aⱼ)` if `v = vᵢ`, and
`w_𝒮(v) = w(v)` otherwise. (Anchors are distinct where it is used, so at most one term of the
sum is nonzero.) -/
def centralWeight (w : V → ℝ) (l : List (Sep V × V)) (v : V) : ℝ :=
  w v + ∑ i : Fin l.length,
    if (l.get i).2 = v then
      wsum w ((l.get i).1.A \
        (Finset.univ.filter (fun j : Fin l.length => j < i)).biUnion (fun j => (l.get j).1.A))
    else 0

/-- `S` is a canonical star separation for `v` in `G` (p.10): `B_v` is a largest weight
connected component of `G \ N[v]`, `C_v` is `v` together with every vertex of `N(v)` with a
neighbour in `B_v`, and `A_v = V(G) \ (B_v ∪ C_v)`. -/
def IsCanonicalStarSep (G : SimpleGraph V) (w : V → ℝ) (v : V) (S : Sep V) : Prop :=
  IsComponentIn G (Finset.univ \ closedNbhd G {v}) S.B ∧
    (∀ D, IsComponentIn G (Finset.univ \ closedNbhd G {v}) D → wsum w D ≤ wsum w S.B) ∧
    S.C = insert v ((nbhd G {v}).filter (fun u => ∃ b ∈ S.B, G.Adj u b)) ∧
    S.A = Finset.univ \ (S.B ∪ S.C)

/-- `u` and `v` are star twins (p.10): `B_u = B_v`, `C_u \ {u} = C_v \ {v}` and
`A_u \ {v} = A_v \ {u}`. -/
def AreStarTwins (S : V → Sep V) (u v : V) : Prop :=
  (S u).B = (S v).B ∧ (S u).C.erase u = (S v).C.erase v ∧ (S u).A.erase v = (S v).A.erase u

/-- The relation `x ≤A y` (p.11): `x = y`, or `x, y` are star twins and `O(x) < O(y)`, or `x, y`
are not star twins and `y ∈ A_x`. -/
def LeA (S : V → Sep V) (O : V → ℕ) (x y : V) : Prop :=
  x = y ∨ (AreStarTwins S x y ∧ O x < O y) ∨ (¬ AreStarTwins S x y ∧ y ∈ (S x).A)

/-- The `O`-star covering `X` (p.11): the set of minimal vertices with respect to `≤A`. -/
def starCovering (S : V → Sep V) (O : V → ℕ) : Finset V :=
  Finset.univ.filter (fun x => ∀ y, LeA S O y x → y = x)

/-- The star-free bag `β = ⋂_{S ∈ 𝒮} (B(S) ∪ C(S))` (p.12), `𝒮 = {S_x : x ∈ X}` the `O`-star
covering sequence. -/
def starFreeBag (S : V → Sep V) (O : V → ℕ) : Finset V :=
  Finset.univ.filter (fun v => ∀ x ∈ starCovering S O, v ∈ (S x).B ∨ v ∈ (S x).C)

/-- The sequence `{S_x : x ∈ X}` can be partitioned into at most `k` loosely laminar
sequences. -/
def HasDimAtMost (S : V → Sep V) (X : Finset V) (k : ℕ) : Prop :=
  ∃ f : V → Fin k, ∀ x ∈ X, ∀ y ∈ X, f x = f y → LooselyNonCrossing (S x) (S y)

/-- `dim({S_x : x ∈ X}) = k` (p.11): the minimum number of loosely laminar sequences into which
the sequence can be partitioned is `k`. -/
def IsDim (S : V → Sep V) (X : Finset V) (k : ℕ) : Prop :=
  HasDimAtMost S X k ∧ ∀ k' < k, ¬ HasDimAtMost S X k'

/-- `Y` is an `F`-copy in `G` (p.4): `G[Y]` is isomorphic to `F`. -/
def IsCopy {W : Type*} (G : SimpleGraph V) (F : SimpleGraph W) (Y : Finset V) : Prop :=
  Nonempty (G.induce (Y : Set V) ≃g F)

/-- `F` is a forcer for `G` (p.14): every `F`-copy `Y` in `G` has a vertex `v ∈ Y` that breaks
`Y \ {v}`. -/
def IsForcer {W : Type*} (F : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∀ Y : Finset V, IsCopy G F Y → ∃ v ∈ Y, BreaksIn G Finset.univ v (Y.erase v)

/-- `(X₁, X₂)` is a bipartition of `G[β]`: a partition of `β` into two independent sets. -/
def IsBipartition (G : SimpleGraph V) (β X₁ X₂ : Finset V) : Prop :=
  Disjoint X₁ X₂ ∧ X₁ ∪ X₂ = β ∧ (∀ x ∈ X₁, ∀ y ∈ X₁, ¬ G.Adj x y) ∧
    ∀ x ∈ X₂, ∀ y ∈ X₂, ¬ G.Adj x y

/-- `{S_x : x ∈ Y}` is loosely laminar. -/
def IsLooselyLaminarOn (S : V → Sep V) (Y : Finset V) : Prop :=
  ∀ x ∈ Y, ∀ y ∈ Y, LooselyNonCrossing (S x) (S y)

/-- The intermediate bag `γ = ⋂_{S ∈ 𝒮₂} (B(S) ∪ C(S))`, `𝒮₂ = {S_x : x ∈ X₂}` (p.20). -/
def intermediateBag (S : V → Sep V) (X₂ : Finset V) : Finset V :=
  Finset.univ.filter (fun v => ∀ x ∈ X₂, v ∈ (S x).B ∨ v ∈ (S x).C)

/-- The core bag `R = β ∪ ⋃_{x₂ ∈ X₂} C_{x₂}` (p.20). -/
def coreBag (S : V → Sep V) (β X₂ : Finset V) : Finset V :=
  β ∪ X₂.biUnion (fun x => (S x).C)

/-- `ℓ` is a linear extension of `≤A` (p.24): injective, and `u ≤A v`, `u ≠ v` imply
`ℓ(u) < ℓ(v)`. -/
def IsLinearExtension (S : V → Sep V) (O : V → ℕ) (ℓ : V → ℕ) : Prop :=
  Function.Injective ℓ ∧ ∀ u v, LeA S O u v → u ≠ v → ℓ u < ℓ v

/-- `ℓ_x(v)` (p.24): the position of `v` in `D` ordered by `ℓ`, an order isomorphism
`D → {1, …, |D|}` for `v ∈ D`. -/
def rankIn (ℓ : V → ℕ) (D : Finset V) (v : V) : ℕ :=
  (D.filter (fun u => ℓ u ≤ ℓ v)).card

/-- `L′ᵢ = ⋃_{xⱼ ∈ X₁} ℓ_{xⱼ}^{-1}(i)` with `Dⱼ = A_{xⱼ} ∩ R` (p.24). -/
def evenSetRepPre (S : V → Sep V) (X₁ R : Finset V) (ℓ : V → ℕ) (i : ℕ) : Finset V :=
  Finset.univ.filter (fun v => ∃ x ∈ X₁, v ∈ (S x).A ∩ R ∧ rankIn ℓ ((S x).A ∩ R) v = i)

/-- `Lᵢ = L′ᵢ \ (L_{i+1} ∪ … ∪ L_{δ²})` for `1 ≤ i ≤ δ²` (p.24), the even set representation of
`R \ β`.

**Formalization Note.** By downward induction on `i`, `L_{i+1} ∪ … ∪ L_{δ²}` equals
`L′_{i+1} ∪ … ∪ L′_{δ²}`, so the recursive definition is written in this closed form. -/
def evenSetRep (S : V → Sep V) (X₁ R : Finset V) (ℓ : V → ℕ) (δ i : ℕ) : Finset V :=
  evenSetRepPre S X₁ R ℓ i \
    Finset.univ.filter (fun v => ∃ j, i < j ∧ j ≤ δ ^ 2 ∧ v ∈ evenSetRepPre S X₁ R ℓ j)

/-- The prefix `Pre(Lᵢ) = L₁ ∪ … ∪ L_{i−1}` (p.24), `Pre(L₁) = ∅`. -/
def evenSetRepPrefix (S : V → Sep V) (X₁ R : Finset V) (ℓ : V → ℕ) (δ i : ℕ) : Finset V :=
  Finset.univ.filter (fun v => ∃ j, 1 ≤ j ∧ j < i ∧ v ∈ evenSetRep S X₁ R ℓ δ j)

end SubmodPerfect


