-- Prove2me | Definitions.Def_BeyondGomoryHu_Units_Hierarchy
-- name    : BeyondGomoryHu_Units_Hierarchy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:45:56.497105+00:00
-- url     : https://prove2.me/theorems/f3f33a7e-269e-4b3d-99f9-7958f54a2ffc
-- title:
--   Skeleton hierarchy, αβ-components, α-components, tied components, maximizers, the traversal list and σ-numberings
-- statement:
--   **Hierarchy (§3.1).** The nodes of $\mathcal T$ are subsets of $V$: the root is $V$, and a node $\mu$ with $|\mu|\ge2$ has the children $\mu\cap U$ for the terminal $\mu$-units $U$. $\mathrm{LCA}_{\mathcal T}(w,z)$ is the node containing $w,z$ that is contained in every node containing both.
--
--   **$\alpha\beta$-components (Def. 3.1, footnote 2).** In $H_\mu$, nodes are $\alpha\beta$-equivalent if they lie on the same side of every canonical cut separating $\alpha$ from $\beta$; an $\alpha\beta$-component is a class with a nonempty node, without the empty entry/exit nodes of the cycles on the path $P_{\alpha\beta}$.
--
--   **$\alpha$-components (Def. 3.5).** For a tree-edge $g=(\alpha,\beta)$ let $H$ be the sub-skeleton rooted by $g$ in direction $\beta$. Type 1: if some $\pi_\mu(z)$ meets $H$ only at $\beta$, or $\deg\beta\ge4$, then $H$ is one component. Type 2: else, if $\beta$ is a tree-node of degree $3$, the two sub-skeletons beyond $\beta$. Type 3: else $\beta=\beta_0$ lies on a cycle $(\beta_0,\dots,\beta_k,\beta_0)$ and the components are the sub-skeletons $T_i$ beyond the tree-edge of $\beta_i$, $1\le i\le k$. $T$ is **tied** to $v$ if $\pi_\mu(v)$ meets $T$ (Def. 3.6).
--
--   **Maximizer (Lemma 4.5).** $\mathcal C_{T,v}$ is the family of $(a,b)$-mincuts $C$ with $a,b\in\alpha$, $T\subseteq C$, $v\notin C$; a maximizer is a member containing all members.
--
--   **Traversal list (p. 21).** The list $T_1,\dots,T_k$ of the $\alpha\beta$-components met along $P_{\alpha\beta}$ from $\alpha$ to $\beta$, reporting at each cycle (entered at $\gamma$, left at $\delta$) one semi-cycle from $\gamma$ to $\delta$ and then the other. **Rightmost component $T_r(v)$ (p. 22):** the component containing the last node of $\pi_\mu(v)\cap P_{\alpha\beta}$ (oriented from $\alpha$ to $\beta$), or, if that node is a cycle's entry node, the first component of that cycle in the list. **$\sigma$-numbering (Lemma 6.3):** for a tree-edge $f$ with endpoint $\gamma$ and sub-skeleton $S$ beyond it, $\sigma(u)<\sigma(v)$ yields a $\mu$-mincut $A$ with $A\cap\mu=S$, $u\in A$, $v\notin A$, and $\sigma(u)=\sigma(v)$ iff $\phi_\mu(u)=\phi_\mu(v)$, for $u,v$ whose projections contain $f$.
--
--   **Formalization Note.** The traversal fixes the semi-cycles traversed first by a simple $\alpha$–$\beta$ path $Q$; nodes are keyed by their index on $Q$, and nodes of the other semi-cycle by the index of the exit node plus their distance from the entry node along that semi-cycle. "Further towards $\beta$" is expressed by canonical cuts separating $\alpha$ from $\beta$. None of these objects refers to the paper's algorithm.
-- source:
--   Koustav Bhanja, Merav Parter, Asaf Petruschka, STOC 2027 submission #1544 (October 2026), §3.1 p. 5 (PDF 7); Definitions 3.1, 3.5, 3.6, pp. 5–8 (PDF 7–10); Lemma 4.5 p. 14 (PDF 16); pp. 21–22 (PDF 23–24); Lemma 6.3 p. 21 (PDF 23)

import Mathlib
import Definitions.Def_BeyondGomoryHu_Units_Carcass

set_option autoImplicit false

namespace BeyondGomoryHu.Units

/-!
Sections 3–6 (pp. 5–25): the skeleton hierarchy `T` (§3.1), `αβ`-components (Definition 3.1 with
the fix of footnote 2), the path `P_αβ`, sub-skeletons and `α`-components (Definition 3.5), tied
components (Definition 3.6), the cut family `C_{T,v}` (Lemma 4.5), the traversal list
`T₁, …, T_k` of the `αβ`-components (p. 21), the rightmost component `T_r(v)` (p. 22) and the
numberings `σ_{f,γ}` of Lemma 6.3. Everything is defined from the cut function and the carcass
data; nothing refers to the paper's algorithm.
-/

open Classical

variable {V : Type} [Fintype V] [DecidableEq V]

/-- §3.1: the nodes of the skeleton hierarchy `T`. The root is `V`; a node `μ` with `|μ| ≥ 2` has
the children `μ ∩ U` for the terminal `μ`-units `U` (the unit of some `s ∈ μ`); singletons are
leaves. -/
inductive IsNode (G : WGraph V) : Finset V → Prop
  | root : IsNode G Finset.univ
  | child {μ : Finset V} (s : V) : IsNode G μ → 2 ≤ μ.card → s ∈ μ →
      IsNode G (μ.filter (fun t => SEquiv G μ s t))

/-- `μ = LCA_T(w, z)`: the node of `T` containing `w` and `z` that is contained in every node of
`T` containing both. -/
def IsLCA (G : WGraph V) (w z : V) (μ : Finset V) : Prop :=
  IsNode G μ ∧ w ∈ μ ∧ z ∈ μ ∧ ∀ ν : Finset V, IsNode G ν → w ∈ ν → z ∈ ν → μ ⊆ ν

variable {N : Type} [Fintype N]

/-- The canonical cut `C` separates the nodes `a` (`α`) and `b` (`β`). -/
def SepCut (K : Carcass V N) (a b : N) (C : Set (Sym2 N)) : Prop :=
  IsCanonicalCut K.H C ∧ ¬ SameSide K.H C a b

/-- Definition 3.1: nodes `c, d` are `αβ`-equivalent if they are on the same side of every
canonical cut separating `α` from `β`. -/
def ABEquiv (K : Carcass V N) (a b c d : N) : Prop :=
  ∀ C, SepCut K a b C → SameSide K.H C c d

/-- The nodes of `P_αβ`: the nodes of the simple paths of `H` from `α` to `β`. -/
def Pnodes (K : Carcass V N) (a b : N) : Set N :=
  {c | ∃ p : K.H.Walk a b, p.IsPath ∧ c ∈ p.support}

/-- `c` is the entry or exit node of a cycle on `P_αβ`: a cycle-node incident to a tree-edge
whose removal separates `α` from `β`. -/
def IsEntryExit (K : Carcass V N) (a b c : N) : Prop :=
  IsCycleNode K.H c ∧ ∃ d, IsTreeEdge K.H s(c, d) ∧ ¬ SameSide K.H {s(c, d)} a b

/-- Definition 3.1 with footnote 2: an `αβ`-component is an `αβ`-equivalence class containing a
nonempty node, with the empty entry and exit nodes of the cycles on `P_αβ` excluded. -/
def IsABComp (K : Carcass V N) (a b : N) (T : Set N) : Prop :=
  ∃ c, (K.terms c).Nonempty ∧
    T = {d | ABEquiv K a b c d ∧ ¬ (K.terms d = ∅ ∧ IsEntryExit K a b d)}

/-- The sub-skeleton rooted by the tree-edge `(u, v)` in direction `v`: the component of
`H` minus that edge containing `v`. -/
def subSkel (K : Carcass V N) (u v : N) : Set N :=
  {d | SameSide K.H {s(u, v)} v d}

/-- Definition 3.5, Type-1 condition for the tree-edge `g = (α, β)`: (i) some vertex `z` has a
projection meeting the sub-skeleton `H` only at `β`, or (ii) `deg β ≥ 4`. -/
def Type1 (K : Carcass V N) (a b : N) : Prop :=
  (∃ z : V, projNodes K z ∩ subSkel K a b = {b}) ∨ 4 ≤ K.H.degree b

/-- `β 0, β 1, …, β k` is a cycle of `H` (`k ≥ 2`): distinct nodes, consecutive ones adjacent,
and `β k` adjacent to `β 0`. -/
def IsCycleSeq (H : SimpleGraph N) (k : ℕ) (β : ℕ → N) : Prop :=
  2 ≤ k ∧ (∀ i j, i ≤ k → j ≤ k → β i = β j → i = j) ∧ (∀ i, i < k → H.Adj (β i) (β (i + 1))) ∧
    H.Adj (β k) (β 0)

/-- The sub-skeleton rooted at the tree-edge `(c, γ)` of the cycle-node `c`, in direction `γ`
(the `Type-3` component of `c`). -/
def cycComp (K : Carcass V N) (c : N) : Set N :=
  {d | ∃ γ, IsTreeEdge K.H s(c, γ) ∧ d ∈ subSkel K c γ}

/-- Definition 3.5, Type-3 situation: `g = (α, β)` is a tree-edge, neither Type-1 nor Type-2
applies, and `β = β₀, β₁, …, β_k` is the cycle `O` through `β`. -/
def IsType3Setup (K : Carcass V N) (a b : N) (k : ℕ) (β : ℕ → N) : Prop :=
  K.H.Adj a b ∧ IsTreeEdge K.H s(a, b) ∧ ¬ Type1 K a b ∧
    ¬ (IsTreeNode K.H b ∧ K.H.degree b = 3) ∧ IsCycleSeq K.H k β ∧ β 0 = b

/-- Definition 3.5: `T` is an `α`-component, for the nonempty node `a` (`α`) of `H_μ`. -/
def IsAlphaComp (K : Carcass V N) (a : N) (T : Set N) : Prop :=
  ∃ b, K.H.Adj a b ∧ IsTreeEdge K.H s(a, b) ∧
    ((Type1 K a b ∧ T = subSkel K a b) ∨
     (¬ Type1 K a b ∧ IsTreeNode K.H b ∧ K.H.degree b = 3 ∧
        ∃ γ, K.H.Adj b γ ∧ γ ≠ a ∧ T = subSkel K b γ) ∨
     (∃ k β, IsType3Setup K a b k β ∧ ∃ i, 1 ≤ i ∧ i ≤ k ∧ T = cycComp K (β i)))

/-- Definition 3.6: the `α`-component `T` is tied to `v` if `π_μ(v)` intersects `T`. -/
def Tied (K : Carcass V N) (T : Set N) (v : V) : Prop :=
  (projNodes K v ∩ T).Nonempty

/-- `v` has exactly one tied `α`-component, namely `T`. -/
def OnlyTied (K : Carcass V N) (a : N) (T : Set N) (v : V) : Prop :=
  IsAlphaComp K a T ∧ Tied K T v ∧ ∀ T', IsAlphaComp K a T' → Tied K T' v → T' = T

/-- Lemma 4.5: `C_{T,v}`, the `(a, b)`-mincuts with `a, b ∈ α` containing `T` and not `v`. -/
def CFamily (G : WGraph V) (K : Carcass V N) (a : N) (T : Set N) (v : V) : Set (Finset V) :=
  {C | ∃ a' ∈ K.terms a, ∃ b' ∈ K.terms a, IsOrientedMincut G a' b' C ∧
    compTerms K T ⊆ (C : Set V) ∧ v ∉ C}

/-- `M` is the maximizer of `C_{T,v}` (the member containing every member). -/
def IsMaximizer (G : WGraph V) (K : Carcass V N) (a : N) (T : Set N) (v : V)
    (M : Finset V) : Prop :=
  M ∈ CFamily G K a T v ∧ ∀ C ∈ CFamily G K a T v, C ⊆ M

/-- Position key of a node of `P_αβ` for the traversal fixed by the simple path `Q` from `α` to
`β` (p. 21): a node of `Q` is keyed by its index on `Q`; a node `p` off `Q` lies on the other
semi-cycle of a cycle `O` that `Q` enters at `γ` and leaves at `δ`, and is keyed just after the
index of `δ`, by its distance from `γ` along that semi-cycle. -/
noncomputable def travKey (K : Carcass V N) {a b : N} (Q : K.H.Walk a b) (p : N) : ℕ :=
  if p ∈ Q.support then Q.support.idxOf p * (Fintype.card N + 1)
  else
    let L := Q.support.filter (fun c => OnCommonCycle K.H c p)
    match L.head?, L.getLast? with
    | some γ, some δ =>
        Q.support.idxOf δ * (Fintype.card N + 1) +
          (K.H.deleteEdges {e | δ ∈ e}).dist γ p
    | _, _ => 0

/-- p. 21, "Ordering the αβ-components": `L` is a list `T₁, …, T_k` of all `αβ`-components
obtained by traversing `P_αβ` from `α` to `β`, reporting at each cycle (entered at `γ`, left at
`δ`) first the components on one semi-cycle from `γ` to `δ` and then those on the other; the
semi-cycles traversed first are those of the simple path `Q`. -/
def IsTraversalList (K : Carcass V N) (a b : N) (L : List (Set N)) : Prop :=
  L.Nodup ∧ (∀ T, T ∈ L ↔ IsABComp K a b T) ∧
    ∃ Q : K.H.Walk a b, Q.IsPath ∧
      L.Pairwise (fun T T' => ∃ p ∈ T, p ∈ Pnodes K a b ∧ ∃ p' ∈ T', p' ∈ Pnodes K a b ∧
        travKey K Q p < travKey K Q p')

/-- The node `p'` of `P_αβ` lies strictly further towards `β` than `p`: some canonical cut
separating `α` from `β` keeps `p` with `α` and `p'` with `β`, and none does the converse. -/
def Beyond (K : Carcass V N) (a b p p' : N) : Prop :=
  (∃ C, SepCut K a b C ∧ SameSide K.H C a p ∧ ¬ SameSide K.H C a p') ∧
    ¬ (∃ C, SepCut K a b C ∧ SameSide K.H C a p' ∧ ¬ SameSide K.H C a p)

/-- p. 22: `T_r(v) = T` for the traversal list `L`. Let `p` be the last node, oriented from `α` to
`β`, of the intersection of `π_μ(v)` with `P_αβ`. If `p` lies in an `αβ`-component, that is
`T_r(v)`; otherwise `p` is the entry node of a cycle `O` and `T_r(v)` is the first
`αβ`-component from `O` in the order of `L`. -/
def IsRightmost (K : Carcass V N) (a b : N) (L : List (Set N)) (v : V) (T : Set N) : Prop :=
  ∃ p ∈ projNodes K v, p ∈ Pnodes K a b ∧
    (∀ p' ∈ projNodes K v, p' ∈ Pnodes K a b → ¬ Beyond K a b p p') ∧
    ((p ∈ T ∧ T ∈ L) ∨
     ((∀ T' ∈ L, p ∉ T') ∧
       ∃ i, ∃ hi : i < L.length, L[i] = T ∧
         (∃ q ∈ T, q ∈ Pnodes K a b ∧ OnCommonCycle K.H q p) ∧
         ∀ j, ∀ hj : j < L.length, (∃ q ∈ L[j], q ∈ Pnodes K a b ∧ OnCommonCycle K.H q p) →
           i ≤ j))

/-- The terminals of the first `i` components of the list `L` (the side of `α` of `C_{i+1}`). -/
def prefixTerms (K : Carcass V N) (L : List (Set N)) (i : ℕ) : Set V :=
  {s | ∃ T ∈ L.take i, s ∈ compTerms K T}

/-- Lemma 6.3's numbering property for the tree-edge `f = (c, γ)` and its endpoint `γ`, with `S`
the sub-skeleton rooted by `f` in direction `γ`: for vertices `u, v` whose projections contain
`f`, `σ(u) < σ(v)` gives a `μ`-mincut `A` with `A ∩ μ = S`, `u ∈ A`, `v ∉ A`, and
`σ(u) = σ(v)` iff `ϕ_μ(u) = ϕ_μ(v)`. -/
def IsSigma (G : WGraph V) (μ : Finset V) (K : Carcass V N) (c γ : N) (σ : V → ℕ) : Prop :=
  ∀ u v, s(c, γ) ∈ projEdges K u → s(c, γ) ∈ projEdges K v →
    (σ u < σ v → ∃ A : Finset V, IsMincut G μ A ∧
        ((A ∩ μ : Finset V) : Set V) = compTerms K (subSkel K c γ) ∧ u ∈ A ∧ v ∉ A) ∧
    (σ u = σ v ↔ SEquiv G μ u v)

end BeyondGomoryHu.Units


