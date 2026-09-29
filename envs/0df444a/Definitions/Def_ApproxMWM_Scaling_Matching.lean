-- Prove2me | Definitions.Def_ApproxMWM_Scaling_Matching
-- name    : ApproxMWM_Scaling_Matching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:05:14.281911+00:00
-- url     : https://prove2.me/theorems/4d3aa219-c0b9-498d-9a61-af74825a4d1d
-- title:
--   Matchings, edge duals yz and laminar families of full blossoms
-- statement:
--   Let $G=(V,E)$ be a finite simple graph and $w:E\to\mathbb R$ an edge weight.
--
--   1. A **matching** $M$ is a finite set of edges of $G$ that are pairwise vertex-disjoint. Its weight is $w(M)=\sum_{e\in M}w(e)$. A vertex is **matched** if it is an endpoint of an edge of $M$ and **free** otherwise.
--   2. For $c\in\mathbb R$, $M$ is a **$c$-MWM** (a $c$-approximate maximum weight matching) if $M$ is a matching and $c\cdot w(M')\le w(M)$ for every matching $M'$ of $G$.
--   3. Given duals $y:V\to\mathbb R$ and $z$ on vertex sets, the **edge dual** of $e=(u,v)$ is
--   $$yz(u,v)=y(u)+y(v)+\sum_{B\in\mathcal V_{\mathrm{odd}},\ (u,v)\in E(B)} z(B),$$
--   where $\mathcal V_{\mathrm{odd}}$ is the family of vertex sets of odd cardinality and $(u,v)\in E(B)$ means that both endpoints lie in $B$ (so $E(B)=E\cap(B\times B)$, not the blossom edge set $E_B$).
--   4. **Blossoms.** A trivial blossom is $\{v\}$ with $E_{\{v\}}=\emptyset$. If $A_0,\dots,A_\ell$ ($\ell\ge2$ even, so an odd number of at least three) are pairwise disjoint blossoms joined in a cycle by edges $e_i=(a_i,b_i)$ of $G$ with $a_i\in A_i$, $b_i\in A_{i+1}$ (indices modulo $\ell+1$), then $B=\bigcup_iA_i$ is a blossom with $E_B=\bigcup_iE_{A_i}\cup\{e_0,\dots,e_\ell\}$. A family $\Omega$ of nontrivial blossoms (with edge sets $E_B$) is a **laminar set of full blossoms** for $M$ if every member is built by this rule from children that are trivial or members of $\Omega$, any two members are nested or disjoint, and every member is full: $|M\cap E_B|=(|B|-1)/2$. A **root blossom** is a member of $\Omega$ contained in no other member.
--
--   These are the objects of Section 2 on which every other statement of the mission is built.
--
--   **Formalization Note** The graph is a `SimpleGraph V` on a `Fintype` with decidable equality; edges are `Sym2 V`, matchings are `Finset (Sym2 V)`. The dual $z$ is a function on all finite vertex sets and the sum in $yz$ ranges over all odd sets containing both endpoints, as on p. 1:9. Fullness is written $2|M\cap E_B|+1=|B|$ to avoid natural-number subtraction. The blossom rule requires the $A_i$ to be pairwise disjoint and at least three, which the page leaves implicit ("an odd-length sequence of blossoms … connected in a cycle"; "a short proof by induction shows that $|B|$ is odd").
-- source:
--   Duan and Pettie, Linear-Time Approximation for Maximum Weight Matching, J. ACM 61(1), Article 1 (2014), https://doi.org/10.1145/2529989, pp. 1:8–1:10, Section 2 and Section 2.1 (matching, dual yz, blossoms, full blossoms, root blossoms)

import Mathlib

namespace ApproxMWM.Scaling

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A matching of `G` (Duan–Pettie p. 1:8): a finite set of edges of `G` that are pairwise
vertex-disjoint. -/
def IsMatching (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧ ∀ e ∈ M, ∀ f ∈ M, ∀ v : V, v ∈ e → v ∈ f → e = f

/-- The weight `w(M) = ∑_{e ∈ M} w(e)` of an edge set. -/
def weight (w : Sym2 V → ℝ) (M : Finset (Sym2 V)) : ℝ :=
  ∑ e ∈ M, w e

/-- `v` is matched by `M`: it is an endpoint of some edge of `M`. -/
def IsMatched (M : Finset (Sym2 V)) (v : V) : Prop :=
  ∃ e ∈ M, v ∈ e

/-- `v` is free with respect to `M`: it is not incident to an edge of `M` (p. 1:8). -/
def IsFree (M : Finset (Sym2 V)) (v : V) : Prop :=
  ¬ IsMatched M v

/-- `M` is a `c`-approximate maximum weight matching (a `c`-MWM) of `(G, w)`: it is a matching of
`G` and `c · w(M') ≤ w(M)` for every matching `M'` of `G`. -/
def IsApproxMWM (G : SimpleGraph V) (w : Sym2 V → ℝ) (c : ℝ) (M : Finset (Sym2 V)) : Prop :=
  IsMatching G M ∧ ∀ M' : Finset (Sym2 V), IsMatching G M' → c * weight w M' ≤ weight w M

/-- The edge dual `yz(u,v) = y(u) + y(v) + ∑_{B ∈ V_odd, (u,v) ∈ E(B)} z(B)` (p. 1:9), where
`V_odd` is the family of odd-cardinality vertex sets and `(u,v) ∈ E(B)` means both endpoints lie
in `B` (`e ∈ B.sym2`). -/
def yz (y : V → ℝ) (z : Finset V → ℝ) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun u v => y u + y v, fun u v => add_comm (y u) (y v)⟩ e +
    ∑ B ∈ (univ : Finset (Finset V)).filter (fun B => Odd B.card ∧ e ∈ B.sym2), z B

/-- A family of vertex sets is laminar: any two members are nested or disjoint. -/
def IsLaminar (Ω : Finset (Finset V)) : Prop :=
  ∀ B ∈ Ω, ∀ B' ∈ Ω, B ⊆ B' ∨ B' ⊆ B ∨ Disjoint B B'

/-- `B` is a root blossom of `Ω`: a member not strictly contained in another member (p. 1:10). -/
def IsRoot (Ω : Finset (Finset V)) (B : Finset V) : Prop :=
  B ∈ Ω ∧ ∀ B' ∈ Ω, B ⊆ B' → B' = B

/-- One application of the blossom rule of p. 1:9. `B` with edge set `EBB` is formed from an odd
number `ℓ + 1 ≥ 3` of pairwise disjoint sub-blossoms `A 0, …, A ℓ` (each satisfying `isChild`,
with edge sets `childEB (A i)`) joined in a cycle by edges `e_i = (a i, b i)` of `G` with
`a i ∈ A i`, `b i ∈ A (i+1)` (indices modulo `ℓ + 1`), each cycle edge satisfying `cyc`; then
`B = ⋃ A i` and `E_B = ⋃ E_{A i} ∪ {e_0, …, e_ℓ}`. -/
def IsBlossomOver (G : SimpleGraph V) (cyc : Sym2 V → Prop) (isChild : Finset V → Prop)
    (childEB : Finset V → Finset (Sym2 V)) (B : Finset V) (EBB : Finset (Sym2 V)) : Prop :=
  ∃ (ℓ : ℕ) (A : Fin (ℓ + 1) → Finset V) (a b : Fin (ℓ + 1) → V),
    Even ℓ ∧ 2 ≤ ℓ ∧
    (∀ i, isChild (A i)) ∧
    (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
    (∀ i, a i ∈ A i ∧ b i ∈ A (i + 1) ∧ G.Adj (a i) (b i) ∧ cyc s(a i, b i)) ∧
    B = univ.biUnion A ∧
    EBB = (univ.biUnion fun i => childEB (A i)) ∪ univ.image (fun i => s(a i, b i))

/-- The edge set `E_A` of a child `A` of a blossom of `Ω`: `EB A` if `A ∈ Ω`, and `∅` for a
trivial blossom `{v}`. -/
def childEB (Ω : Finset (Finset V)) (EB : Finset V → Finset (Sym2 V)) (A : Finset V) :
    Finset (Sym2 V) :=
  if A ∈ Ω then EB A else ∅

/-- `Ω` (with edge sets `EB`) is a laminar set of full blossoms with respect to the matching `M`
(pp. 1:9–1:10): every member is formed by the blossom rule from children that are trivial
blossoms `{v}` or members of `Ω`, the family is laminar, and every member is full,
`|M ∩ E_B| = (|B| - 1)/2`, written `2 |M ∩ E_B| + 1 = |B|`. -/
def IsBlossomFamily (G : SimpleGraph V) (M : Finset (Sym2 V)) (Ω : Finset (Finset V))
    (EB : Finset V → Finset (Sym2 V)) : Prop :=
  (∀ B ∈ Ω, IsBlossomOver G (fun _ => True) (fun A => A ∈ Ω ∨ ∃ v, A = {v})
      (childEB Ω EB) B (EB B)) ∧
  IsLaminar Ω ∧
  ∀ B ∈ Ω, 2 * (M ∩ EB B).card + 1 = B.card

/-- The edges of the blossoms of `Ω`: `⋃_{B ∈ Ω} E_B`. -/
def blossomEdges (Ω : Finset (Finset V)) (EB : Finset V → Finset (Sym2 V)) : Finset (Sym2 V) :=
  Ω.biUnion EB

end ApproxMWM.Scaling


