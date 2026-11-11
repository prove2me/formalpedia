-- Prove2me | Definitions.Def_FOMCMonDep_IsPFlip
-- name    : FOMCMonDep_IsPFlip
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:22.410586+00:00
-- url     : https://prove2.me/theorems/bf3cdd92-89fe-4f1a-a57c-78be4955d439
-- title:
--   Balls, the atomic-type partition $\mathcal P_S$, $\mathcal P$-flips, $s$-flips and $s$-definable flips
-- statement:
--   Let $G$ be a graph on a (possibly infinite) vertex set $V$.
--
--   1. **Balls.** $\mathrm{Ball}^G_r(v)=\{w:\mathrm{dist}_G(v,w)\le r\}$, and $\mathrm{Ball}^G_r(C)=\bigcup_{v\in C}\mathrm{Ball}^G_r(v)$ for a set $C$. Distances are shortest-path distances, $\infty$ between different components.
--   2. **Atomic types over $S$.** Two vertices $u,v$ have the same atomic type over $S\subseteq V$ iff $u=v$, or $u,v\notin S$ and $N(u)\cap S=N(v)\cap S$. The corresponding partition $\mathcal P_S$ splits $S$ into singletons and the other vertices by their neighbourhood in $S$.
--   3. **Flips.** For a partition $\mathcal P$ of $V$, a $\mathcal P$-flip of $G$ is a graph $H$ on $V$ such that for every pair of parts $X,Y\in\mathcal P$ (possibly $X=Y$), either $H[X,Y]=G[X,Y]$ or $H[X,Y]=\overline G[X,Y]$: between $X$ and $Y$ all adjacencies are kept or all are complemented. A $\mathcal P_S$-flip is called an $S$-flip.
--   4. **$s$-flips.** $H$ is an $s$-flip of $G$ if it is a $\mathcal P$-flip for a partition with $|\mathcal P|\le s$.
--   5. **$s$-definable flips.** $H$ is an $s$-definable flip of $G$ if it is an $S$-flip for some $S\subseteq V$ with $|S|\le s$.
--
--   These are the flips of the Closure Theorems (Theorems 5.1 and 5.2) and of Lemmas 5.6 and 5.7.
--
--   **Formalization Note** Distances are `SimpleGraph.edist`, valued in $\mathbb N\cup\{\infty\}$. The paper defines $s$-definable flips as $G\oplus(\bar p,R)$, the flip by a symmetric relation $R$ on the atomic types over an $s$-tuple $\bar p$, and states the equivalent form used here ("an S-flip for some S of size at most s"). The number of parts $|\mathcal P|$ is a `Set.encard`.
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), §3, pp.10–12 (PDF 12–14); §5.1, p.18 (PDF 20)

import Mathlib

set_option autoImplicit false

namespace FOMCMonDep

/-- **Balls.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §3, p.10 (PDF 12): "For r ∈ N, denote Ball^G_r(v) := {w ∈ V(G) :
dist_G(v, w) ⩽ r}, where dist_G(·, ·) is the shortest-path distance in G. These notations extend to sets A, B ⊆ V(G)
with Ball^G_r(A) := ⋃_{a∈A} Ball^G_r(a) and dist_G(A, B) := min_{a∈A, b∈B} dist_G(a, b), and to tuples of vertices as
expected."

**Formalization Note.** The vertex type `V` is arbitrary (Part I allows infinite graphs). Distances are
`SimpleGraph.edist`, in `ℕ∞`, which is `⊤` between vertices in different components; "dist_H(v, A) > r" is written
`∀ a ∈ A, r < H.edist v a`, which holds when `A = ∅` (the minimum over the empty set is `∞`). -/
def ballSet {V : Type*} (H : SimpleGraph V) (r : ℕ) (C : Set V) : Set V :=
  {w | ∃ v ∈ C, H.edist v w ≤ (r : ℕ∞)}

/-- **The partition 𝒫_S into atomic types over `S`.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §3, p.12 (PDF 14): "for a
graph G and vertex set S ⊆ V(G), two vertices u, v ∈ V(G) have the same atomic type over S if and only if either
u = v, or u, v ∉ S and N(u) ∩ S = N(v) ∩ S. The partition into atomic types, denoted 𝒫_S, is the corresponding
partition of V(G), which partitions S into singletons, and vertices in V(G) − S according to their neighborhood in
S." On any vertex type (the published `MonDepMW.oneType` is the same partition on `Fin n`). -/
def atomicPartition {V : Type*} (G : SimpleGraph V) (S : Set V) : Setoid V where
  r a b := a = b ∨ (a ∉ S ∧ b ∉ S ∧ ∀ s ∈ S, (G.Adj a s ↔ G.Adj b s))
  iseqv :=
    { refl := fun _ => Or.inl rfl
      symm := by
        rintro a b (h | ⟨ha, hb, h⟩)
        · exact Or.inl h.symm
        · exact Or.inr ⟨hb, ha, fun s hs => (h s hs).symm⟩
      trans := by
        rintro a b c (rfl | ⟨ha, hb, h⟩) (rfl | ⟨hb', hc, h'⟩)
        · exact Or.inl rfl
        · exact Or.inr ⟨hb', hc, h'⟩
        · exact Or.inr ⟨ha, hb, h⟩
        · exact Or.inr ⟨ha, hc, fun s hs => (h s hs).trans (h' s hs)⟩ }

/-- **`𝒫`-flips.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §3, p.12 (PDF 14): "For a graph G and partition 𝒫 of V := V(G), a
𝒫-flip of G is a graph H with V(H) = V such that for every pair X, Y ∈ 𝒫 (possibly X = Y), either H[X, Y] = G[X, Y]
or H[X, Y] = \overline{G}[X, Y]." Here `P` is a setoid on `V`; the parts are the classes of `a` and `b`, and the
pairs concerned are the pairs of distinct vertices `x ∈ X`, `y ∈ Y`. An `S`-flip ("a 𝒫_S-flip of G is called an
S-flip") is `IsPFlip G (atomicPartition G S) H`. -/
def IsPFlip {V : Type*} (G : SimpleGraph V) (P : Setoid V) (H : SimpleGraph V) : Prop :=
  ∀ a b : V,
    (∀ x y, P a x → P b y → x ≠ y → (G.Adj x y ↔ H.Adj x y)) ∨
    (∀ x y, P a x → P b y → x ≠ y → (G.Adj x y ↔ ¬ H.Adj x y))

/-- **`s`-flips.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §3, p.12 (PDF 14): "If |𝒫| ⩽ s, then we call H an s-flip of G."

**Formalization Note.** `|𝒫|` is the `encard` of the set of classes, so that it is the true number of parts also on
an infinite vertex set. -/
def IsSFlip {V : Type*} (G : SimpleGraph V) (s : ℕ) (H : SimpleGraph V) : Prop :=
  ∃ P : Setoid V, (Set.univ : Set (Quotient P)).encard ≤ s ∧ IsPFlip G P H

/-- **`s`-definable flips.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §5.1, p.18 (PDF 20): "For a symmetric relation
R ⊆ Π^s × Π^s, we denote by G ⊕ (p̄, R) the {p1, . . . , ps}-flip H of G obtained by partitioning V(G) into atomic
types over p̄ and then flipping according to R. […] We call such a flip s-definable. Equivalently, an s-definable flip
is an S-flip for some S ⊆ V(G) of size at most s."

**Formalization Note.** The equivalent form printed in the source is used: a `𝒫_S`-flip for a finite `S` with
`|S| ⩽ s`. (The classes of the atomic types over `p̄` are exactly the parts of `𝒫_S` for `S = {p1, …, ps}`, and a
symmetric `R` chooses, for each pair of parts, whether to flip.) -/
def IsSDefFlip {V : Type*} (G : SimpleGraph V) (s : ℕ) (H : SimpleGraph V) : Prop :=
  ∃ S : Finset V, S.card ≤ s ∧ IsPFlip G (atomicPartition G (S : Set V)) H

end FOMCMonDep


