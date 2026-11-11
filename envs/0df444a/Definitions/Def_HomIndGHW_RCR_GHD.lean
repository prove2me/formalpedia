-- Prove2me | Definitions.Def_HomIndGHW_RCR_GHD
-- name    : HomIndGHW_RCR_GHD
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:00:48.874465+00:00
-- url     : https://prove2.me/theorems/7dacf926-0245-4884-a748-edf214141ac4
-- title:
--   Edge covers, generalised and fractional hypertree decompositions, width, full, pure and semi-pure decompositions (Definitions 1.10–1.11, 2.2–2.3)
-- statement:
--   Let $\mathcal A$ be a $\sigma$-structure. A sequence $C$ of coloured tuples is an **edge cover** of $X\subseteq A$ if $X\subseteq\bigcup_{R(\bar t)\in C}\mathrm{set}(\bar t)$ (Definition 1.10). A **generalised hypertree decomposition** (GHD) of $\mathcal A$ is a triple $(T,B,\lambda)$ with $T$ a tree, $B:V(T)\to 2^A$, and $\lambda$ mapping each node to a sequence of coloured tuples (repetitions allowed), such that
--
--   1. for every $\bar t\in\mathrm{CT}(\mathcal A)$ some node $v$ has $\mathrm{set}(\bar t)\subseteq B(v)$;
--   2. for every $x\in A$ the nodes $\{v\mid x\in B(v)\}$ induce a connected subtree;
--   3. for every node $v$, $\lambda(v)$ is an edge cover of $B(v)$.
--
--   Its **width** is $\max_{v}|\lambda(v)|$; $\mathcal A$ **admits a GHD of width at most $k$** if some GHD has $|\lambda(v)|\le k$ for every $v$:
--   $$\mathrm{width}(T,B,\lambda)=\max_{v\in V(T)}|\lambda(v)|\le k .$$
--   A **fractional edge cover** of $X$ by a sequence $C$ assigns $\rho(p)\in\mathbb Q_{\ge0}$ to each position $p$ with $\sum_{p:\,x\in C[p]}\rho(p)\ge1$ for every $x\in X$ (Definition 2.2). A **fractional hypertree decomposition** (FHD) is $(T,B,\lambda,(\rho_v)_v)$ with conditions 1–2 and, in place of 3, $\rho_v$ a fractional edge cover of $B(v)$ by $\lambda(v)$; its width is $\max_v\sum_p\rho_v(p)$ (Definition 2.3). A decomposition is **full** if every coloured tuple $R(\bar a)$ has a node $v$ with $\mathrm{set}(\bar a)\subseteq B(v)$ and $R(\bar a)\in\lambda(v)$; **pure** if $B(v)=\bigcup_{R(\bar t)\in\lambda(v)}\mathrm{set}(\bar t)$ for every $v$; an FHD of width $w$ is **semi-pure** if every $\bigcup_{R(\bar t)\in\lambda(v)}\mathrm{set}(\bar t)$ has a fractional edge cover by $\lambda(v)$ of size at most $w$.
--
--   GHDs carry the width parameter of the main theorem; full, pure and semi-pure decompositions are the normal forms its proof uses.
--
--   **Formalization Note.** The tree is a Mathlib `SimpleGraph` on a node type with `IsTree`; `AdmitsGHD` uses node type `Fin m`. $\lambda(v)$ is a `List`, so the width counts repetitions. Condition 2 is `Preconnected` of the induced subgraph (an element in no bag imposes nothing; for structures without isolated elements every element is in a bag by condition 1). The FHD width is the maximum of the node sums, with value $0$ for an empty node type. For semi-purity the cover is taken over the sequence $\lambda(v)$, as for condition 3 (footnote 8).
-- source:
--   Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, Homomorphism Indistinguishability Beyond Graphs, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…), pp. 8–9, Definitions 1.10–1.11; pp. 16–17, Definitions 2.2–2.3 and the definitions of full, pure and semi-pure decompositions

import Mathlib
import Definitions.Def_HomIndGHW_RCR_Structures

set_option autoImplicit false

namespace HomIndGHW.RCR

/-!
# Edge covers, generalised and fractional hypertree decompositions, full / pure / semi-pure

Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, *Homomorphism Indistinguishability Beyond
Graphs*, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…), Definitions
1.10–1.11 (p. 8–9), Definitions 2.2–2.3 and the definitions of full / pure / semi-pure
decompositions (pp. 16–17).

* The tree `T` is a Mathlib `SimpleGraph` on a node type `N` (finite, by `[Fintype N]` binders in the
  statements) with `T.IsTree` (connected, acyclic, nonempty).
* `λ(v)` is a `List` of coloured tuples: a sequence, repetitions allowed; the width counts the
  length of the list, so repetitions count.
* Condition (2) ("the subtree induced by `{v | x ∈ B(v)}` is connected") is read as
  `Preconnected`, so that an element lying in no bag imposes nothing; for structures without
  isolated elements every element lies in a bag by condition (1).
-/

open Structure Classical

variable {σ : Sig} {V : Type*}

/-- `X ⊆ ⋃_{R(t̄) ∈ C} set(t̄)`: the sequence `C` of coloured tuples is an **edge cover** of `X`
(Definition 1.10, p. 8). -/
def IsEdgeCover {A : Structure σ V} (C : List (CT A)) (X : Set V) : Prop :=
  ∀ x ∈ X, ∃ c ∈ C, c.Mem x

/-- The data `(T, B, λ)` of a generalised hypertree decomposition of `A` with node type `N`
(Definition 1.11, p. 8). -/
structure GHD (A : Structure σ V) (N : Type*) where
  /-- the tree `T` -/
  T : SimpleGraph N
  /-- the bags `B : V(T) → 2^A` -/
  bag : N → Set V
  /-- `λ(v)`, a sequence of coloured tuples of `A` -/
  lam : N → List (CT A)

namespace GHD

variable {A : Structure σ V} {N : Type*}

/-- `(T, B, λ)` is a **generalised hypertree decomposition** of `A` (Definition 1.11, p. 8;
Definition 2.3, p. 17): `T` is a tree, and
(1) every coloured tuple `t̄ ∈ CT(A)` has a node `v` with `set(t̄) ⊆ B(v)`;
(2) for every `x ∈ A` the nodes `{v | x ∈ B(v)}` induce a connected subtree;
(3) for every node `v`, `λ(v)` is an edge cover of `B(v)`. -/
def IsGHD (D : GHD A N) : Prop :=
  D.T.IsTree ∧
  (∀ c : CT A, ∃ v : N, ∀ x, c.Mem x → x ∈ D.bag v) ∧
  (∀ x : V, (D.T.induce {v | x ∈ D.bag v}).Preconnected) ∧
  (∀ v : N, IsEdgeCover (D.lam v) (D.bag v))

/-- **Width at most `k`**: `|λ(v)| ≤ k` for every node (p. 9). -/
def WidthLe (D : GHD A N) (k : ℕ) : Prop := ∀ v : N, (D.lam v).length ≤ k

/-- The **width** `max_{v ∈ V(T)} |λ(v)|` (p. 9). -/
def width [Fintype N] (D : GHD A N) : ℕ := Finset.univ.sup fun v => (D.lam v).length

/-- `D` is **full** (p. 9; p. 17): every coloured tuple `R(ā)` of `A` has a node `v` with
(a) `set(ā) ⊆ B(v)` and (b) `R(ā) ∈ λ(v)`. -/
def Full (D : GHD A N) : Prop :=
  ∀ c : CT A, ∃ v : N, (∀ x, c.Mem x → x ∈ D.bag v) ∧ c ∈ D.lam v

/-- `D` is **pure** (p. 17): `B(v) = ⋃_{R(t̄) ∈ λ(v)} set(t̄)` for every node. -/
def Pure (D : GHD A N) : Prop :=
  ∀ v : N, D.bag v = {x | ∃ c ∈ D.lam v, c.Mem x}

end GHD

/-- `A` **admits a generalised hypertree decomposition of width at most `k`**: there are a finite
tree (on nodes `Fin m`, any finite tree being isomorphic to one of these) and maps `B`, `λ`
satisfying Definition 1.11 with `|λ(v)| ≤ k` for every node. -/
def AdmitsGHD (A : Structure σ V) (k : ℕ) : Prop :=
  ∃ (m : ℕ) (D : GHD A (Fin m)), D.IsGHD ∧ D.WidthLe k

/-- `ρ` is a **fractional edge cover** of `X` by the sequence `C` (Definition 2.2, p. 16, for
sequences per footnote 8, p. 17): `ρ` assigns a nonnegative rational to each position of `C`, and
`∑_{positions p with x ∈ C[p]} ρ(p) ≥ 1` for every `x ∈ X`. -/
def IsFracEdgeCover {A : Structure σ V} (C : List (CT A)) (ρ : Fin C.length → ℚ) (X : Set V) :
    Prop :=
  (∀ p, 0 ≤ ρ p) ∧
  ∀ x ∈ X, 1 ≤ ∑ p ∈ (Finset.univ.filter fun p : Fin C.length => ∃ j, (C.get p).tup j = x), ρ p

/-- The data `(T, B, λ, (ρ_v)_v)` of a fractional hypertree decomposition (Definition 2.3,
pp. 16–17): as for a GHD, together with the weights `ρ_v : λ(v) → ℚ₊` of condition (3), which
determine the width. -/
structure FHD (A : Structure σ V) (N : Type*) extends GHD A N where
  /-- the fractional edge cover `ρ_v` of `B(v)` by `λ(v)` -/
  rho : (v : N) → Fin (lam v).length → ℚ

namespace FHD

variable {A : Structure σ V} {N : Type*}

/-- `(T, B, λ, ρ)` is a **fractional hypertree decomposition** of `A` (Definition 2.3): conditions
(1) and (2) of a GHD, and (3) `ρ_v` is a fractional edge cover of `B(v)` for every node. -/
def IsFHD (D : FHD A N) : Prop :=
  D.T.IsTree ∧
  (∀ c : CT A, ∃ v : N, ∀ x, c.Mem x → x ∈ D.bag v) ∧
  (∀ x : V, (D.T.induce {v | x ∈ D.bag v}).Preconnected) ∧
  (∀ v : N, IsFracEdgeCover (D.lam v) (D.rho v) (D.bag v))

/-- The **width** `max_v ρ_v(λ(v))` of an FHD (p. 17), with `ρ_v(λ(v)) = ∑_p ρ_v(p)`; the maximum
over the empty node set is `0` (the weights are nonnegative, so `0` never exceeds the maximum
of a nonempty tree). -/
def width [Fintype N] (D : FHD A N) : ℚ :=
  Finset.fold max 0 (fun v => ∑ p, D.rho v p) Finset.univ

/-- An FHD is **full** when its underlying `(T, B, λ)` is (p. 17). -/
def Full (D : FHD A N) : Prop := D.toGHD.Full

/-- An FHD is **pure** when its underlying `(T, B, λ)` is (p. 17). -/
def Pure (D : FHD A N) : Prop := D.toGHD.Pure

/-- An FHD of width `w` is **semi-pure** (p. 17): for every node `v` there is a fractional edge
cover of `⋃_{R(t̄) ∈ λ(v)} set(t̄)` (by the sequence `λ(v)`) of size at most `w`. -/
def SemiPure [Fintype N] (D : FHD A N) : Prop :=
  ∀ v : N, ∃ ρ : Fin (D.lam v).length → ℚ,
    IsFracEdgeCover (D.lam v) ρ {x | ∃ c ∈ D.lam v, c.Mem x} ∧ ∑ p, ρ p ≤ D.width

end FHD

end HomIndGHW.RCR


