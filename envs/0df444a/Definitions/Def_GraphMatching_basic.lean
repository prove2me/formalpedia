-- Prove2me | Definitions.Def_GraphMatching_basic
-- name    : GraphMatching_basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-27T04:24:16.106362+00:00
-- url     : https://prove2.me/theorems/de568135-756f-4779-8c3c-4cbdeba7616a
-- title:
--   Matchings, vertex covers, fractional vertex covers and the bipartite double cover
-- statement:
--   Basic notions for matchings and vertex covers of a finite simple graph $H$ on a vertex set $W$, together with the fractional vertex cover and the bipartite double cover of a graph $G$ on $V$.
--
--   1. A **matching** of $H$ is a set $M$ of edges of $H$ that are pairwise vertex-disjoint; the **matching number** $\nu(H)$ is the largest size of a matching.
--   2. A **vertex cover** of $H$ is a set $C\subseteq W$ meeting every edge; the **vertex cover number** $\tau(H)$ is the smallest size of a vertex cover.
--   3. A **fractional vertex cover** of $G$ is a function $y:V\to[0,1]$ with $y(u)+y(v)\ge 1$ for every edge $uv$ of $G$; the **fractional vertex cover number** is
--   $$\tau^*(G)=\min\Big\{\sum_{v\in V}y(v)\ :\ y \text{ a fractional vertex cover}\Big\}.$$
--   4. The **bipartite double cover** of $G$ has vertex set $\{0,1\}\times V$, and $(a,u)$ is adjacent to $(b,v)$ exactly when $a\ne b$ and $uv$ is an edge of $G$.
--
--   These are the objects of the matching-based estimate of the cost $\tau$ of combining fragment shortenings in the sublinear metric TSP algorithm, where $\tau$ is $\sigma$ times a minimum fractional vertex cover of a conflict graph and is estimated through the matching number of its double cover.
--
--   **Formalization Note** `matchingNumber` is a supremum and `vcNumber` a `Nat.find` over finitely many sets; `fracVC` is an infimum over a nonempty set bounded below by $0$. The file also contains the simp lemma `doubleCover_adj` and `isVC_univ` (the whole vertex set is a cover), used to define `vcNumber`.
-- source:
--   Standard (e.g. Schrijver, Combinatorial Optimization, 2003, §16 and §30, matchings/vertex covers/fractional vertex covers); used in Azarmehr–Behnezhad 2026, https://arxiv.org/abs/2611.04283, §7.1.3 p.23 (fractional vertex cover τ_P) and §9.2.2 p.38 (bipartite double cover).

import Mathlib

/-!
# Matchings, vertex covers and fractional vertex covers of finite simple graphs
-/

namespace GraphMatching

open Finset

section Defs

variable {V : Type*}

/-- Fractional vertex cover. -/
def IsFracVC (G : SimpleGraph V) (y : V → ℝ) : Prop :=
  (∀ v, 0 ≤ y v ∧ y v ≤ 1) ∧ ∀ u v, G.Adj u v → 1 ≤ y u + y v

/-- Value of the minimum fractional vertex cover. -/
noncomputable def fracVC [Fintype V] (G : SimpleGraph V) : ℝ :=
  sInf {t | ∃ y, IsFracVC G y ∧ t = ∑ v, y v}

/-- The bipartite double cover. -/
def doubleCover (G : SimpleGraph V) : SimpleGraph (Bool × V) where
  Adj p q := p.1 ≠ q.1 ∧ G.Adj p.2 q.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp] theorem doubleCover_adj (G : SimpleGraph V) (a b : Bool) (u v : V) :
    (doubleCover G).Adj (a, u) (b, v) ↔ a ≠ b ∧ G.Adj u v := Iff.rfl

end Defs

section Matching

variable {W : Type*}

/-- A matching: a finset of edges of `H` that are pairwise vertex-disjoint. -/
def IsMatching (H : SimpleGraph W) (M : Finset (Sym2 W)) : Prop :=
  (∀ e ∈ M, e ∈ H.edgeSet) ∧ ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ x, x ∈ e → x ∉ f

open Classical in
/-- Maximum size of a matching (a sup over the finitely many edge sets). -/
noncomputable def matchingNumber [Fintype W] (H : SimpleGraph W) : ℕ :=
  ((univ : Finset (Finset (Sym2 W))).filter (IsMatching H)).sup Finset.card

/-- Vertex cover. -/
def IsVC (H : SimpleGraph W) (C : Finset W) : Prop :=
  ∀ x y, H.Adj x y → x ∈ C ∨ y ∈ C

theorem isVC_univ [Fintype W] (H : SimpleGraph W) : IsVC H univ :=
  fun x _ _ => Or.inl (mem_univ x)

open Classical in
/-- Minimum size of a vertex cover. -/
noncomputable def vcNumber [Fintype W] (H : SimpleGraph W) : ℕ :=
  Nat.find (⟨_, univ, isVC_univ H, rfl⟩ : ∃ n, ∃ C : Finset W, IsVC H C ∧ C.card = n)


end Matching

end GraphMatching


