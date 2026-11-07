-- Prove2me | Definitions.Def_LovaszECCKernel_flip
-- name    : LovaszECCKernel_flip
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:54:47.362505+00:00
-- url     : https://prove2.me/theorems/be7dca9a-b9e9-4b2a-ab46-5c560a692707
-- title:
--   Pair sets $M\subseteq\binom{V(G)}{2}$ and the modified graph $G\triangle M$
-- statement:
--   A **pair set** is a set $M$ of unordered pairs of distinct vertices, $M\subseteq\binom{V(G)}{2}$. The graph
--   $$G\triangle M=(V(G),\,E(G)\triangle M)$$
--   deletes the edges of $E(G)\cap M$ and adds the pairs of $M\setminus E(G)$: two distinct vertices are adjacent in $G\triangle M$ iff exactly one of "$uv\in E(G)$" and "$uv\in M$" holds. $|M|$ is the number of adjacency modifications.
--
--   **Formalization Note** Pairs are `Sym2 V`. A diagonal pair in $M$ has no effect on $G\triangle M$; every statement that measures $|M|$ also requires $M$ to be a pair set.
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), §2, p.15 (= PDF p.15)

import Mathlib

set_option autoImplicit false

namespace LovaszECCKernel

/-- `M` is a set of **pairs of distinct vertices**, `M ⊆ (V(G) choose 2)` (Fomin, Golovach,
Khargeliia, Sagunov, Simonov, *Stability Meets Kernelization: Algorithmic Extensions of the Lovász
and Erdős–Goodman–Pósa Theorems*, STOC 2027 submission (manuscript sha256 a9d53ab8…), §2, p.15
(= PDF p.15): "We write (V(G) choose 2) to denote the set of all pairs of distinct vertices").

**Formalization Note** Pairs are `Sym2 V`; the condition excludes the diagonal pairs `s(v, v)`. -/
def IsPairSet {V : Type*} (M : Finset (Sym2 V)) : Prop := ∀ e ∈ M, ¬ e.IsDiag

/-- The graph `G△M` (Fomin et al., STOC 2027 submission (manuscript sha256 a9d53ab8…), §2, p.15
(= PDF p.15)): "For S ⊆ (V(G) choose 2), G△S = (V(G), E(G)△S), that is, the graph obtained by
deleting of edges of E(G) ∩ S and adding the edges of S \ E(G)."

**Formalization Note** Two distinct vertices `u, v` are adjacent in `flip G M` iff exactly one of
"`uv ∈ E(G)`" and "`s(u, v) ∈ M`" holds. A diagonal pair in `M` has no effect; statements that
measure `|M|` require `IsPairSet M`. -/
def flip {V : Type*} (G : SimpleGraph V) (M : Finset (Sym2 V)) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (G.Adj u v ↔ s(u, v) ∉ M)
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact ⟨fun h' => h.2.1 h'.symm,
    fun h' => (h.2.2 h').symm⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end LovaszECCKernel


