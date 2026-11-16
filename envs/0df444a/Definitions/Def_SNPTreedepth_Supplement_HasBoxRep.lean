-- Prove2me | Definitions.Def_SNPTreedepth_Supplement_HasBoxRep
-- name    : SNPTreedepth_Supplement_HasBoxRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:53:43.185877+00:00
-- url     : https://prove2.me/theorems/6f4e835c-59b6-422f-b73e-92bb1af2adef
-- title:
--   Box representations and boxicity $\mathrm{box}(G)\le d$
-- statement:
--   A **$d$-box** is a product $I_1\times\dots\times I_d\subseteq\mathbb R^d$ of closed intervals $I_i=[a_i,b_i]$, $a_i\le b_i$. A **$d$-box representation** of a graph $G=(V,E)$ assigns to every vertex $v$ a $d$-box $B_v$ such that for all distinct $u,v\in V$,
--   $$
--   uv\in E\iff B_u\cap B_v\neq\emptyset .
--   $$
--   The **boxicity** $\mathrm{box}(G)$ is the least $d\ge1$ such that $G$ has a $d$-box representation. A $d'$-box representation with $d'\le d$ extends to a $d$-box representation by constant coordinates, so for $d\ge1$, $\mathrm{box}(G)\le d$ holds exactly when $G$ has a $d$-box representation.
--
--   Graphs of boxicity $1$ are the interval graphs; Theorem 53 expresses $\mathrm{box}(G)\le d$ by an SNP sentence.
-- source:
--   Depian, Ganian, Greilhuber, Gründel, Wietheger, A Uniform Algorithm for Strict NP on Bounded-Treedepth Structures, STOC 2027 submission (manuscript sha256 98e4e1a9…), Definition 50, p.50 (PDF p.51)

import Mathlib

set_option autoImplicit false

namespace SNPTreedepth.Supplement

/-- The **`d`-box** `[lo₁, hi₁] × ⋯ × [lo_d, hi_d] ⊆ ℝ^d` (Depian et al., *A Uniform Algorithm for
Strict NP on Bounded-Treedepth Structures*, STOC 2027 submission (manuscript sha256 98e4e1a9…),
Definition 50, p.50): a product of closed intervals. -/
def boxOf {d : ℕ} (lo hi : Fin d → ℝ) : Set (Fin d → ℝ) :=
  Set.univ.pi (fun i => Set.Icc (lo i) (hi i))

/-- A **`d`-box representation** of `G` (Depian et al., Definition 50, p.50): every vertex `v` gets
the `d`-box `B_v = boxOf (lo v) (hi v)`, each interval `[lo v i, hi v i]` a closed interval
(`lo v i ≤ hi v i`), such that for all distinct `u, v ∈ V`: `uv ∈ E ⟺ B_u ∩ B_v ≠ ∅`. -/
def IsBoxRep {V : Type} (G : SimpleGraph V) (d : ℕ) (lo hi : V → Fin d → ℝ) : Prop :=
  (∀ v i, lo v i ≤ hi v i) ∧
  ∀ u v, u ≠ v → (G.Adj u v ↔ (boxOf (lo u) (hi u) ∩ boxOf (lo v) (hi v)).Nonempty)

/-- `G` **has a `d`-box representation**; for `d ≥ 1` this is `box(G) ≤ d` (Depian et al.,
Definition 50, p.50: "the boxicity box(G) of G is the least d ≥ 1 such that G has a d-box
representation").

**Formalization Note** A `d'`-box representation with `d' ≤ d` extends to a `d`-box representation
by constant coordinates `[0, 0]`, so for `d ≥ 1` the existence of a `d`-box representation is
exactly `box(G) ≤ d`. Statements use this predicate only for `d ≥ 1`. -/
def HasBoxRep {V : Type} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ lo hi : V → Fin d → ℝ, IsBoxRep G d lo hi

end SNPTreedepth.Supplement


