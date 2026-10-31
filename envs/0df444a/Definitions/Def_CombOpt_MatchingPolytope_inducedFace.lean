-- Prove2me | Definitions.Def_CombOpt_MatchingPolytope_inducedFace
-- name    : CombOpt_MatchingPolytope_inducedFace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:22.892853+00:00
-- url     : https://prove2.me/theorems/4aa7e465-6418-423e-9b69-9bd74ffdc200
-- title:
--   The face $\{x\in P: w^\top x=t\}$ induced by an inequality
-- statement:
--   For a set $P$, a vector $w$ and a number $t$, this is the set
--   $$\{x\in P:\ w^\top x=t\}.$$
--   An inequality $w^\top x\le t$ **induces** a facet $F$ of $P$ if $F$ is a facet and $F=\{x\in P:\ w^\top x=t\}$.
--
--   Theorem 6.17 and Corollary 6.19 relate the rows of a defining system to the facets they induce.
--
--   **Formalization Note** The space $\mathbb R^n$ is the coordinate space $\mathbb R^\iota$ of functions $\iota\to\mathbb R$ on a finite index type $\iota$ (take $\iota=\{1,\dots,n\}$ for $\mathbb R^n$, or $\iota=E$ for $\mathbb R^E$), and $w^\top x$ is the dot product.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.3, p. 212 (PDF p. 220)

import Mathlib

namespace CombOpt.MatchingPolytope

/-- **The face induced by an inequality.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.3, p. 212 (PDF p. 220): "We say an inequality w^T x ≤ t induces a facet F of P if
F = {x ∈ P : w^T x = t}."

`inducedFace P w t` is the set `{x ∈ P : w^T x = t}`; the inequality `w^T x ≤ t` induces the
facet `F` iff `IsFacet P F ∧ F = inducedFace P w t`.

**Formalization Note.** `ℝ^n` is the coordinate space `ι → ℝ` over a finite index type `ι`
(`Fin n` for the book's `ℝ^n`, `E` for `ℝ^E`); `w ⬝ᵥ x` is `w^T x`. -/
def inducedFace {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) (w : ι → ℝ) (t : ℝ) :
    Set (ι → ℝ) :=
  {x | x ∈ P ∧ w ⬝ᵥ x = t}

end CombOpt.MatchingPolytope


