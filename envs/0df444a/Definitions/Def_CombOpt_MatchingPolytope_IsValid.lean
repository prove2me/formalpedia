-- Prove2me | Definitions.Def_CombOpt_MatchingPolytope_IsValid
-- name    : CombOpt_MatchingPolytope_IsValid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:16.43453+00:00
-- url     : https://prove2.me/theorems/f047e27d-21f8-4261-b87c-f56aba254060
-- title:
--   A valid inequality for a set
-- statement:
--   An inequality $w^\top x\le t$ is **valid** for a polyhedron $P$ if $P\subseteq\{x:\ w^\top x\le t\}$, that is, every point of $P$ satisfies it.
--
--   **Formalization Note** The space $\mathbb R^n$ is the coordinate space $\mathbb R^\iota$ of functions $\iota\to\mathbb R$ on a finite index type $\iota$ (take $\iota=\{1,\dots,n\}$ for $\mathbb R^n$, or $\iota=E$ for $\mathbb R^E$), and $w^\top x$ is the dot product. The definition is stated for any set $P$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.2, p. 204 (PDF p. 212)

import Mathlib

namespace CombOpt.MatchingPolytope

/-- **A valid inequality.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.2, p. 204 (PDF p. 212): "An inequality w^T x ≤ t is valid for a polyhedron P if
P ⊆ {x : w^T x ≤ t}."

**Formalization Note.** `ℝ^n` is the coordinate space `ι → ℝ` over a finite index type `ι`
(`Fin n` for the book's `ℝ^n`, `E` for `ℝ^E`); `w ⬝ᵥ x` is `w^T x`. -/
def IsValid {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) (w : ι → ℝ) (t : ℝ) : Prop :=
  P ⊆ {x | w ⬝ᵥ x ≤ t}

end CombOpt.MatchingPolytope


