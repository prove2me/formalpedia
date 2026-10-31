-- Prove2me | Definitions.Def_CombOpt_ChvatalRank_IsValid
-- name    : CombOpt_ChvatalRank_IsValid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:20.671041+00:00
-- url     : https://prove2.me/theorems/96478265-0e0f-4f63-950c-c8a372a83808
-- title:
--   Valid inequality $w^Tx\le t$ for a set $P$
-- statement:
--   An inequality $w^Tx\le t$, with $w\in\mathbb R^n$ and $t\in\mathbb R$, is **valid** for $P\subseteq\mathbb R^n$ if
--   $$
--   P\subseteq\{x : w^Tx\le t\}.
--   $$
--   Valid inequalities are the raw material of faces and of Gomory–Chvátal cuts.
--
--   **Formalization Note** The book states this for polyhedra; it is stated here for an arbitrary set, since the iterates $P^{(i)}$ are known to be polyhedra only through Theorem 6.34. Every inequality is valid for the empty set.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.2, p. 204 (PDF 212)

import Mathlib

open Matrix

namespace CombOpt.ChvatalRank

/-- **Valid inequality.** Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.2, p. 204 (PDF 212):
"An inequality wᵀx ≤ t is valid for a polyhedron P if P ⊆ {x : wᵀx ≤ t}."

**Formalization Note.** Stated for an arbitrary set `P`, because the closure iterates are only known
to be polyhedra by Theorem 6.34. Every inequality is valid for the empty set. -/
def IsValid {n : ℕ} (P : Set (Fin n → ℝ)) (w : Fin n → ℝ) (t : ℝ) : Prop :=
  ∀ x ∈ P, w ⬝ᵥ x ≤ t

end CombOpt.ChvatalRank


