-- Prove2me | Definitions.Def_MeanBudgetXC_IsCanonical
-- name    : MeanBudgetXC_IsCanonical
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:41:19.174518+00:00
-- url     : https://prove2.me/theorems/d1a43d08-4175-4cf9-b596-214439a3ad58
-- title:
--   Canonical choices in the host graph
-- statement:
--   A vertex set of the host graph is a **canonical choice** when it is obtained as follows: on each source path select either $\{v_{i,0},b_i\}$ (bit zero) or $\{a_i,v_{i,1}\}$ (bit one); select a minimum vertex cover in every padding copy; select one end of each marker edge; select no isolated vertex.
--
--   These sets generate the maximum face of the coefficient body in the anchor direction, with one independent source bit per path.
--
--   **Formalization Note** The auxiliary predicate `canonMem`, recorded in the same module, spells out membership given the bits, the covers and the marker ends. "Minimum vertex cover" uses Mathlib's `SimpleGraph.vertexCoverNum`.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 4.3, p.19

import Mathlib
import Definitions.Def_MeanBudgetXC_HostV

namespace MeanBudgetXC

variable {n₀ t ℓ c niso : ℕ}

/-- Membership in a canonical choice (Section 4.3, p.19), given a source bit `β(s,i)` for every
path, a vertex set `C p` of the `p`-th padding copy and a chosen end `γ m` of every marker edge:
on the path of `(s,i)` select `{v_{i,0}, b_i}` (bit zero, positions `0, 2`) or `{a_i, v_{i,1}}`
(bit one, positions `1, 3`); select `C p` in the `p`-th padding copy; select the end `γ m` of the
`m`-th marker edge; select no isolated vertex. -/
def canonMem (β : Fin 2 × Fin n₀ → Bool) (C : Fin ℓ → Finset (Fin t)) (γ : Fin c → Fin 2) :
    HostV n₀ t ℓ c niso → Prop
  | .inl (s, i, k) => if β (s, i) then (k = 1 ∨ k = 3) else (k = 0 ∨ k = 2)
  | .inr (.inl (p, u)) => u ∈ C p
  | .inr (.inr (.inl (m, b))) => b = γ m
  | .inr (.inr (.inr _)) => False

/-- A **canonical choice** (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 4.3, p.19): on each source path select either
`{v_{i,0}, b_i}` or `{a_i, v_{i,1}}`, a minimum vertex cover in every padding copy, one end of
each marker edge, and no isolated vertices. -/
def IsCanonical (T : SimpleGraph (Fin t)) (S : Finset (HostV n₀ t ℓ c niso)) : Prop :=
  ∃ (β : Fin 2 × Fin n₀ → Bool) (C : Fin ℓ → Finset (Fin t)) (γ : Fin c → Fin 2),
    (∀ p, T.IsVertexCover (C p : Set (Fin t)) ∧ ((C p).card : ℕ∞) = T.vertexCoverNum) ∧
    ∀ x, x ∈ S ↔ canonMem β C γ x

end MeanBudgetXC


