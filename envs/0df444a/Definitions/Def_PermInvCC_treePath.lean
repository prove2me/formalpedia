-- Prove2me | Definitions.Def_PermInvCC_treePath
-- name    : PermInvCC_treePath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:24:19.510698+00:00
-- url     : https://prove2.me/theorems/4dca134d-1f11-4a81-ac34-5b26134d520d
-- title:
--   Tree paths $P_e$ and their minima $\lambda_e$
-- statement:
--   For a spanning tree $\tau$ of the bipartite symbol graph and a cell $e=(a,b)$, $P_e$ is the set of cells on the $\tau$-path joining $R_a$ and $K_b$, and for edge weights $C$
--   $$\lambda_e:=\min_{e'\in P_e}C_{e'}. \tag{4.7}$$
--
--   **Formalization Note** The path in a tree is unique; the definition returns $\emptyset$ if there is none (never for a spanning tree), and $\lambda_e$ is the infimum of natural numbers, the minimum on a nonempty path.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Lemma 4.5, eq. (4.7), p.18

import Mathlib
import Definitions.Def_PermInvCC_symbolGraph

namespace PermInvCC

open Classical in
/-- The **tree path** `P_e` (Y. Huang and Z. Ye, arXiv:2609.40116, held version sha256
fe1797dd…, Lemma 4.5, p.18): for a spanning tree `τ` of the bipartite symbol graph and a cell
`e = (a, b)`, the cells of the `τ`-path joining `R_a` and `K_b`.

**Formalization Note.** In a tree the path is unique; the definition picks a path in `τ` from
`R_a` to `K_b` and returns `∅` if there is none (never the case for a spanning tree). -/
noncomputable def treePath {q : ℕ} (τ : Finset (Fin q × Fin q)) (e : Fin q × Fin q) :
    Finset (Fin q × Fin q) :=
  if h : ∃ p : (symbolGraph τ).Walk (Sum.inl e.1) (Sum.inr e.2), p.IsPath then
    τ.filter fun e' => s(Sum.inl e'.1, Sum.inr e'.2) ∈ (Classical.choose h).edges
  else ∅

/-- `λ_e := min_{e'∈P_e} C_{e'}`, the smallest weight on the tree path (Lemma 4.5, eq. (4.7),
p.18).

**Formalization Note.** `sInf` of natural numbers; on the nonempty path of a non-tree cell it is
the minimum (`0` only on an empty path, which does not occur for a spanning tree). -/
noncomputable def lamE {q : ℕ} (τ : Finset (Fin q × Fin q)) (C : Fin q → Fin q → ℕ)
    (e : Fin q × Fin q) : ℕ :=
  sInf ((fun e' : Fin q × Fin q => C e'.1 e'.2) '' (treePath τ e : Set (Fin q × Fin q)))

end PermInvCC


