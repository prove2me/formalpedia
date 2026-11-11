-- Prove2me | Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Richness
-- name    : SymmetricDepthHierarchy_ConstantDepth_Richness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:01.919344+00:00
-- url     : https://prove2.me/theorems/ef7d711b-c3d5-4ca0-bcbc-69191beb1d56
-- title:
--   $(\Delta,k)$-rich graphs
-- statement:
--   Let $k\ge1$. A graph $F$ is **$(1,k)$-rich** if some connected component of $F$ has at least $k+1$ vertices. For $\Delta\ge2$, a connected graph $F$ is **$(\Delta,k)$-rich** if it contains $k+1$ pairwise vertex-disjoint connected subgraphs each of which is $(\Delta-1,k)$-rich. A disconnected graph is $(\Delta,k)$-rich if it has a $(\Delta,k)$-rich connected component.
--
--   Richness is the obstruction dual to $\Delta$-forestwidth (Lemma B.10) and is preserved backwards along weak oddomorphisms (Theorem B.17).
--
--   **Formalization Note.** `RichConn Δ k G` is the clause for a connected graph and `Rich Δ k G` asks that some connected component satisfy it. Subgraphs are arbitrary (not necessarily induced) subgraphs. Richness is not defined for $\Delta=0$ (it is `False`).
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), Definition B.9, p. 34 (PDF p. 37)

import Mathlib

open scoped Classical

noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth

/-!
# `(Δ, k)`-rich graphs

STOC 2027 submission #1521, Definition B.9 (printed p. 34, PDF p. 37):

> Let `k ≥ 1`. A graph `F` is `(1, k)`-rich if some connected component of `F` has at least `k + 1`
> vertices. For `Δ ≥ 2`, a connected graph `F` is `(Δ, k)`-rich if it contains `k + 1` pairwise
> vertex-disjoint connected subgraphs each of which is `(Δ − 1, k)`-rich. A disconnected graph is
> `(Δ, k)`-rich if it has a `(Δ, k)`-rich connected component.

`RichConn Δ k G` is the clause for a connected graph `G`; `Rich Δ k G` holds iff some connected
component of `G` (the whole graph, if `G` is connected) satisfies it. Subgraphs are Mathlib
subgraphs (not necessarily induced). Richness is not defined for `Δ = 0` (`False`).
-/

/-- The richness clause for a connected graph `G` on `V`. -/
def RichConn : ℕ → ℕ → (V : Type) → SimpleGraph V → Prop
  | 0, _, _, _ => False
  | 1, k, V, _ => k + 1 ≤ Nat.card V
  | Δ + 2, k, _, G =>
      ∃ H : Fin (k + 1) → G.Subgraph,
        (∀ i, (H i).Connected) ∧
        (Pairwise fun i j => Disjoint (H i).verts (H j).verts) ∧
        ∀ i, ∃ c : (H i).coe.ConnectedComponent,
          RichConn (Δ + 1) k c.supp ((H i).coe.induce c.supp)

/-- `G` is `(Δ, k)`-rich: some connected component of `G` satisfies the richness clause. -/
def Rich (Δ k : ℕ) {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ c : G.ConnectedComponent, RichConn Δ k c.supp (G.induce c.supp)

end SymmetricDepthHierarchy.ConstantDepth


