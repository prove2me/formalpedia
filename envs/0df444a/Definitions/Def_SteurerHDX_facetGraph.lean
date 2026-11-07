-- Prove2me | Definitions.Def_SteurerHDX_facetGraph
-- name    : SteurerHDX_facetGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:31:11.560205+00:00
-- url     : https://prove2.me/theorems/23b4013e-9697-49da-a9a7-0281fc549b80
-- title:
--   The support graph $G$ of the down-up walk
-- statement:
--   For a $d$-dimensional complex $\mathcal X$, $G$ is the graph on $\mathcal X(d)$ in which $\sigma\ne\tau$ are adjacent iff
--   $$|\tau\Delta\sigma|:=|\tau\setminus\sigma|+|\sigma\setminus\tau|=2 ,$$
--   i.e. iff the down-up walk can jump from $\sigma$ to $\tau$. Its shortest-path distance is written $\mathrm{dist}$.
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, proof of Theorem 3.1, p.5

import Mathlib
import Definitions.Def_SteurerHDX_faces

namespace SteurerHDX

/-- **The support graph G of the down-up walk.** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, proof of Theorem 3.1, p.5: "we
construct a graph G on vertex set X(d) which is the support graph of the down-up walk: Namely, we
connect σ, τ ∈ X(d) if |τΔσ| = 2", with "|τΔσ| := |τ ∖ σ| + |σ ∖ τ|" (p.4). -/
def facetGraph {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (d : ℕ) :
    SimpleGraph (faces X d) where
  Adj σ τ := (σ.1 \ τ.1).card + (τ.1 \ σ.1).card = 2
  symm := ⟨fun σ τ h => by simpa [add_comm] using h⟩
  loopless := ⟨fun σ h => by simp at h⟩

end SteurerHDX


