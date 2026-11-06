-- Prove2me | Definitions.Def_SpatialSorting_IsScaffold
-- name    : SpatialSorting_IsScaffold
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:59.630183+00:00
-- url     : https://prove2.me/theorems/5f86a050-5b64-4c00-8322-7695ffd66f90
-- title:
--   Scaffolds (Definition 3.8)
-- statement:
--   A finite family $\mathcal S\subseteq\mathcal C$ of contours with supports in $D_L$ is a *scaffold* if
--
--   1. (W1) $\overline{\mathcal S}\cap\mathsf L_0=\emptyset$ and $\omega_{\mathcal S}\equiv0$ on $\overline{\mathcal S}\cap\mathsf L_1$;
--   2. (W2) $d(\overline\gamma,\overline{\gamma'})\ge2$ for distinct $\gamma,\gamma'\in\mathcal S$;
--   3. (W3) for each complementary component $V_k$ of $D_L\setminus\overline{\mathcal S}$ there is a label $j_k$ with $\omega_{\mathcal S}(s)=j_k$ for every $s\in\overline{\mathcal S}$ adjacent to $V_k$, and $j_0=0$ for the component $V_0$ containing $\mathsf L_0$.
--
--   Scaffolds are the closed contour selections on which the partition function factorizes over the complementary components.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 3.8, p. 19 (PDF p. 20)

import Mathlib
import Definitions.Def_SpatialSorting_D
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_IsContour
import Definitions.Def_SpatialSorting_supp
import Definitions.Def_SpatialSorting_Compatible
import Definitions.Def_SpatialSorting_Lay
import Definitions.Def_SpatialSorting_IsLabeling
open Classical Filter Topology

namespace SpatialSorting

/-- Definition 3.8: a finite family of contours with supports in `D_L` satisfying (W1)–(W3).

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 3.8, p. 19 (PDF p. 20). -/
def IsScaffold {q : ℕ} [NeZero q] (L : ℕ) (S : Finset (Contour q)) : Prop :=
  (∀ γ ∈ S, IsContour γ ∧ γ.support ⊆ D L) ∧
    Disjoint (supp S) (Lay 0 L) ∧
    (∀ γ ∈ S, ∀ s ∈ γ.support, s ∈ Lay 1 L → γ.color s = 0) ∧
    (∀ γ ∈ S, ∀ γ' ∈ S, γ ≠ γ' → Compatible γ γ') ∧
    ∃ lab, IsLabeling L S lab

end SpatialSorting


