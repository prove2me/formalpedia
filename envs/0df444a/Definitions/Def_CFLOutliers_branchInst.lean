-- Prove2me | Definitions.Def_CFLOutliers_branchInst
-- name    : CFLOutliers_branchInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:37:23.760046+00:00
-- url     : https://prove2.me/theorems/0bf9075f-c12c-43d1-ab21-eb4c04c20bcf
-- title:
--   The modified instance of a facility-cost guess
-- statement:
--   For a guess $i_0$ of a facility of maximum opening cost in an optimal solution, set $M=f_{i_0}$. The **modified instance** of the branch $i_0$ discards every facility with $f_i>M$ and makes $i_0$ free: its facilities are the retained facilities $\{i: f_i\le f_{i_0}\}$, with the original distances and capacities, opening cost $0$ at $i_0$ and $f_i$ elsewhere; clients and quota are unchanged.
--
--   A solution of the modified instance is read back as a solution of the original instance with the same open facilities and assignment; its cost there is the cost with the original opening costs restored.
--
--   **Formalization Note** The retained facilities are renumbered $0,\dots,m'-1$ ($m'\le m$) by a fixed bijection `keptEmb`; discarded facilities do not exist in the modified instance.
-- source:
--   R. Dabas, A Constant-Factor Approximation for Capacitated Facility Location with Outliers, arXiv:2611.04094 (preprint; held version, sha256 613f7405…9798), §2.2 "Absorbing the opening charge", p.6; Appendix B, p.14

import Mathlib
import Definitions.Def_CFLOutliers_Sol

namespace CFLOutliers

open Finset

open Classical in
/-- The facilities retained in the branch of guess `i₀`: those with `f_i ≤ f_{i₀}`. -/
noncomputable def kept (I : Inst) (i0 : Fin I.m) : Finset (Fin I.m) :=
  univ.filter (fun i => I.f i ≤ I.f i0)

/-- The retained facilities, renumbered `0, …, m' − 1` (`m' = |kept|`), as original facilities. -/
noncomputable def keptEmb (I : Inst) (i0 : Fin I.m) (k : Fin (kept I i0).card) : Fin I.m :=
  ((kept I i0).equivFin.symm k).1

theorem keptEmb_injective (I : Inst) (i0 : Fin I.m) : Function.Injective (keptEmb I i0) := by
  intro a b h
  exact (kept I i0).equivFin.symm.injective (Subtype.ext h)

/-- **The modified instance of the branch `i₀`** (§2.2 "Absorbing the opening charge", p.6, and
Appendix B, p.14): with `M = f_{i₀}`, "discard facilities costing more than M, and temporarily
make i₀ free". Clients, distances, capacities and the quota are unchanged.

**Formalization Note.** Discarded facilities are removed: the branch instance has the
`m' = |{i : f_i ≤ f_{i₀}}| ≤ m` retained facilities, renumbered by `keptEmb`; its opening costs
are those of the original instance except `f_{i₀} := 0`. -/
noncomputable def branchInst (I : Inst) (i0 : Fin I.m) : Inst where
  m := (kept I i0).card
  n := I.n
  c x y := I.c (Sum.map (keptEmb I i0) id x) (Sum.map (keptEmb I i0) id y)
  f k := if keptEmb I i0 k = i0 then 0 else I.f (keptEmb I i0 k)
  u k := I.u (keptEmb I i0 k)
  q := I.q

/-- A solution of a branch instance read as a solution of the original instance (the same open
facilities and assignment; its `cost` there is the cost with the original opening costs
restored). -/
noncomputable def liftSol {I : Inst} {i0 : Fin I.m} (S : Sol (branchInst I i0)) : Sol I where
  openSet := S.openSet.image (keptEmb I i0)
  σ j := (S.σ j).map (keptEmb I i0)

end CFLOutliers


