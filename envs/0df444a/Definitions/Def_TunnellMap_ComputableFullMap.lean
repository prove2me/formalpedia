-- Prove2me | Definitions.Def_TunnellMap_ComputableFullMap
-- name    : TunnellMap_ComputableFullMap
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T16:08:50.403239+00:00
-- url     : https://prove2.me/theorems/4e6bd05e-a9e5-459a-ae1c-7aa05e6582c7
-- title:
--   Computable Full Map
-- statement:
--   Definitions and structural lemmas for Computable Full Map, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableFullMap.lean

import Definitions.Def_TunnellMap_ComputableDirect
import Definitions.Def_TunnellMap_ComputablePipeline
import Definitions.Def_TunnellMap_FullAssembly
set_option autoImplicit true
namespace TunnellMap
variable {n : ℤ}
def oddMapExec (hnpos : 0 < n) (hsq : Squarefree n) (fallback : AResidual n)
    (q : BOddRep n) : ARep n :=
  if hd : SourceUsedTriple q.1 then
    (directMapExec q).getD fallback.1
  else
    (RecordDA.residualMapExec hnpos hsq fallback
      ⟨q, fun hc => hd ((directSourceUsed_iff q).mp hc)⟩).1
section Agreement
variable [Fintype (BOddRep n)] [Fintype (ARep n)]
end Agreement
def paperTunnellMapExec (hnpos : 0 < n) (hsq : Squarefree n)
    (fallback : AResidual n) (p : BRep n) : ARep n :=
  if h : p.1.z % 2 = 0 then
    evenEquiv n (evenRepToParam ⟨p, Int.even_iff.mpr h⟩)
  else
    oddMapExec hnpos hsq fallback ⟨p.1, p.2, Int.odd_iff.mpr (by omega)⟩
section FullAgreement
variable [Fintype (BRep n)] [Fintype (ARep n)]
end FullAgreement
end TunnellMap


