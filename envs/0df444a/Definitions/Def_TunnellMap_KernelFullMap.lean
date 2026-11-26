-- Prove2me | Definitions.Def_TunnellMap_KernelFullMap
-- name    : TunnellMap_KernelFullMap
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T16:12:33.059848+00:00
-- url     : https://prove2.me/theorems/42f7198c-209c-4f44-88f1-a3862d5e1025
-- title:
--   Kernel Full Map
-- statement:
--   Definitions and structural lemmas for Kernel Full Map, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelFullMap.lean

import Definitions.Def_TunnellMap_KernelPipeline
import Definitions.Def_TunnellMap_ComputableFullMap
set_option autoImplicit true
namespace TunnellMap
namespace RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}
def terminalRunK (hsq : Squarefree n) (fuel : ℕ) : DARun n :=
  runK (framesExecK hsq) fuel (DARun.initial (sourceRosterExec n))
def FuelSuffices (hsq : Squarefree n) (fuel : ℕ) : Prop :=
  (stepK (framesExecK hsq) (terminalRunK hsq fuel)).isNone = true
def residualMapExecK (hnpos : 0 < n) (hsq : Squarefree n)
    (fallback : AResidual n) (fuel : ℕ) (x : BResidual n) : AResidual n :=
  match (terminalRunK hsq fuel).assigned (canonicalBExec x) with
  | none => fallback
  | some r =>
      match aResidualOfTriple n r.target with
      | none => fallback
      | some F =>
          signActA hnpos
            (bResidualSignExec x * etaPointExec (canonicalBExec x) F) F
def inverseByRerunExecK (hsq : Squarefree n) (fallback : BResidual n)
    (fuel : ℕ) (y : AResidual n) : BResidual n :=
  ((terminalRunK hsq fuel).held
      (canonicalTargetLift (residualTargetLift y))).elim fallback
    fun p => signActB (targetLiftSign (residualTargetLift y) * p.2.sign) p.1
end RecordDA
variable {n : ℤ}
def oddMapExecK (hnpos : 0 < n) (hsq : Squarefree n) (fallback : AResidual n)
    (fuel : ℕ) (q : BOddRep n) : ARep n :=
  if hd : SourceUsedTriple q.1 then
    (directMapExec q).getD fallback.1
  else
    (RecordDA.residualMapExecK hnpos hsq fallback fuel
      ⟨q, fun hc => hd ((directSourceUsed_iff q).mp hc)⟩).1
def paperTunnellMapExecK (hnpos : 0 < n) (hsq : Squarefree n)
    (fallback : AResidual n) (fuel : ℕ) (p : BRep n) : ARep n :=
  if h : p.1.z % 2 = 0 then
    evenEquiv n (evenRepToParam ⟨p, Int.even_iff.mpr h⟩)
  else
    oddMapExecK hnpos hsq fallback fuel ⟨p.1, p.2, Int.odd_iff.mpr (by omega)⟩
end TunnellMap


