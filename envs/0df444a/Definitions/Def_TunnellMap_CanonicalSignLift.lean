-- Prove2me | Definitions.Def_TunnellMap_CanonicalSignLift
-- name    : TunnellMap_CanonicalSignLift
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T15:02:12.998746+00:00
-- url     : https://prove2.me/theorems/360cde25-ab85-4554-928a-605f14a20de3
-- title:
--   Canonical Sign Lift
-- statement:
--   Definitions and structural lemmas for Canonical Sign Lift, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
set_option autoImplicit true
namespace TunnellMap
namespace FreeInvolution
variable {X : Type*} (I : FreeInvolution X)
def signAct (σ : ℤ) (x : X) : X := if σ = 1 then x else I.neg x
section Key
variable {K : Type*} [LinearOrder K]
def signOf (key : X → K) (x : X) : ℤ := if key x < key (I.neg x) then 1 else -1
end Key
end FreeInvolution
variable {n : ℤ}
abbrev signActB (σ : ℤ) (x : BResidual n) : BResidual n :=
  (bResidualInvolution n).signAct σ x
abbrev signActA {n : ℤ} (hnpos : 0 < n) (σ : ℤ) (y : AResidual n) : AResidual n :=
  (aResidualInvolution n hnpos).signAct σ y
def bResidualSign (x : BResidual n) : ℤ :=
  (bResidualInvolution n).signOf bResidualLexKey x
def aResidualSign {n : ℤ} (hnpos : 0 < n) (y : AResidual n) : ℤ :=
  (aResidualInvolution n hnpos).signOf aResidualLexKey y
noncomputable def etaPoint {n : ℤ} (s : BResidual n) (t : AResidual n) : ℤ :=
  if directionKey (plusVector s t) < directionKey (minusVector s t) then 1 else -1
def etaPointExec {n : ℤ} (s : BResidual n) (t : AResidual n) : ℤ :=
  if keyLtExec (directionKeyExec (plusVector s t))
      (directionKeyExec (minusVector s t)) then 1 else -1
noncomputable def canonicalEta {n : ℤ} (hnpos : 0 < n)
    (q : (bResidualInvolution n).Orbit)
    (o : (aResidualInvolution n hnpos).Orbit) : ℤ :=
  etaPoint (canonicalBResidualRepresentative q)
    (canonicalAResidualRepresentative hnpos o)
noncomputable def signedPartner {n : ℤ} (hnpos : 0 < n) (s : BResidual n)
    (t : AResidual n) : AResidual n :=
  signActA hnpos (etaPoint s t) t
noncomputable def canonicalResidualMapOf {n : ℤ} (hnpos : 0 < n)
    (M : (bResidualInvolution n).Orbit ≃ (aResidualInvolution n hnpos).Orbit)
    (x : BResidual n) : AResidual n :=
  signActA hnpos
    (bResidualSign x *
      canonicalEta hnpos ((bResidualInvolution n).orbit x)
        (M ((bResidualInvolution n).orbit x)))
    (canonicalAResidualRepresentative hnpos
      (M ((bResidualInvolution n).orbit x)))
namespace FreeInvolution
variable {X Y : Type*} (I : FreeInvolution X) (J : FreeInvolution Y)
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
end FreeInvolution
section Agreement
variable {n : ℤ} (hnpos : 0 < n) [Fintype (BOddRep n)] [Fintype (ARep n)]
end Agreement
end TunnellMap


