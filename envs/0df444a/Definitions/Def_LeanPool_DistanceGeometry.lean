-- Prove2me | Definitions.Def_LeanPool_DistanceGeometry
-- name    : LeanPool_DistanceGeometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:46:11.632763+00:00
-- url     : https://prove2.me/theorems/e35719fe-f505-4f4c-9d83-0013fc8be8fe
-- title:
--   Distance Geometry
-- statement:
--   Definitions and structural lemmas for Distance Geometry, from Egor Lyfar; LeanPool contributors's pinned Euclidean distance geometry development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry.lean

module
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
public import Definitions.Def_LeanPool_DistanceGeometry_Schoenberg
public import Definitions.Def_LeanPool_DistanceGeometry_SchoenbergHard
public import Definitions.Def_LeanPool_DistanceGeometry_Trilateration
public import Definitions.Def_LeanPool_DistanceGeometry_CayleyMengerVolume
public import Mathlib.Tactic.Positivity.Finset
set_option autoImplicit true
@[expose] public section
@[expose] public section


