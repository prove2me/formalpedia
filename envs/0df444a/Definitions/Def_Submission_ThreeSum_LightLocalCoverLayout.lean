-- Prove2me | Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout
-- name    : Submission_ThreeSum_LightLocalCoverLayout
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:07:22.641011+00:00
-- url     : https://prove2.me/theorems/a5821a92-e271-452d-a3f7-9a6fa86c56f0
-- title:
--   Light Local Cover Layout
-- statement:
--   Definitions and structural lemmas for Light Local Cover Layout, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverLayout.lean

import Definitions.Def_Submission_ThreeSum_LightLocalCoverBuild
set_option autoImplicit false
namespace ThreeSum.LightLocalCoverLayout
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
def vertices (h : ℕ) : ℕ := LocalMaskGraph.vertexCount (512*h) h
def bitPtr (base h : ℕ) : ℕ := base+vertices h
def maps (base h : ℕ) : ℕ := bitPtr base h+vertices h*(512*h)
def raw0 (base h : ℕ) : ℕ := maps base h+rows h*(2*(512*h))
def raw1 (base h : ℕ) : ℕ := raw0 base h+2*vertices h
def hist0 (base h : ℕ) : ℕ := raw1 base h+2*vertices h
def hist1 (base h : ℕ) : ℕ := hist0 base h+rows h*localPrime h
def matrixPtr (base h : ℕ) : ℕ := hist1 base h+rows h*localPrime h
def work (base h : ℕ) : ℕ := matrixPtr base h+rows h*cols h
def scheduleMaps (base h : ℕ) : ℕ :=
  work base h+LightCoverGreedy.total (rows h) (cols h) (scheduleSize h)
def candidates (base h : ℕ) : ℕ := LightCoverGreedy.out (work base h) (rows h) (cols h)
def space (base h : ℕ) : ℕ :=
  max (LightLocalCoverCandidate.space (work base h) (512*h) (vertices h) (localPrime h))
    (scheduleMaps base h+scheduleSize h*(2*(512*h)))
end ThreeSum.LightLocalCoverLayout


