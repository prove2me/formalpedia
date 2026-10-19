-- Prove2me | Definitions.Def_AngelDevil_ReducedJourney
-- name    : AngelDevil_ReducedJourney
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-18T12:57:20.329816+00:00
-- url     : https://prove2.me/theorems/7f9bf1fe-1d1f-4577-abc5-4386445c58ca
-- title:
--   Earliest-predecessor reduction of finite Angel journeys
-- statement:
--   A total recursive implementation of the reduced journey in Mathe Section 2, equation (1). At each endpoint it chooses the earliest reachable predecessor in the original prefix, recursively reduces that prefix, and appends the endpoint. Empty and malformed histories have explicit fallback cases; proved correctness for valid journeys is a separate theorem.
-- source:
--   Mathe, The Angel of power 2 wins (2007), https://doi.org/10.1017/S0963548306008303, author manuscript p. 3, equation (1).

import Definitions.Def_AngelDevil_Game

namespace AngelDevil

instance jumpDecidable (p : Nat) (u v : Point) : Decidable (Jump p u v) := by
  unfold Jump
  infer_instance

def firstReachable (p : Nat) (h : List Point) (z : Point) : Nat :=
  h.findIdx (fun v => decide (Jump p v z))

/- Section 2, equation (1). The recursive predecessor is the earliest point in
the ORIGINAL prefix that can reach the endpoint, not an arbitrary loop erasure.
The singleton fallback only specifies a total function on malformed journeys.
-/
def reducedJourney (p : Nat) (h : List Point) : List Point :=
  if _hnil : h = [] then [] else
  let z := h.getLastD origin
  if z = origin then [origin] else
  let prior := h.dropLast
  let i := firstReachable p prior z
  if i < prior.length then
    reducedJourney p (prior.take (i+1)) ++ [z]
  else [z]
termination_by h.length
decreasing_by
  have hpos : 0 < h.length := List.length_pos_iff.mpr _hnil
  simp only [List.length_take, List.length_dropLast]
  omega

end AngelDevil


