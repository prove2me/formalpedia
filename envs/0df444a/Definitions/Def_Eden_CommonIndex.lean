-- Prove2me | Definitions.Def_Eden_CommonIndex
-- name    : Eden_CommonIndex
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:03:44.269567+00:00
-- url     : https://prove2.me/theorems/4edfa5ec-57c8-4ec4-801e-28b3fc35a6e4
-- title:
--   Common Index
-- statement:
--   Definitions and structural lemmas for Common Index, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndex.lean

import Definitions.Def_Eden_ExponentSums
set_option autoImplicit true
noncomputable section
open Set
namespace Eden
def commonIndexCandidates (c : ℝ) : Set ℕ :=
  {k | k ≤ 4 ∧ supremumExponentSum c (k + 1) < 0}
def commonIndex (c : ℝ) : ℕ := sInf (commonIndexCandidates c)
def commonIndexRatio (c : ℝ) (p : PhaseSpace) : ℝ :=
  spectrumPartialSum (lyapunovExponent c p) (commonIndex c) /
    (-spectrumEntry (lyapunovExponent c p) (commonIndex c))
def commonIndexLocalDimension (c : ℝ) (p : PhaseSpace) : ℝ :=
  (commonIndex c : ℝ) + commonIndexRatio c p
def commonIndexDimension (c : ℝ) : ℝ :=
  (commonIndex c : ℝ) + sSup (commonIndexRatio c '' attractor)
end Eden


