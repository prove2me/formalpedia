-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_Residue
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:53.478251+00:00
-- url     : https://prove2.me/theorems/3369411d-231d-42cc-8a1d-98e04eff2d0d
-- title:
--   Residue
-- statement:
--   Definitions and structural lemmas for Residue, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Residue.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
namespace GroundTheory.Global
namespace Elliptic
def dslopeIter (p : ℂ) (k : ℕ) (g : ℂ → ℂ) : ℂ → ℂ :=
  (Function.swap dslope p)^[k] g
open Classical in

def meromorphicShift (f : ℂ → ℂ) (p : ℂ) : ℕ :=
  if h : MeromorphicAt f p then Nat.find h else 0
def laurentNumerator (f : ℂ → ℂ) (p : ℂ) : ℂ → ℂ :=
  fun z ↦ (z - p) ^ (meromorphicShift f p + 1) * f z
def laurentCoeff (f : ℂ → ℂ) (p : ℂ) (j : ℕ) : ℂ :=
  dslopeIter p j (laurentNumerator f p) p
def residue (f : ℂ → ℂ) (p : ℂ) : ℂ :=
  laurentCoeff f p (meromorphicShift f p)
def principalPart (f : ℂ → ℂ) (p : ℂ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (meromorphicShift f p + 1),
    laurentCoeff f p j * ((z - p) ^ (meromorphicShift f p + 1 - j))⁻¹
def regularPart (f : ℂ → ℂ) (p : ℂ) : ℂ → ℂ :=
  dslopeIter p (meromorphicShift f p + 1) (laurentNumerator f p)
end Elliptic
end GroundTheory.Global


