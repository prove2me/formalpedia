-- Prove2me | Definitions.Def_Eden_FrequencyDimensions
-- name    : Eden_FrequencyDimensions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:20:08.49183+00:00
-- url     : https://prove2.me/theorems/a7e9a90c-6b63-5de3-b385-54d4be600210
-- title:
--   Frequency Dimensions
-- statement:
--   Definitions and structural lemmas for Frequency Dimensions, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyDimensions.lean

import Definitions.Def_Eden_FrequencySingularValues
import Definitions.Def_Eden_DimensionConvergence
set_option autoImplicit true
noncomputable section
open Set Filter Topology
namespace Eden
def frequencyFiniteTimeDimension (c ν t : ℝ) (p : PhaseSpace) : ℝ :=
  mapLyapunovDimension (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap
def frequencyGlobalLyapunovDimension (c ν : ℝ) (K : Set PhaseSpace) : ℝ :=
  sInf {v : ℝ | ∃ t : ℝ, 0 < t ∧ v = sSup (frequencyFiniteTimeDimension c ν t '' K)}
def frequencyLyapunovExponent (c ν : ℝ) (p : PhaseSpace) (i : Fin 5) : ℝ :=
  limUnder atTop (fun t : ℝ => Real.log
    ((fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues i) / t)
def frequencyAsymptoticDimension (c ν : ℝ) (p : PhaseSpace) : ℝ :=
  kaplanYorkeDimension (frequencyLyapunovExponent c ν p)
end Eden


