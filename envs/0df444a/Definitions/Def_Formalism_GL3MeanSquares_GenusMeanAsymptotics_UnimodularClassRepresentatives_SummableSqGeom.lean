-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:24:47.600797+00:00
-- url     : https://prove2.me/theorems/cf4ae446-b9ae-4a04-8779-1784e42932da
-- title:
--   Summable Sq Geom
-- statement:
--   Definitions and structural lemmas for Summable Sq Geom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SummableSqGeom.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.A5
variable {ι : Type*}
def ebox (s : Finset ι) (J : ι → ℕ) : Finset (ι →₀ ℕ) := s.finsupp fun i => range (J i + 1)
def dif (R : ι → ℕ → ℝ) (i : ι) : ℕ → ℝ
  | 0 => 1
  | j + 1 => R i (j + 1) - R i j
def cGeom : ℝ := ∑' j : ℕ, 8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j
variable {q : ι → ℝ}
def nrm (q : ι → ℝ) (v : ι →₀ ℕ) : ℝ := v.prod fun i e => q i ^ e
end Formalism.HermitianLattices.Ext.L3.A5


