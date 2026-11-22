-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqPairs
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqPairs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:43:21.609108+00:00
-- url     : https://prove2.me/theorems/7f444e17-bb39-4b8e-8dd0-3f567cb3d2b8
-- title:
--   MSq Pairs
-- statement:
--   Definitions and structural lemmas for MSq Pairs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPairs.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace Pairs
def tPart (m₀ n : ℕ) : ℕ :=
  if Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀ then 1 else n.minFac
def aW (c : ℕ → ℝ) (p n : ℕ) : ℝ := if IsPrimePow n ∧ n.minFac = p then c n else 0
def gW (c : ℕ → ℝ) (m₀ n : ℕ) : ℝ :=
  if IsPrimePow n ∧ (Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀) then c n else 0
end Pairs
open Pairs
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds


