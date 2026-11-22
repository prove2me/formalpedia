-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoWeightedTprod
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoWeightedTprod
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:31:15.378999+00:00
-- url     : https://prove2.me/theorems/a3aff01f-a808-44ff-bdc7-6ba451f5c63c
-- title:
--   Tendsto Weighted Tprod
-- statement:
--   Definitions and structural lemmas for Tendsto Weighted Tprod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoWeightedTprod.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
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
variable {ι X : Type*} {q : ι → ℝ}
open scoped Classical in

def cut (ρ : ι → ℕ → ℝ) (S' : Finset ι) (i : ι) (j : ℕ) : ℝ := if i ∈ S' then ρ i j else 1
end Formalism.HermitianLattices.Ext.L3.A5


