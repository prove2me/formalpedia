-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEleventh
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEleventh
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:11:18.499632+00:00
-- url     : https://prove2.me/theorems/4378b0d7-5153-4d22-aee7-170a0cfce706
-- title:
--   Local Density Eleventh
-- statement:
--   Definitions and structural lemmas for Local Density Eleventh, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensityEleventh.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.vectorCountBounds
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms hermitianFormColumns
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
def nkB (𝔭 : Ideal (𝓞 F)) (k c : ℕ) (H : Matrix m m (𝓞 K)) (n : 𝓞 F) : ℕ :=
  Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // ¬ Qc 𝔭 k c H x ∧
    fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)}
end Formalism.HermitianLattices.Ext.L3.vectorCountBounds


