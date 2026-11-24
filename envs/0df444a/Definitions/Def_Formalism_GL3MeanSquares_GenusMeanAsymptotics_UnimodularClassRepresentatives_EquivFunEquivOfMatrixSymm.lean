-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EquivFunEquivOfMatrixSymm
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EquivFunEquivOfMatrixSymm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:14.06231+00:00
-- url     : https://prove2.me/theorems/2b183128-c6bb-4f3a-802f-edca54a1efe6
-- title:
--   Equiv Fun Equiv Of Matrix Symm
-- statement:
--   Definitions and structural lemmas for Equiv Fun Equiv Of Matrix Symm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EquivFunEquivOfMatrixSymm.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeZeroOfNotMem
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
namespace Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
def gramK (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) : Matrix κ κ K := Matrix.of fun i j => h (b i) (b j)
def equivOfMatrix (b : Basis κ K V) (G G' : Matrix κ κ K) (hG : G * G' = 1) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (Matrix.toLin b b G) (Matrix.toLin b b G')
    (by rw [← Matrix.toLin_mul, hG, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul, mul_eq_one_comm.1 hG, Matrix.toLin_one])
end Formalism.HermitianLattices.Ext.L3.HU


