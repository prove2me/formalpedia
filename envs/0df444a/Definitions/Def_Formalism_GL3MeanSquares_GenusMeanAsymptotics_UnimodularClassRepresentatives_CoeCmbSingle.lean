-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CoeCmbSingle
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CoeCmbSingle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:40.238469+00:00
-- url     : https://prove2.me/theorems/46470a90-e618-4a70-b2cf-56a1b82a38a7
-- title:
--   Coe Cmb Single
-- statement:
--   Definitions and structural lemmas for Coe Cmb Single, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CoeCmbSingle.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMatrixOfIsom
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_conj

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
def cmb (b : Basis κ K V) (c : κ → 𝓞 K) : spanO b := (bO b).equivFun.symm c
def inA (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (b : Basis κ K V) : spanO b →ₗ[𝓞 K] ↥(locF 𝔭 (spanO b)) :=
  Submodule.inclusion (le_locF 𝔭 (spanO b))
abbrev QA (𝔭 : Ideal (𝓞 F)) (b : Basis κ K V) (k : ℕ) : Type :=
  ↥(locF 𝔭 (spanO b)) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 (spanO b)))
def eL {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (b : Basis κ K V) (k : ℕ) :
    Module.End (𝓞 K) (QA 𝔭 b k) ≃ Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  (quotLocF h𝔭 (spanO b) k).symm.conj.toEquiv.trans (eM b (extP K 𝔭 ^ k))
end Formalism.HermitianLattices.Ext.L3.HU


