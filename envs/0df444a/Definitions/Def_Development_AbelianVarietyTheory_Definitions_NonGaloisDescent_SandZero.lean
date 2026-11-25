-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SandZero
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SandZero
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:48:46.59266+00:00
-- url     : https://prove2.me/theorems/05a51f4c-ccd2-44fa-918a-64fbe1d8fa30
-- title:
--   Sand Zero
-- statement:
--   Definitions and structural lemmas for Sand Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/SandZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsOfLayers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HWL
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s} {R : WSer Γ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {I : WIo R RA RW inclR φR gR πA} {E : WEt I} {Zl : Type} [CommRing Zl] {zl : PowerSeries Zl →+* LetA O n}
def Sand (Mo : WN E zl) (T : LocLat G Qp LL O) (w : RA) : Prop :=
  (∀ x ∈ Mo.N T, ∃ y : TW RA T, TWincl inclR T y = inclR w • E.jD T x) ∧
    ∀ t : ↥T.L.T, inclR w • ((1 : RW) ⊗ₜ[O] t : TW RW T) ∈
      Submodule.span O {z : TW RW T | ∃ (a : RA), ∃ y ∈ Mo.N T, z = inclR a • E.jD T y}
end GlobalTheory.HWL


