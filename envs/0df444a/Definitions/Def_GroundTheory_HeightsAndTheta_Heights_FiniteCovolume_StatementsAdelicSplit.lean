-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdelicSplit
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdelicSplit
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T02:02:56.885407+00:00
-- url     : https://prove2.me/theorems/81ec3ed3-94e9-552b-b474-ae5228f7f0e6
-- title:
--   Statements Adelic Split
-- statement:
--   Definitions and structural lemmas for Statements Adelic Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsAdelicSplit.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Statements
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans
import Theorems.Thm_GroundTheory_Automorphic_isUnit_det_gram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory IsDedekindDomain
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
def adeleSplit (h : HermitianForm F E W) (v : Basis ι E W) :
    unitaryPoints F E (gram h.toSesq v) 𝔸[F] ≃ₜ*
      unitaryPoints F E (gram h.toSesq v) (InfiniteAdeleRing F) ×
        unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F) :=
  (unitaryCongr (gram h.toSesq v) (adeleRingEquivProd F) (by exact continuous_id)
      (by exact continuous_id)).trans
    (unitaryProdEquiv F (gram h.toSesq v) _ _ (isUnit_det_gram h v))
def ArchimedeanUnitaryEquiv.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∃ ψ : unitaryPoints F E (gram h.toSesq v) (InfiniteAdeleRing F) ≃ₜ* archUnitary h v,
    ∀ γ : h.unitaryGroup, ψ (adeleSplit h v (hermitianDiagonal h v γ)).1 = archEmbed h v γ
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


