-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiagQConjTranspose
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiagQConjTranspose
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T11:13:05.236274+00:00
-- url     : https://prove2.me/theorems/f1d3392f-09cf-4b22-9876-874260b65a04
-- title:
--   Diag QConj Transpose
-- statement:
--   Definitions and structural lemmas for Diag QConj Transpose, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiagQConjTranspose.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantNormShapesBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
namespace Formalism.L2.SG.Pf.discriminantNormShapes
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
def SolveOnto : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k → ∀ Y : udPre K 𝔭 k a,
      ∃ Y' P W Z Z₀ : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k),
        Y' - Y.1 = Z₀ * diagQ K 𝔭 k a ∧ P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y' ∧
        Y'ᴴ * diagQ K 𝔭 k a * Y' - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a ∧
        W + Pᴴ * Z + Zᴴ * P + Zᴴ * diagQ K 𝔭 k a * Z = 0
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}
end Formalism.L2.SG.Pf.discriminantNormShapes


