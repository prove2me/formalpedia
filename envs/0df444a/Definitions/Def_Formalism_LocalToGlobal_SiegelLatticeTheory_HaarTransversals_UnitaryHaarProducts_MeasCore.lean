-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_MeasCore
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_MeasCore
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:18.044157+00:00
-- url     : https://prove2.me/theorems/9931934c-f5fa-41ac-95a7-ea357a302d4e
-- title:
--   Meas Core
-- statement:
--   Definitions and structural lemmas for Meas Core, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/MeasCore.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_Measures
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
namespace Formalism.L2.SG.Pf.MeasCore
def StdCharExists : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ ∧
    ∀ x : Ainf F, psiInf F ψ x =
      Complex.exp (2 * Real.pi * Complex.I *
        ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))
def MWCore : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (P : Frame E n r) (T : F),
    IsCMExt F E σ → IsHermND σ J → P.IsStd σ J T →
    ∀ (μNinf : Measure (Nsub (Ainf F) σ J P)) (μHinf : Measure (Hsub (Ainf F) σ J P)),
      μNinf.IsHaarMeasure → μHinf.IsHaarMeasure →
      ∃ W : MeasW σ J P, W.IsTextNorm ∧ W.μNinf = μNinf ∧ W.μHinf = μHinf
end Formalism.L2.SG.Pf.MeasCore


