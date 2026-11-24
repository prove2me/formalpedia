-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_ArchimedeanUniformConstantsCompactSupport
-- name    : Formalism_HermitianCurvature_ArchimedeanUniformConstantsCompactSupport
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T17:12:55.533602+00:00
-- url     : https://prove2.me/theorems/2cff28e4-21e6-4412-a426-afb6b3b65383
-- title:
--   Archimedean Uniform Constants Compact Support
-- statement:
--   Definitions and structural lemmas for Archimedean Uniform Constants Compact Support, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/ArchimedeanUniformConstantsCompactSupport.lean

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_StatementJCCpt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.KB
open Finset Filter Topology NumberField MeasureTheory Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Classical
def BuiltBounds2Cpt : Prop :=
  P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc C₄ : ℝ, 1 ≤ C₄ ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    IsLeadingFormSetting Cb Cc S p f χ A₀ →
      C.ThmPPos S ∧ IntAll S ∧ (∃ Lw, JC.WaveByPlaces S Lw ∧ JC.HidaCurvatureBarriers S Lw) ∧
      (∃ Ll Ll', JC.LiftBelowTop S Ll ∧ JC.LiftTopDiag S Ll' ∧ JC.ThresholdsLift S Ll Ll') ∧
      JC.SumFormConcrete S C₄
def ArchimedeanUniformConstantsCompactSupport : Prop :=
  P5.ThmPActualCpt → JC.RadialModuleForm → JC.PosDensityCpt → JC.FormLevSesqMM → JC.ThmPModuleOfActualCpt →
  D.MuRHaar → MA.LemmaEModel → JCT.LevelsActualBuilt → JCT.SlicesCCBuilt → JCT.ModelPlaceBuilt2 → Top.TopPSDT →
  BuiltBounds2Cpt →
  ∀ Cb : ℝ, ∃ C₆ Cc C₄ : ℝ, 0 < C₆ ∧ 1 ≤ C₄ ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ)
    (c : LE.Cut) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : TB.Pt E → H),
    IsLeadingFormPlace Cb Cc S p f χ A₀ → JCT.SliceBudget S A₀ → c.χ = χ →
    (∀ v, C₆ * ((S.G.k : ℝ) * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2 + (S.Ntop : ℝ) ^ 2 * ((S.G.r : ℝ) + 1) ^ 2) ≤
      S.cutHi v - S.cutLo v) →
    JCT.VtTensor S (plT S p) f (plν S p) (plm S p) Vt →
    ∃ (L : ∀ v : Fin S.f, R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
      (j : ∀ v : Fin S.f, M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT)
      (lam : ∀ v : Fin S.f, Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1) → ℝ) (Cm σ : Fin S.f → ℝ),
      (∀ v, JC.IsModelPlace S (plT S p) f χ v (L v) (j v) (lam v) c (Cm v) (σ v)) ∧
      ∀ Kr hK0 Th e, PB.RealInputs (S.mkData Kr hK0 Th e) C₄ (∏ v, JCT.jvModel S j Cm v) Vt
end
end Formalism.FourierDecayAlt.KB


