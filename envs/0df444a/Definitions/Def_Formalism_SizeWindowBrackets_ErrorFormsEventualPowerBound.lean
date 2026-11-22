-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsEventualPowerBound
-- name    : Formalism_SizeWindowBrackets_ErrorFormsEventualPowerBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:40:26.759145+00:00
-- url     : https://prove2.me/theorems/26c9679b-1629-43bc-aea0-05c1158e0a69
-- title:
--   Error Forms Eventual Power Bound
-- statement:
--   Definitions and structural lemmas for Error Forms Eventual Power Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ErrorFormsEventualPowerBound.lean

import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
namespace Formalism.LFunctionChainParameters.LErr7
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.LErr
noncomputable section
def CErr7 (C : Consts) : ℝ := max (C.eDiv + 1) (max (C.eLoss + 2) 3)
def CErrValues : Prop :=
  (∀ C : Consts, C.eDiv = 2 → C.eLoss = 0 → CErr7 C = 3) ∧
  (∀ C : Consts, C.eDiv ≤ 2 → C.eLoss ≤ 1 → CErr7 C = 3) ∧
  (∀ C : Consts, 3 ≤ CErr7 C) ∧
  (∀ C : Consts, 0 ≤ C.eLoss → CErr7 C ≤ max (C.eDiv + 1) (C.eLoss + 3)) ∧
  (∀ C : Consts, 0 ≤ C.eDiv → 0 ≤ C.eLoss → CErr7 C ≤ CErr C)
def ErrorFormsAnyExponent : Prop :=
  ∀ {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts) (Xpp eK K c : ℝ),
    ErrWindows D C Xpp eK K → LargeX D.x D.ε K C.cHH eK →
    C.eDiv + 1 ≤ c → C.eLoss + 2 ≤ c → 3 ≤ c →
    errorTermWith D C Xpp ≤ D.x ^ (c * D.ε) * ErrText D ∧
    ∀ u0, ErrX5at D C Xpp u0 ≤ D.x ^ (c * D.ε) * ErrText D
def ErrorTermPowerBound : Prop :=
  ∀ {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ),
    ErrWindows D C Xpp eK K → LargeX D.x D.ε K C.cHH eK →
    errorTermWith D C Xpp ≤ D.x ^ (CErr7 C * D.ε) * ErrText D
def ErrorFormsEachTranslate : Prop :=
  ∀ {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ),
    ErrWindows D C Xpp eK K → LargeX D.x D.ε K C.cHH eK →
    ∀ u0, ErrX5at D C Xpp u0 ≤ D.x ^ (CErr7 C * D.ε) * ErrText D
def ErrorFormsExponentThree : Prop :=
  ∀ {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ),
    ErrWindows D C Xpp eK K → LargeX D.x D.ε K C.cHH eK → C.eDiv ≤ 2 → C.eLoss ≤ 1 →
    errorTermWith D C Xpp ≤ D.x ^ (3 * D.ε) * ErrText D ∧
    ∀ u0, ErrX5at D C Xpp u0 ≤ D.x ^ (3 * D.ε) * ErrText D
def ErrorFormsEventualPowerBound : Prop :=
  ∀ ε K cHH eK : ℝ, 0 < ε → ∃ x₀ : ℝ,
    ∀ {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
      {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ),
      D.ε = ε → C.cHH = cHH → x₀ ≤ D.x → ErrWindows D C Xpp eK K →
      errorTermWith D C Xpp ≤ D.x ^ (CErr7 C * D.ε) * ErrText D ∧
      ∀ u0, ErrX5at D C Xpp u0 ≤ D.x ^ (CErr7 C * D.ε) * ErrText D
def ErrorFormsSizeBound : Prop :=
  ∀ ε K cHH eK : ℝ, 0 < ε → ∃ x₀ : ℝ,
    ∀ {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
      {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts) (Xpp n lrd : ℝ),
      D.ε = ε → C.cHH = cHH → x₀ ≤ D.x → TextSizes D C Xpp eK K n lrd →
      errorTermWith D C Xpp ≤ D.x ^ (CErr7 C * D.ε) * ErrText D ∧
      ∀ u0, ErrX5at D C Xpp u0 ≤ D.x ^ (CErr7 C * D.ε) * ErrText D
def ExponentSevenErrorLeError : Prop :=
  ∀ {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ),
    ErrWindows D C Xpp eK K →
    D.x ^ (CErr7 C * D.ε) * ErrText D ≤ D.x ^ (CErr C * D.ε) * ErrText D
def TopLineThree : Prop :=
  ∀ {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ),
    D.HidaSetting C → D.DIV C → EComp5 D C → D.HComp C → Count5 D C → D.Slopes C →
    QuotientSlopeBoundsWith D C Xpp → LossBounds D C → D.SlopeIneq → D.HHBound C → D.FParams →
    ErrWindows D C Xpp eK K → LargeX D.x D.ε K C.cHH eK → C.eDiv ≤ 2 → C.eLoss ≤ 1 →
    ∀ u0, D.ASK u0 ≤ D.Main u0 + D.x ^ (3 * D.ε) * ErrText D
def DivisionBoundOfExplicitInequality : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts) (c : ℝ),
    0 ≤ D.x → 0 ≤ D.a → 0 ≤ D.La → 0 ≤ D.B0 + D.Nc → c ≤ C.cDiv → 1 ≤ C.cDiv → C.eDiv = 2 →
    (∀ u0 (u : W u0), D.muCC u0 + D.h u0 u - D.Fo u0 ≤
      (∑ t, ((m : ℝ) * (ph (D.aT t) - D.aT t * D.logOm) - D.aT t * Real.log (D.T u0 u)))
        + c * D.nT * D.a * D.La + (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (2 * D.ε)) →
    D.DIV C
def LoPZero : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts),
    C.eLoss = 0 → D.LoP C = C.cLoss * D.nT * (m : ℝ) * D.b
def DivisionLossTermsSumLeErrorTerm : Prop :=
  ∀ {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ),
    ErrWindows0 D C Xpp eK K →
    C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε) + D.LoP C + (m : ℝ) * C.cE * D.B0 ≤ errorTermWith D C Xpp
def DivisionTermLeErrorTerm : Prop :=
  ∀ {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ),
    ErrWindows0 D C Xpp eK K →
    C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε) ≤ errorTermWith D C Xpp
def LossTermLeErrorTerm : Prop :=
  ∀ {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ),
    ErrWindows0 D C Xpp eK K →
    D.LoP C ≤ errorTermWith D C Xpp
def ErrExpBelow : Prop :=
  ∀ {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ),
    ErrWindows D C Xpp eK K → LargeX D.x D.ε K C.cHH eK →
    errorTermWith D C Xpp ≤ D.x ^ (max C.eDiv (max (C.eLoss + 2) 3) * D.ε) * ErrText D
def ErrExpBelowFalse : Prop := ¬ ErrExpBelow
def ErrExpBelowOnes : Prop :=
  ∀ {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ),
    ErrWindows D C Xpp eK K → LargeX D.x D.ε K C.cHH eK →
    (C.cDiv = 1 ∧ C.cE = 1 ∧ C.cH = 1 ∧ C.cCount = 1 ∧ C.cSlope = 1 ∧ C.cSl1 = 1 ∧ C.cLoss = 1) →
    errorTermWith D C Xpp ≤ D.x ^ (max C.eDiv (max (C.eLoss + 2) 3) * D.ε) * ErrText D
def ErrExpBelowOnesFalse : Prop := ¬ ErrExpBelowOnes
def ErrWindowsModel' : Prop :=
  ∃ (D : Data Unit (fun _ => Unit) Unit 1 1) (C : Consts) (Xpp eK K : ℝ),
    ErrWindows D C Xpp eK K ∧ LargeX D.x D.ε K C.cHH eK ∧ 0 < D.etaBar ∧ C.eDiv = 2 ∧ C.eLoss = 0 ∧
    C.cDiv = 1 ∧ C.cE = 1 ∧ C.cH = 1 ∧ C.cCount = 1 ∧ C.cSlope = 1 ∧ C.cSl1 = 1 ∧ C.cLoss = 1 ∧
    D.ε < 1 / 52 ∧ 0 < D.B0 ∧ 0 < D.Nc
def SizesSat : Prop :=
  ∀ x₀ : ℝ, ∃ (D : Data Unit (fun _ => Unit) Unit 1 1) (C : Consts) (Xpp n lrd : ℝ),
    x₀ ≤ D.x ∧ D.ε = 1 / 100 ∧ C.cHH = 1 ∧ C.eDiv = 2 ∧ C.eLoss = 0 ∧ TextSizes D C Xpp 1 1 n lrd
section
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
def LeadingTermGrowthJointExponentSeven : Prop :=
  LeadingTermTranslateMean (H := H) →
  ∀ {W : H → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
    (Dd : Data H W Top m f) (C : Consts) (Xpp eK K : ℝ)
    (D : ArithData H) (N : ℕ) (ell : AddChar (E0 × H) ℂ → ℂ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)),
    MeanBoundWith Dd C Xpp →
    Dd.HidaSetting C → Dd.DIV C → EComp5 Dd C → Dd.HComp C → Count5 Dd C → Dd.Slopes C →
    QuotientSlopeBoundsWith Dd C Xpp → LossBounds Dd C → Dd.SlopeIneq → Dd.HHBound C → Dd.FParams →
    ErrWindows Dd C Xpp eK K → LargeX Dd.x Dd.ε K C.cHH eK →
    Dd.B0 ≤ (2 * (Fintype.card H : ℝ)) * m * Dd.b * Dd.x ^ Dd.ε →
    Dd.Nc ≤ (T2.card : ℝ) * Dd.k * Dd.b * Dd.x ^ Dd.ε
      / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * Dd.x ^ (-Dd.ε))) →
    (∀ τ, Dd.aT τ = a (eT τ)) → (∀ u0 j ρ, Dd.w u0 j ρ = w u0 j (eP ρ)) →
    Dd.gam = Real.eulerMascheroniConstant → Dd.LpL = (ell chC).re →
    (∀ u0, Dd.ASK u0 = ∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w u0 j)) →
    topExcess D N ell TT a w ≤
      Dd.x ^ (CErr7 C * Dd.ε) * errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a
end
end
end Formalism.LFunctionChainParameters.LErr7


