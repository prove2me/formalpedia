-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
-- name    : Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:48:14.812054+00:00
-- url     : https://prove2.me/theorems/505d5288-94de-472b-bb23-42b8c761aa05
-- title:
--   Error Forms Weak Windows False
-- statement:
--   Definitions and structural lemmas for Error Forms Weak Windows False, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean

import Definitions.Def_Formalism_SizeWindowBrackets_QuotientSlopeBoundsWith
import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
namespace Formalism.LFunctionChainParameters.LErr
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
noncomputable section
section
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
def ErrText (D : Data U0 W Top m f) : ℝ :=
  D.nT * D.a * (1 + (m : ℝ) ^ 2 / D.k) + (m : ℝ) * (D.B0 + D.Nc)
def CErr (C : Consts) : ℝ := C.eDiv + C.eLoss + 3
def KBig (K cHH eK : ℝ) : ℝ := 200 * (1 + K) ^ 2 * (1 + cHH) * (1 + eK)
def ConstsBound (C : Consts) (K : ℝ) : Prop :=
  0 ≤ C.cDiv ∧ C.cDiv ≤ K ∧ 0 ≤ C.cE ∧ C.cE ≤ K ∧ 0 ≤ C.cH ∧ C.cH ≤ K ∧
  0 ≤ C.cCount ∧ C.cCount ≤ K ∧ 0 ≤ C.cSlope ∧ C.cSlope ≤ K ∧ 0 ≤ C.cSl1 ∧ C.cSl1 ≤ K ∧
  0 ≤ C.cLoss ∧ C.cLoss ≤ K ∧ 0 ≤ C.eDiv ∧ 0 ≤ C.eLoss ∧ 0 ≤ C.cHH
def ErrWindows0 (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ) : Prop :=
  1 ≤ D.x ∧ 0 < D.ε ∧ D.ε ≤ 1 ∧
  1 ≤ D.b ∧ D.x * D.b ≤ D.a ∧
  1 ≤ D.nT ∧
  (m : ℝ) ≤ D.x ^ ((1 : ℝ) / 2 + D.ε / 2) ∧ D.x * m ≤ D.k ∧
  0 ≤ eK ∧ 1 ≤ D.k ∧ D.k ≤ D.x ^ eK ∧ D.k ≤ D.a ∧
  0 ≤ D.L ∧ D.L ≤ 2 * D.x ^ D.ε ∧ 0 ≤ D.La ∧ D.La ≤ 2 * D.x ^ D.ε ∧
  0 ≤ D.b' ∧ D.k * D.b' ≤ D.a ∧
  0 ≤ Xpp ∧ Xpp ≤ D.a ∧
  (∀ t, 0 ≤ D.aT t ∧ D.aT t ≤ 2 * D.a) ∧
  0 ≤ D.B0 ∧ 0 ≤ D.Nc ∧
  (∀ u0, Real.log (Fintype.card (W u0) : ℝ) ≤ (D.k - 3) * Real.log 2) ∧
  D.delBar ≤ 1 / 2 ∧ 0 ≤ D.etaBar ∧ 0 ≤ D.eBar ∧
  ConstsBound C K
def ErrWindows (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ) : Prop :=
  ErrWindows0 D C Xpp eK K ∧
  (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b) ≤ K * D.x ^ D.ε * (D.nT * D.a)
def ErrWindowsWeak (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ) : Prop :=
  ErrWindows0 D C Xpp eK K ∧ D.etaBar ≤ 1 ∧ D.eBar ≤ 1
end
def LargeX (x ε K cHH eK : ℝ) : Prop := Real.log x ≤ x ^ ε ∧ KBig K cHH eK ≤ x ^ ε
def ErrorFormsUnderWindows : Prop :=
  ∀ {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ),
    ErrWindows D C Xpp eK K → LargeX D.x D.ε K C.cHH eK →
    errorTermWith D C Xpp ≤ D.x ^ (CErr C * D.ε) * ErrText D
def ErrorFormsWeakWindowsFalse : Prop :=
  ∀ {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ),
    ErrWindowsWeak D C Xpp eK K → LargeX D.x D.ε K C.cHH eK →
    errorTermWith D C Xpp ≤ D.x ^ (CErr C * D.ε) * ErrText D
def TraceTermLeErrorTerm : Prop :=
  ∀ {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ),
    ErrWindows0 D C Xpp eK K → 0 ≤ D.delBar →
    (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b) ≤ errorTermWith D C Xpp
def ErrWindowsModel : Prop :=
  ∃ (D : Data Unit (fun _ => Unit) Unit 1 1) (C : Consts) (Xpp eK K : ℝ),
    ErrWindows D C Xpp eK K ∧ LargeX D.x D.ε K C.cHH eK ∧ 0 < D.etaBar ∧
    C.cDiv = 1 ∧ C.cE = 1 ∧ C.cH = 1 ∧ C.cCount = 1 ∧ C.cSlope = 1 ∧ C.cSl1 = 1 ∧ C.cLoss = 1
def LargeXEv : Prop :=
  ∀ ε K cHH eK : ℝ, 0 < ε → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → LargeX x ε K cHH eK
def ErrorFormsEventual : Prop :=
  ∀ ε K cHH eK : ℝ, 0 < ε → ∃ x₀ : ℝ,
    ∀ {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
      {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ),
      D.ε = ε → C.cHH = cHH → x₀ ≤ D.x → ErrWindows D C Xpp eK K →
      errorTermWith D C Xpp ≤ D.x ^ (CErr C * D.ε) * ErrText D
def bTx (x ε : ℝ) : ℝ := Real.exp (x ^ ε)
def aTx (x ε : ℝ) : ℝ := x * bTx x ε
def XpTx (x ε : ℝ) : ℝ := Real.exp (x ^ (ε / 3))
def bpTx (x ε : ℝ) : ℝ := aTx x ε / XpTx x ε
def wppTx (x ε n : ℝ) : ℝ := bpTx x ε / (x * n)
def XppTx (x ε n : ℝ) : ℝ := aTx x ε / wppTx x ε n
def TextSizesWindows : Prop :=
  ∀ ε e : ℝ, 0 < ε → ∃ x₀ : ℝ, ∀ x k n lrd : ℝ, x₀ ≤ x → 0 < k → k ≤ x ^ e → 0 < n → n ≤ x ^ e →
    lrd ≤ x ^ (ε / 3) →
    1 ≤ x ∧ 1 ≤ bTx x ε ∧ Real.log (bTx x ε) = x ^ ε ∧ Real.log (aTx x ε) + lrd ≤ 2 * x ^ ε ∧
    k ≤ aTx x ε ∧ 0 ≤ bpTx x ε ∧ k * bpTx x ε ≤ aTx x ε ∧
    0 ≤ XppTx x ε n ∧ XppTx x ε n ≤ aTx x ε
def TextSizes {U0 : Type} {W : U0 → Type} [∀ u0, Fintype (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
    (D : Data U0 W Top m f) (C : Consts) (Xpp eK K n lrd : ℝ) : Prop :=
  D.b = bTx D.x D.ε ∧ D.a = aTx D.x D.ε ∧ D.b' = bpTx D.x D.ε ∧ Xpp = XppTx D.x D.ε n ∧
  D.L = Real.log D.b ∧ D.La = Real.log D.a + lrd ∧ 0 ≤ lrd ∧ lrd ≤ D.x ^ (D.ε / 3) ∧
  0 < n ∧ n ≤ D.x ^ eK ∧ D.ε ≤ 1 ∧
  1 ≤ D.nT ∧
  (m : ℝ) ≤ D.x ^ ((1 : ℝ) / 2 + D.ε / 2) ∧ D.x * m ≤ D.k ∧
  0 ≤ eK ∧ 1 ≤ D.k ∧ D.k ≤ D.x ^ eK ∧
  (∀ t, 0 ≤ D.aT t ∧ D.aT t ≤ 2 * D.a) ∧
  0 ≤ D.B0 ∧ 0 ≤ D.Nc ∧
  (∀ u0, Real.log (Fintype.card (W u0) : ℝ) ≤ (D.k - 3) * Real.log 2) ∧
  D.delBar ≤ 1 / 2 ∧ 0 ≤ D.etaBar ∧ 0 ≤ D.eBar ∧
  (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b) ≤ K * D.x ^ D.ε * (D.nT * D.a) ∧
  ConstsBound C K
def ErrorFormsEventualUnderSizeParameters : Prop :=
  ∀ ε K cHH eK : ℝ, 0 < ε → ∃ x₀ : ℝ,
    ∀ {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
      {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts) (Xpp n lrd : ℝ),
      D.ε = ε → C.cHH = cHH → x₀ ≤ D.x → TextSizes D C Xpp eK K n lrd →
      errorTermWith D C Xpp ≤ D.x ^ (CErr C * D.ε) * ErrText D
section
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
def errorBracketSizeWindows (x ε : ℝ) (n nT nT2 m : ℕ) (b k aE : ℝ) : ℝ :=
  (nT : ℝ) * aE * (1 + (m : ℝ) ^ 2 / k)
    + m * ((2 * n) * m * b * x ^ ε + nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε))))
def SizeWindowsOfBracket : Prop :=
  ∀ (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err0 : ℝ), SizeWindows C ε x n nT nT2 m b k aE Err0 →
    SizeWindows C ε x n nT nT2 m b k aE (x ^ (C * ε) * errorBracketSizeWindows x ε n nT nT2 m b k aE)
def LeadingTermGrowthJoint : Prop :=
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
      Dd.x ^ (CErr C * Dd.ε) * errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a
end
end
end Formalism.LFunctionChainParameters.LErr


