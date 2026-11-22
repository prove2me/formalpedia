-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_SChain
-- name    : Formalism_SizeWindowBrackets_SChain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:51:48.018828+00:00
-- url     : https://prove2.me/theorems/25bb1cc0-9824-4261-b46f-4ccda3ca5002
-- title:
--   SChain
-- statement:
--   Definitions and structural lemmas for SChain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/SChain.lean

import Definitions.Def_Formalism_SizeWindowBrackets_QuotientSlopeBoundsWith
import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.LFunctionChainParameters.LChain
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
section
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
  {Top : Type} [Fintype Top] {m f : ℕ}
def SizeData₂ (Dd : Data U0 W Top m f) (C : Consts) (Xpp : ℝ) : Prop :=
  Dd.HidaSetting C ∧ Dd.DIV C ∧ EComp5 Dd C ∧ Dd.HComp C ∧ Count5 Dd C ∧ Dd.Slopes C ∧
  QuotientSlopeBoundsWith Dd C Xpp ∧ LossBounds Dd C ∧ Dd.SlopeIneq ∧ Dd.HHBound C ∧ Dd.FParams
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
def Ident {W : H → Type} {Top : Type} {m f : ℕ} (Dd : Data H W Top m f) (D : ArithData H) (N : ℕ)
    (ell : AddChar (E0 × H) ℂ → ℂ) (TT : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)) : Prop :=
  (∀ τ, Dd.aT τ = a (eT τ)) ∧ (∀ u0 j ρ, Dd.w u0 j ρ = w u0 j (eP ρ)) ∧
  Dd.gam = Real.eulerMascheroniConstant ∧ Dd.LpL = (ell chC).re ∧
  (∀ u0, Dd.ASK u0 = ∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w u0 j))
def BNBounds {W : H → Type} {Top : Type} {m f : ℕ} (Dd : Data H W Top m f) (T2 : Finset H) : Prop :=
  Dd.B0 ≤ (2 * (Fintype.card H : ℝ)) * m * Dd.b * Dd.x ^ Dd.ε ∧
  Dd.Nc ≤ (T2.card : ℝ) * Dd.k * Dd.b * Dd.x ^ Dd.ε
    / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * Dd.x ^ (-Dd.ε)))
def GrowthInequalitySizes {m : ℕ} (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (N : ℕ) (x b b' η X' θ : ℝ) : Prop :=
  0 ≤ η ∧ 0 < X' ∧ 0 < b' ∧ b' * X' ≤ x * b ∧ 0 ≤ θ ∧
  (∀ t ∈ TT, |a t / b - x| ≤ 1) ∧
  NodeSizes T2 b b' η w ∧
  (∀ u0 j t ρ, t ∈ TT → InPhi ρ → a t / w u0 j ρ ≤ N)
def GrowthInequalityRemainingHyps (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) {m : ℕ} (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (x ε b b' η X' θ CL : ℝ) : Prop :=
  GrowthInequalitySizes TT T2 a w N x b b' η X' θ ∧ ThinScales D ell X' θ ∧ ValuesAtX D ell x ε CL
end
def CostWindows (x f b η θ : ℝ) : Prop :=
  2 * f * (x + 1) * θ ≤ 1 / x ∧ 6 * f * (x + 1) * (η + 1) ≤ b / x
def RestSize (ε x : ℝ) (n nT nT2 m : ℕ) (b k aE : ℝ) : Prop :=
  aE ≤ 2 * x * b ∧
  x ^ (-(ε / 8)) * n / 2 ≤ nT ∧
  x ^ (-ε) ≤ (nT2 : ℝ) / n ∧
  x ^ ((1 : ℝ) / 2 - ε) ≤ m ∧
  k ≤ (n : ℝ) ^ 2 * x ^ ((1 : ℝ) / 2 - ε)
def ChainCore (eD eL K cHH eK CL ε x : ℝ) : Prop :=
  ∃ (H : Type) (_ : AddCommGroup H) (_ : Fintype H) (_ : DecidableEq H)
    (W : H → Type) (_ : ∀ u0, Fintype (W u0)) (_ : ∀ u0, Nonempty (W u0)) (Top : Type) (_ : Fintype Top)
    (m f : ℕ) (Dd : Data H W Top m f) (C : Consts) (Xpp : ℝ)
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)) (η X' θ : ℝ),
    Dd.x = x ∧ Dd.ε = ε ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧
    HostFacts D ∧
    Ident Dd D N ell TT a w eT eP ∧
    SizeData₂ Dd C Xpp ∧
    ErrWindows Dd C Xpp eK K ∧
    BNBounds Dd T2 ∧
    GrowthInequalityRemainingHyps D ell N TT T2 a w x ε Dd.b Dd.b' η X' θ CL ∧
    CostWindows x (fPl H) Dd.b η θ ∧
    RestSize ε x (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a
def XLarge (K cHH eK Cd CL ε x : ℝ) : Prop :=
  3 ≤ x ∧ 26 ≤ x ^ (3 * ε / 8) ∧ LargeX x ε K cHH eK ∧ moveCost x Cd CL ≤ x ^ ((1 : ℝ) / 2 + ε)
def XLargeEv : Prop :=
  ∀ K cHH eK Cd CL ε : ℝ, 0 < ε → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → XLarge K cHH eK Cd CL ε x
def ChainInputs (Cd eD eL ε x : ℝ) : Prop :=
  ∃ K cHH eK CL : ℝ, ChainCore eD eL K cHH eK CL ε x ∧ XLarge K cHH eK Cd CL ε x
def ChainTop : Prop :=
  ∀ Cd eD eL ε x : ℝ, ChainInputs Cd eD eL ε x → ReducedGrowthInequalityDataExists Cd (eD + eL + 3) ε x
def ChainAt : Prop :=
  ∃ Cd : ℝ, 0 ≤ Cd ∧
    ∀ eD eL ε x : ℝ, ChainInputs Cd eD eL ε x → Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε)
def ChainGivesRiemannHypothesis : Prop :=
  ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ChainInputs Cd eD eL ε x) →
    RiemannHypothesis
def ChainEventualGivesRiemannHypothesis : Prop :=
  ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ K cHH eK CL x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ChainCore eD eL K cHH eK CL ε x) →
    RiemannHypothesis
def GrowthHypothesesSplit : Prop :=
  ∀ {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ)
    {m : ℕ} (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (x ε b b' η X' θ Cd CL Err : ℝ),
    GrowthInequalityHypotheses D ell N TT T2 a w x ε b b' η X' θ Cd CL Err ↔
      (3 ≤ x ∧ 0 < b ∧ GrowthInequalityRemainingHyps D ell N TT T2 a w x ε b b' η X' θ CL ∧ topExcess D N ell TT a w ≤ Err ∧
        (0 ≤ Cd ∧ LipW D ell ∧ DerivInt D ell Cd))
def SmallCostsSplit : Prop :=
  ∀ x ε f b η θ Cd CL : ℝ,
    SmallCosts x ε f b η θ Cd CL ↔ (moveCost x Cd CL ≤ x ^ ((1 : ℝ) / 2 + ε) ∧ CostWindows x f b η θ)
def SizeWindowsSplit : Prop :=
  ∀ (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err : ℝ),
    SizeWindows C ε x n nT nT2 m b k aE Err ↔
      (RestSize ε x n nT nT2 m b k aE ∧ Err ≤ x ^ (C * ε) * errorBracketSizeWindows x ε n nT nT2 m b k aE ∧
        (3 ≤ x ∧ 26 ≤ x ^ (3 * ε / 8)) ∧
        (0 < ε ∧ 0 ≤ C ∧ 0 < n ∧ 0 < b ∧ 0 ≤ aE ∧ nT2 ≤ n ∧ (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2) ∧ x * m ≤ k))
def SameVisible {U0 : Type} {W W' : U0 → Type} {Top : Type} {m f : ℕ} (D1 : Data U0 W Top m f)
    (D0 : Data U0 W' Top m f) : Prop :=
  D1.x = D0.x ∧ D1.ε = D0.ε ∧ D1.a = D0.a ∧ D1.b = D0.b ∧ D1.b' = D0.b' ∧ D1.k = D0.k ∧ D1.L = D0.L ∧ D1.La = D0.La ∧
  D1.B0 = D0.B0 ∧ D1.Nc = D0.Nc ∧ D1.gam = D0.gam ∧ D1.LpL = D0.LpL ∧ D1.aT = D0.aT ∧ D1.w = D0.w ∧ D1.ASK = D0.ASK
def DataCompletion : Prop :=
  ∀ {U0 : Type} [Fintype U0] {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} (D0 : Data U0 W Top m f)
    (C : Consts) (Xpp : ℝ),
    0 < D0.x → 0 < D0.b → 0 ≤ D0.a → 0 ≤ D0.b' → 1 ≤ D0.k → 0 ≤ D0.La → 0 ≤ D0.B0 → 0 ≤ Xpp → 0 < f →
    (∀ t, 0 ≤ D0.aT t) → (∀ u0 j ρ, 0 < D0.w u0 j ρ) →
    (0 ≤ C.cE ∧ 0 ≤ C.cH ∧ 0 ≤ C.cCount ∧ 0 ≤ C.cSlope ∧ 0 ≤ C.cSl1 ∧ 0 ≤ C.cLoss) →
    (∀ u0, 0 ≤ ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D0.w u0 j ρ)) →
    (∀ u0, ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D0.w u0 j ρ) ≤ C.cCount * (m : ℝ) * D0.L) →
    (∀ u0, D0.ASK u0 ≤ D0.Main u0 + C.cDiv * D0.nT * D0.a * D0.La
      + C.cDiv * (m : ℝ) * (D0.B0 + D0.Nc) * D0.x ^ (C.eDiv * D0.ε) + D0.LoP C) →
    ∃ D1 : Data U0 (fun _ => Unit) Top m f, SameVisible D1 D0 ∧ D1.delBar = 0 ∧ D1.etaBar = 0 ∧ D1.eBar = 0 ∧
      SizeData₂ D1 C Xpp
def ChainCoreOfTop : Prop :=
  ∀ {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {Top : Type} [Fintype Top] {m f : ℕ}
    (D0 : Data H (fun _ => Unit) Top m f) (C : Consts) (Xpp eK K CL : ℝ)
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)) (η X' θ : ℝ),
    HostFacts D → Ident D0 D N ell TT a w eT eP → ErrWindows D0 C Xpp eK K → BNBounds D0 T2 →
    GrowthInequalityRemainingHyps D ell N TT T2 a w D0.x D0.ε D0.b D0.b' η X' θ CL → CostWindows D0.x (fPl H) D0.b η θ →
    RestSize D0.ε D0.x (Fintype.card H) TT.card T2.card m D0.b D0.k D0.a →
    (∀ u0, 0 ≤ ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D0.w u0 j ρ)) →
    (∀ u0, ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D0.w u0 j ρ) ≤ C.cCount * (m : ℝ) * D0.L) →
    (∀ u0, D0.ASK u0 ≤ D0.Main u0 + C.cDiv * D0.nT * D0.a * D0.La
      + C.cDiv * (m : ℝ) * (D0.B0 + D0.Nc) * D0.x ^ (C.eDiv * D0.ε) + D0.LoP C) →
    ChainCore C.eDiv C.eLoss K C.cHH eK CL D0.ε D0.x
def SizesModelAt (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] : Prop :=
  ∃ (Top : Type) (_ : Fintype Top) (m f : ℕ)
    (D0 : Data H (fun _ => Unit) Top m f) (C : Consts) (Xpp eK K : ℝ)
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)) (η X' θ : ℝ),
    HostFacts D ∧ Ident D0 D N ell TT a w eT eP ∧ ErrWindows D0 C Xpp eK K ∧ BNBounds D0 T2 ∧
    GrowthInequalitySizes TT T2 a w N D0.x D0.b D0.b' η X' θ ∧ 0 < θ ∧ CostWindows D0.x (fPl H) D0.b η θ ∧
    RestSize D0.ε D0.x (Fintype.card H) TT.card T2.card m D0.b D0.k D0.a ∧
    (∀ u0, 0 ≤ ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D0.w u0 j ρ)) ∧
    (∀ u0, ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D0.w u0 j ρ) ≤ C.cCount * (m : ℝ) * D0.L) ∧
    3 ≤ D0.x ∧ 26 ≤ D0.x ^ (3 * D0.ε / 8) ∧ LargeX D0.x D0.ε K C.cHH eK
def ChainSizesModel : Prop :=
  ∃ (H : Type) (_ : AddCommGroup H) (_ : Fintype H) (_ : DecidableEq H), SizesModelAt H
def CoreTopEach : Prop :=
  ∀ {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    {W : H → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
    (Dd : Data H W Top m f) (C : Consts) (Xpp : ℝ)
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)),
    Ident Dd D N ell TT a w eT eP → SizeData₂ Dd C Xpp →
    ∀ u0, (∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w u0 j)) ≤ Dd.Main u0 + ErrX5at Dd C Xpp u0
def CoreTopEachSized : Prop :=
  ∀ {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    {W : H → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
    (Dd : Data H W Top m f) (C : Consts) (Xpp eK K : ℝ)
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)),
    Ident Dd D N ell TT a w eT eP → SizeData₂ Dd C Xpp → ErrWindows Dd C Xpp eK K → BNBounds Dd T2 →
    LargeX Dd.x Dd.ε K C.cHH eK →
    ∀ u0, (∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w u0 j)) ≤ Dd.Main u0
      + Dd.x ^ (CErr C * Dd.ε) * errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a
def ChainCoreNoAnalytic (eD eL K cHH eK ε x : ℝ) : Prop :=
  ∃ (H : Type) (_ : AddCommGroup H) (_ : Fintype H) (_ : DecidableEq H)
    (W : H → Type) (_ : ∀ u0, Fintype (W u0)) (_ : ∀ u0, Nonempty (W u0)) (Top : Type) (_ : Fintype Top)
    (m f : ℕ) (Dd : Data H W Top m f) (C : Consts) (Xpp : ℝ)
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)) (η X' θ : ℝ),
    Dd.x = x ∧ Dd.ε = ε ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧
    HostFacts D ∧
    Ident Dd D N ell TT a w eT eP ∧
    SizeData₂ Dd C Xpp ∧
    ErrWindows Dd C Xpp eK K ∧
    BNBounds Dd T2 ∧
    GrowthInequalitySizes TT T2 a w N x Dd.b Dd.b' η X' θ ∧ 0 < θ ∧
    CostWindows x (fPl H) Dd.b η θ ∧
    RestSize ε x (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a
def ChainSizesModelEv : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ChainCoreNoAnalytic 1 1 1 1 2 ε x
def SizesTextAt (ε x : ℝ) : Prop :=
  ∃ (n : ℕ) (_ : NeZero n) (Top : Type) (_ : Fintype Top) (m f : ℕ)
    (D0 : Data (ZMod n) (fun _ => Unit) Top m f) (C : Consts) (Xpp : ℝ)
    (D : ArithData (ZMod n)) (ell : AddChar (E0 × ZMod n) ℂ → ℂ) (N : ℕ) (TT T2 : Finset (ZMod n)) (a : ZMod n → ℝ)
    (w : ZMod n → Fin m → E0 × ZMod n → ℝ) (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := ZMod n)) (η X' θ : ℝ),
    D0.x = x ∧ D0.ε = ε ∧
    (x ^ (2 + 8 * ε) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x ^ (2 + 8 * ε) ∧
      x ^ ((1 : ℝ) / 2 - ε / 16) ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 2 - ε / 16) ∧
      (TT.card : ℝ) < x ^ (-(ε / 8)) * (n : ℝ) / 2 + 1 ∧ (T2.card : ℝ) < x ^ (-ε) * (n : ℝ) + 1) ∧
    (D0.b = Real.exp (x ^ ε) ∧ D0.a = x * D0.b ∧ X' = Real.exp (x ^ (ε / 3)) ∧ D0.b' = D0.a / X' ∧
      Xpp = D0.a / (D0.b' / (x * (n : ℝ))) ∧ D0.k = x ^ ((9 : ℝ) / 2 + 10 * ε) ∧ D0.L = Real.log D0.b ∧
      D0.La = Real.log D0.a + x ^ (ε / 3) ∧ η = Real.exp (x ^ (ε / 4)) ∧ θ = Real.exp (-(x ^ (ε / 8))) ∧
      D0.etaBar = x ^ (-1 : ℝ)) ∧
    (D0.B0 = (2 * (n : ℝ)) * m * D0.b * x ^ ε ∧
      D0.Nc = (T2.card : ℝ) * D0.k * D0.b * x ^ ε / ((n : ℝ) * ((n : ℝ) * x ^ (-ε)))) ∧
    (C.eDiv ≤ 1 ∧ C.eLoss ≤ 1 ∧ C.cHH ≤ 1) ∧
    HostFacts D ∧ Ident D0 D N ell TT a w eT eP ∧ ErrWindows D0 C Xpp 15 2 ∧ BNBounds D0 T2 ∧
    GrowthInequalitySizes TT T2 a w N x D0.b D0.b' η X' θ ∧ CostWindows x (fPl (ZMod n)) D0.b η θ ∧
    RestSize ε x (Fintype.card (ZMod n)) TT.card T2.card m D0.b D0.k D0.a ∧
    (∀ u0, 0 ≤ ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D0.w u0 j ρ)) ∧
    (∀ u0, (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D0.w u0 j ρ)) ≤ C.cCount * (m : ℝ) * D0.L)
def ChainSizesTextEv : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → SizesTextAt ε x
def ChainEpsG : Prop :=
  ∀ eD eL ε : ℝ,
    (∃ K cHH eK CL x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ChainCore eD eL K cHH eK CL ε x) →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε)
def ChainEpsHalfPlane : Prop :=
  ∀ eD eL ε : ℝ,
    (∃ K cHH eK CL x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ChainCore eD eL K cHH eK CL ε x) →
    ∀ s : ℂ, (1 : ℝ) / 2 + (eD + eL + 6) * ε < s.re → riemannZeta s ≠ 0
def ChainCoreWeakL : Prop :=
  ∀ eD eL K cHH eK CL ε : ℝ, 0 < ε → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ChainCore eD eL K cHH eK CL ε x → ChainCore eD eL K cHH eK (x ^ ε / Real.log x) ε x
def ChainWeakLogDerivGivesRiemannHyp : Prop :=
  ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ K cHH eK x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ChainCore eD eL K cHH eK (x ^ ε / Real.log x) ε x) →
    RiemannHypothesis
end Formalism.LFunctionChainParameters.LChain


