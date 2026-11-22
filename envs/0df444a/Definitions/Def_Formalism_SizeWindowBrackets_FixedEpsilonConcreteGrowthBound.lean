-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_FixedEpsilonConcreteGrowthBound
-- name    : Formalism_SizeWindowBrackets_FixedEpsilonConcreteGrowthBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:43.074089+00:00
-- url     : https://prove2.me/theorems/6469ef7c-9236-4285-8686-20e840e47a96
-- title:
--   Fixed Epsilon Concrete Growth Bound
-- statement:
--   Definitions and structural lemmas for Fixed Epsilon Concrete Growth Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/FixedEpsilonConcreteGrowthBound.lean

import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsEventualPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesFromSizeAndCount
import Definitions.Def_Formalism_SizeWindowBrackets_PowerBoundGivesRiemannHypothesis
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
namespace Formalism.LFunctionChainParameters.LTop7
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LErr7
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LChain6
def cTop7 (eD eL : ℝ) : ℝ := max (eD + 1) (max (eL + 2) 3)
def CTop7Values : Prop :=
  cTop7 2 0 = 3 ∧
  (∀ eD eL : ℝ, eD ≤ 2 → eL ≤ 1 → cTop7 eD eL = 3) ∧
  (∀ eD eL : ℝ, 3 ≤ cTop7 eD eL) ∧
  (∀ eD eL eD' eL' : ℝ, eD ≤ eD' → eL ≤ eL' → cTop7 eD eL ≤ cTop7 eD' eL') ∧
  (∀ C : Consts, CErr7 C = cTop7 C.eDiv C.eLoss) ∧
  (∀ eD eL : ℝ, 0 ≤ eD → 0 ≤ eL → cTop7 eD eL ≤ eD + eL + 3)
def CoreTopEachSized7 : Prop :=
  ∀ {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    {W : H → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
    (Dd : Data H W Top m f) (C : Consts) (Xpp eK K : ℝ)
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)),
    Ident Dd D N ell TT a w eT eP → SizeData₂ Dd C Xpp → ErrWindows Dd C Xpp eK K → BNBounds Dd T2 →
    LargeX Dd.x Dd.ε K C.cHH eK →
    ∀ u0, (∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w u0 j)) ≤ Dd.Main u0
      + Dd.x ^ (CErr7 C * Dd.ε) * errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a
def PropTL7 : Prop :=
  ∀ {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    {W : H → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
    (Dd : Data H W Top m f) (C : Consts) (Xpp eK K : ℝ)
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)),
    Ident Dd D N ell TT a w eT eP → SizeData₂ Dd C Xpp → ErrWindows Dd C Xpp eK K → BNBounds Dd T2 →
    LargeX Dd.x Dd.ε K C.cHH eK → C.eDiv ≤ 2 → C.eLoss ≤ 1 →
    ∀ u0, (∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w u0 j)) ≤ Dd.Main u0
      + Dd.x ^ (3 * Dd.ε) * errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a
section DataT
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}
def TopOfInputs2Sized7 : Prop :=
  ∀ (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m)
    (η θ eK K CL : ℝ), Inputs2 D ell G C cT N TT T2 a w Fm η θ eK K CL → LargeX G.x G.ε K C.cHH eK →
    ∀ u0, (∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w u0 j))
      ≤ (mkData G C.cHH D ell N TT T2 a w Fm).Main u0
        + G.x ^ (CErr7 C * G.ε)
          * errorBracketSizeWindows G.x G.ε (Fintype.card H) TT.card T2.card m (bTx G.x G.ε) G.k (aTx G.x G.ε)
end DataT
def ChainTop7 : Prop :=
  ∀ Cd eD eL ε x : ℝ, ChainInputs Cd eD eL ε x → ReducedGrowthInequalityDataExists Cd (cTop7 eD eL) ε x
def ChainAt7 : Prop :=
  ∃ Cd : ℝ, 0 ≤ Cd ∧
    ∀ eD eL ε x : ℝ, ChainInputs Cd eD eL ε x → Gz x ≤ x ^ ((1 : ℝ) / 2 + (cTop7 eD eL + 3) * ε)
def ExponentSevenBoundLeEarlierBound : Prop :=
  ∀ eD eL ε x : ℝ, 0 ≤ eD → 0 ≤ eL → 0 ≤ ε → 1 ≤ x →
    x ^ ((1 : ℝ) / 2 + (cTop7 eD eL + 3) * ε) ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε)
def ChainCoreMono : Prop :=
  ∀ eD eL eD' eL' K cHH eK CL ε x : ℝ, eD ≤ eD' → eL ≤ eL' →
    ChainCore eD eL K cHH eK CL ε x → ChainCore eD' eL' K cHH eK CL ε x
def FixedEpsilonGrowthBound : Prop :=
  ∀ eD eL ε : ℝ,
    (∃ K cHH eK CL x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ChainCore eD eL K cHH eK CL ε x) →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → Gz x ≤ x ^ ((1 : ℝ) / 2 + (cTop7 eD eL + 3) * ε)
def ChainEpsHalfPlane7 : Prop :=
  ∀ eD eL ε : ℝ,
    (∃ K cHH eK CL x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ChainCore eD eL K cHH eK CL ε x) →
    ∀ s : ℂ, (1 : ℝ) / 2 + (cTop7 eD eL + 3) * ε < s.re → riemannZeta s ≠ 0
def Core6ToCore : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ A K cHH eK eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ eD eL CL x : ℝ, x₁ ≤ x → Chain6Core A Cord eD eL K cHH eK CL eW KW ε x →
      ChainCore eD eL K cHH eK CL ε x
def Core6'ToCore : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ A K cHH eK eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ eD eL CL x : ℝ, x₁ ≤ x → Chain6Core' A Cord eD eL K cHH eK CL eW KW ε x →
      ChainCore eD eL K cHH eK CL ε x
def Chain6AtTop7 : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK CL eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → Chain6Core A Cord eD eL K cHH eK CL eW KW ε x →
      Gz x ≤ x ^ ((1 : ℝ) / 2 + (cTop7 eD eL + 3) * ε)
def Chain6At'Top7 : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK CL eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → Chain6Core' A Cord eD eL K cHH eK CL eW KW ε x →
      Gz x ≤ x ^ ((1 : ℝ) / 2 + (cTop7 eD eL + 3) * ε)
def GrowthBoundAndRiemannHypothesis : Prop :=
  (∀ ε : ℝ, 0 < ε → ε < 1 / 52 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → Gz x ≤ x ^ ((1 : ℝ) / 2 + 6 * ε)) ∧
  (∀ s : ℂ, (1 : ℝ) / 2 < s.re → riemannZeta s ≠ 0) ∧
  RiemannHypothesis
def RiemannHypothesisOfEventualGrowthBound : Prop :=
  (∀ ε : ℝ, 0 < ε → ε < 1 / 52 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → Gz x ≤ x ^ ((1 : ℝ) / 2 + 6 * ε)) → GrowthBoundAndRiemannHypothesis
def GrowthBoundSmallExponents : Prop :=
  ∀ eD eL ε : ℝ, eD ≤ 2 → eL ≤ 1 →
    (∃ K cHH eK CL x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ChainCore eD eL K cHH eK CL ε x) →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → Gz x ≤ x ^ ((1 : ℝ) / 2 + 6 * ε)
def RiemannHypothesisOfChainCore : Prop :=
  (∀ ε : ℝ, 0 < ε → ε < 1 / 52 →
    ∃ K cHH eK CL x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ChainCore 2 0 K cHH eK CL ε x) → GrowthBoundAndRiemannHypothesis
def FixedEpsilonConcreteGrowthBound : Prop :=
  ∀ eD eL ε : ℝ,
    (∃ K cHH eK CL x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → Chain2Core eD eL K cHH eK CL ε x) →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → Gz x ≤ x ^ ((1 : ℝ) / 2 + (cTop7 eD eL + 3) * ε)
def RiemannHypothesisOfConcreteChain : Prop :=
  (∀ ε : ℝ, 0 < ε → ε < 1 / 52 →
    ∃ K cHH eK CL x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → Chain2Core 2 0 K cHH eK CL ε x) → GrowthBoundAndRiemannHypothesis
def RiemannHypothesisOfComposedChain : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧
    ((∀ ε : ℝ, 0 < ε → ε < 1 / 52 →
      ∃ A K cHH eK CL eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x → Chain6Core A Cord 2 0 K cHH eK CL eW KW ε x) → GrowthBoundAndRiemannHypothesis)
def RiemannHypothesisOfComposedChain' : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧
    ((∀ ε : ℝ, 0 < ε → ε < 1 / 52 →
      ∃ A K cHH eK CL eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x → Chain6Core' A Cord 2 0 K cHH eK CL eW KW ε x) → GrowthBoundAndRiemannHypothesis)
def ChainSizesModelEv7 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ChainCoreNoAnalytic 2 0 1 1 2 ε x
end Formalism.LFunctionChainParameters.LTop7


