-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_SlopesFromSizeAndCount
-- name    : Formalism_SizeWindowBrackets_SlopesFromSizeAndCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:06:14.902096+00:00
-- url     : https://prove2.me/theorems/8cf23cfb-6319-4a41-9531-d050928f8f68
-- title:
--   Slopes From Size And Count
-- statement:
--   Definitions and structural lemmas for Slopes From Size And Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/SlopesFromSizeAndCount.lean

import Definitions.Def_Formalism_SizeWindowBrackets_Chain2aCoreNoAnalytic
import Definitions.Def_Formalism_SizeWindowBrackets_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_SizeWindowBrackets_SBrDiv
import Definitions.Def_Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBracketBoundOfSizeWindows
import Definitions.Def_Formalism_SizeWindowBrackets_SSmall
import Definitions.Def_Formalism_SizeWindowBrackets_JointCSlopeExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix IsDedekindDomain
open Formalism.HN
noncomputable section
namespace Formalism.LFunctionChainParameters.LChain6
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
def HostAn (c' : ℝ) : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (C : ℝ) (q d : ℕ) [Fact q.Prime] [Fact d.Prime], PrimePairBounds ε C x q d →
      FrobeniusOrbits.HostHyp q d ∧ ∀ e : ℕ, ((2 ^ e : ℕ) : ℝ) ≤ x ^ A →
        ThinScales (hostData e q d) (hostEll e q d) (XpTx x ε) (Real.exp (-c' * x ^ (ε / 8))) ∧
        ValuesAtX (hostData e q d) (hostEll e q d) x ε C
structure Rows {I : Type} {m : ℕ} (F : Fam I m) where

  D : ℕ

  XE : InfinitePlace F.K → Matrix (Fin D) (Fin D) ℂ

  R : Submodule (𝓞 F.K) (Fin D → F.K)

  ψ : Module.Dual F.K (Fin D → F.K) →ₗ[F.K] F.Wd
namespace Fam6
variable {I : Type} {m : ℕ} (F : Fam I m)
def FoAll : ℝ :=
  ∑ j, ∑ᶠ z : HeightOneSpectrum (𝓞 F.K), lw z * (if plOf z ∈ F.S then ramE (plOf z) * F.Fj j (plOf z) else 0)
def EAll (u : I) (j : Fin m) : ℝ :=
  ∑ᶠ z : HeightOneSpectrum (𝓞 F.K), lw z * (if plOf z ∈ F.S then ramE (plOf z) * F.Ej u j (plOf z) else 0)
def sMean [Fintype I] : ℝ := WeightedMeanLemmas.sF F.du (fun u => muDef (F.b u) (F.X u) (F.N' u)) F.h
end Fam6
section Defs
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}
def budgetAtPoint (H : Type) [Fintype H] (G : Glob) (m : ℕ) : ℝ :=
  (2 * (Fintype.card H : ℝ)) * (m : ℝ) * Real.exp (G.x ^ G.ε) * G.x ^ G.ε
def NcTx (G : Glob) (T2 : Finset H) : ℝ :=
  (T2.card : ℝ) * G.k * bTx G.x G.ε * G.x ^ G.ε / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * G.x ^ (-G.ε)))
def topPhi (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] : H ↪ PhiSet (H := H) :=
  ⟨fun t => ⟨topPl t, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩, fun _ _ h => congrArg (fun z => z.1.2) h⟩
def aPhi (a : H → ℝ) : PhiSet (H := H) → ℝ := fun ρ => a ρ.1.2
def DivIn (G : Glob) (C : Consts) (TT T2 : Finset H) (a : H → ℝ) (Fm : ∀ u0, Fam (W u0) m)
    (Rw : ∀ u0, Rows (Fm u0)) (logOm C0 : ℝ) (g₁ g₂ : ℕ) : Prop :=
  (∀ u0, 0 < (Rw u0).D ∧ (∀ v, IsUnit ((Rw u0).XE v).det) ∧ Submodule.IsLattice (Fm u0).K (Rw u0).R ∧
    RowsAreDual (Fm u0) (Rw u0).XE (Rw u0).R (Rw u0).ψ) ∧
  50 * C0 + 10 ≤ C.cDiv ∧ 9 * C0 ^ 2 + 6 * C0 + 20 ≤ C.cE ∧ 7 * C0 ^ 2 + 18 ≤ C.cH ∧
  (∀ u0 (u : W u0), ThmConcl (TT.map (topPhi H)) (aPhi a)
    (lcv (Rw u0).XE (Rw u0).R / ((Rw u0).D : ℝ)) ((Fm u0).h u) (Fam6.FoAll (Fm u0))
    (Real.log ((Fm u0).T u : ℝ)) logOm (m : ℝ) (G.x * Real.exp (G.x ^ G.ε)) G.La
    (budgetAtPoint H G m) (NcTx G T2) (G.x ^ (C.eDiv * G.ε)) C0) ∧
  (∀ u0 (u : W u0), TypePrimeCostDeviationBound (TT.map (topPhi H)) (aPhi a) (Fam6.EAll (Fm u0) u)
    (Real.log ((g₁ : ℝ) * (g₂ : ℝ))) (m : ℝ) (budgetAtPoint H G m) C0) ∧
  (∀ u0, CorrectedHeightVariationBound (TT.map (topPhi H)) (Fm u0).h (fun u => Real.log ((Fm u0).T u : ℝ)) (fun _ => aPhi a)
    (G.x * Real.exp (G.x ^ G.ε)) G.La (budgetAtPoint H G m) (m : ℝ) C0) ∧
  (∀ u0, muMaxDef (Pi.basisFun (Fm u0).K (Fin (Rw u0).D)) (Rw u0).XE (Rw u0).R + Fam6.sMean (Fm u0)
    ≤ G.x ^ C.cHH * bTx G.x G.ε)
def DivOfDivIn : Prop :=
  ∀ (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (Rw : ∀ u0, Rows (Fm u0)) (logOm C0 : ℝ) (g₁ g₂ : ℕ),
    0 ≤ G.x → 0 ≤ G.k → 0 ≤ G.La → G.lg = Real.log ((g₁ : ℝ) * (g₂ : ℝ)) → (∀ u0 v, IsUnit ((Fm u0).X' v).det) →
    DivIn G C TT T2 a Fm Rw logOm C0 g₁ g₂ →
    DivAt (mkData G C.cHH D ell N TT T2 a w Fm) C logOm ∧
    EComp5 (mkData G C.cHH D ell N TT T2 a w Fm) C ∧
    (mkData G C.cHH D ell N TT T2 a w Fm).HComp C ∧
    (∀ u0, (mkData G C.cHH D ell N TT T2 a w Fm).s u0 - muMinDef (Fm u0).b' (Fm u0).X' (Fm u0).cc
      ≤ G.x ^ C.cHH * bTx G.x G.ε)
def Inputs6a (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (Rw : ∀ u0, Rows (Fm u0))
    (η θ eK K logOm C0 : ℝ) (g₁ g₂ : ℕ) : Prop :=
  (∀ u0, (Fm u0).LatHyp (sgX G C.cHH)) ∧
  (∀ u0, (Fm u0).PlaceHyp (PhiSet (H := H)).card (bTx G.x G.ε)) ∧
  SizesPl G C cT TT Fm ∧
  (∀ u0 u, 0 < (Fm u0).du u) ∧ G.eBar ≤ 1 / 4 ∧
  DivIn G C TT T2 a Fm Rw logOm C0 g₁ g₂ ∧
  Count5 (mkData G C.cHH D ell N TT T2 a w Fm) C ∧
  (mkData G C.cHH D ell N TT T2 a w Fm).Slopes C ∧
  (∀ u0, (Fm u0).del ≤ G.delBar ∧ 5 * sgX G C.cHH + 3 * Real.sqrt (Fm u0).deF ≤ G.etaBar ∧
    2 * (Fm u0).e0 ≤ G.eBar) ∧
  ErrWindows (mkData G C.cHH D ell N TT T2 a w Fm) C (XppH H G) eK K ∧
  GrowthInequalitySizes TT T2 a w N G.x (bTx G.x G.ε) (bpTx G.x G.ε) η (XpTx G.x G.ε) θ ∧
  CostWindows G.x (fPl H) (bTx G.x G.ε) η θ ∧
  RestSize G.ε G.x (Fintype.card H) TT.card T2.card m (bTx G.x G.ε) G.k (aTx G.x G.ε)
def Inputs6aToD : Prop :=
  ∀ (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (Rw : ∀ u0, Rows (Fm u0))
    (η θ eK K CL logOm C0 : ℝ) (g₁ g₂ : ℕ), G.lg = Real.log ((g₁ : ℝ) * (g₂ : ℝ)) →
    Inputs6a D ell G C cT N TT T2 a w Fm Rw η θ eK K logOm C0 g₁ g₂ →
    ThinScales D ell (XpTx G.x G.ε) θ → ValuesAtX D ell G.x G.ε CL →
    InputsD D ell G C cT N TT T2 a w Fm η θ eK K CL logOm
end Defs
def Chain6aCore (A c' Cord eD eL K cHH eK CL eW KW ε x : ℝ) : Prop :=
  ∃ (e q d : ℕ) (_ : Fact q.Prime) (_ : Fact d.Prime) (Ω : Type) (_ : Fintype Ω)
    (W : Ω → HA e → Type) (_ : ∀ o u0, Fintype (W o u0)) (_ : ∀ o u0, Nonempty (W o u0)) (m : ℕ)
    (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset (HA e)) (a : Ω → HA e → ℝ) (w : Ω → HA e → Fin m → E0 × HA e → ℝ)
    (Fm : ∀ o u0, Fam (W o u0) m) (Rw : ∀ o u0, Rows (Fm o u0)) (Lp : HA e → Ω → LossP (HA e) m)
    (P : PrimeWindowSizeBounds.Par) (π : Ω → ℝ) (s sB : Finset ℕ) (BAD : ℕ → HA e → Prop) (Sig : ℕ → Ω → ℝ) (η : ℝ)
    (g₁ g₂ : ℕ) (logOm C0 : ℝ),
    G.x = x ∧ G.ε = ε ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧ P.e₂ = e ∧
    ((2 ^ e : ℕ) : ℝ) ≤ x ^ A ∧ PrimePairBounds ε CL x q d ∧
    G.v = hostV e q d ∧ g₁.Prime ∧ g₂.Prime ∧ G.lg = Real.log ((g₁ : ℝ) * (g₂ : ℝ)) ∧
    PerHost e q d logOm ∧
    LossHyp (hostData e q d) G C N TT a w Fm Lp P π s sB BAD Sig Cord eW KW ∧
    ∀ o, 0 < π o →
      Inputs6a (hostData e q d) (hostEll e q d) G C cT N TT T2 (a o) (w o) (Fm o) (Rw o) η
        (Real.exp (-c' * x ^ (ε / 8))) eK K logOm C0 g₁ g₂
def Core6aToCore2d : Prop :=
  ∀ c' : ℝ, HostAn c' → ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ x₁ : ℝ, ∀ Cord eD eL K cHH eK CL eW KW x : ℝ, x₁ ≤ x →
    Chain6aCore A c' Cord eD eL K cHH eK CL eW KW ε x → Chain2dCore Cord eD eL K cHH eK CL eW KW ε x
def Chain6a : Prop :=
  NoRealZeroSmall → LogNE → ∃ Cord c' : ℝ, 0 ≤ Cord ∧ 0 < c' ∧ ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ A K cHH eK CL eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x → Chain6aCore A c' Cord eD eL K cHH eK CL eW KW ε x) →
    RiemannHypothesis
def withGam {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ} (D : Data U0 W Top m f) (Gam : ℝ) :
    Data U0 W Top m f := { D with logGam := Real.log Gam }
structure SizeCountLevelObjects (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (W : H → Type) (m : ℕ) (TT : Finset H) where

  X : ∀ u0, W u0 → ℝ

  dst : ∀ u0, W u0 → ℝ

  bN : H → Fin m → Fin (PhiSet (H := H)).card → ℝ

  Gam : ℝ

  Sc : ℝ

  LZ : ℝ

  aM : ℝ

  Wt : TT → ℝ

  bt : TT → ℝ

  VV : ∀ u0, W u0 → Finset TT
namespace Fam6
variable {I : Type} {m : ℕ} (F : Fam I m)
def PlaceIn (f : ℕ) (bb : ℝ) (g₁ g₂ : ℕ) (Xpp : ℝ) : Prop :=
  (∀ w ∈ F.S, 0 ≤ F.τ w) ∧ (∀ w, w ∉ F.S → F.τ w = 0) ∧ (∀ w ∈ F.S, 0 ≤ F.iop (prBelow w)) ∧
  (∀ w ∈ F.S, ∀ w' : slopeLatticeData.FinPl F.K, prBelow w' = prBelow w → w' ∈ F.S) ∧
  F.Ta ≤ bb ^ 2 ∧
  ∀ u : I,
    (F.M u).FG ∧ Submodule.span F.K (F.M u : Set (F.V u)) = ⊤ ∧
    (F.Mf u).FG ∧ Submodule.span F.K (F.Mf u : Set (F.Vf u)) = ⊤ ∧ F.N0 u ≤ F.ItM u ∧
    rkK (F.N0 u) = rkK (F.M u) ∧
    (∀ w, w ∉ F.S → F.σ u w = 0 ∧ F.lenN u w = 0) ∧
    F.T u ∈ F.Pr ∧ (∀ w ∈ F.ST u, F.τ w = 0) ∧
    F.du u = F.dM u * (1 - 1 / ((F.T u : ℝ) - 1)) ^ f ∧
    (∀ w ∈ F.S \ F.ST u, F.lenR u w ≤ F.dM u * (F.tauR w + F.iop (prBelow w))) ∧
    (∀ w ∈ F.ST u, F.lenR u w ≤ F.dM u * F.lam u) ∧ 0 ≤ F.lam u ∧
    (∀ w ∈ F.S, F.σ u w = ⌊ramE w * F.sgw u w⌋) ∧
    (∀ w ∈ F.S, Xpp < (prBelow w : ℝ) → prBelow w ≠ g₁ → prBelow w ≠ g₂ → prBelow w ≠ F.T u → F.sgw u w = 0) ∧
    muDef (F.b u) (F.X u) (F.M u) = muDef (F.bf u) (F.Xf u) (F.Mf u)
      - (f : ℝ) * Real.log ((F.T u : ℝ) - 1) / ((F.T u : ℝ) - 2)
end Fam6
def RoundOfFloor : Prop :=
  ∀ (I : Type) (m : ℕ) (F : Fam I m) (u : I) (g₁ g₂ : ℕ) (Xpp : ℝ), 0 ≤ Xpp →
    (∀ w ∈ F.S, ∀ w' : slopeLatticeData.FinPl F.K, prBelow w' = prBelow w → w' ∈ F.S) →
    (∀ w ∈ F.S, F.σ u w = ⌊ramE w * F.sgw u w⌋) →
    (∀ w ∈ F.S, Xpp < (prBelow w : ℝ) → prBelow w ≠ g₁ → prBelow w ≠ g₂ → prBelow w ≠ F.T u → F.sgw u w = 0) →
    Real.log g₁ ≤ Xpp → Real.log g₂ ≤ Xpp → Real.log (F.T u) ≤ Xpp →
    (∀ w ∈ F.S, F.sgR u w ≤ F.sgw u w) ∧ F.Rd u ≤ (2 * Real.log 4 + 6) * Xpp
section DefsB
variable {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}
def Step4In (D : Data U0 W Top m f) (C : Consts) (cZ cL c5 Sc LZ : ℝ) : Prop :=
  PropZ D cZ Sc LZ ∧ ZWindows D cZ cL (c5 + 1) Sc LZ ∧ cSlopeZ cZ cL (c5 + 1) ≤ C.cSlope
def Step5In (D : Data U0 W Top m f) (C : Consts) (cE5 c5 Gam : ℝ) (X : ∀ u0, W u0 → ℝ)
    (bN : U0 → Fin m → Fin f → ℝ) : Prop :=
  ExactCoeff5 D cE5 X bN ∧ (∀ u0 (u : W u0), Real.log (X u0 u) ≤ c5 * (m : ℝ) * D.L) ∧ Variation5 D c5 X ∧
  SectionsFourToSixTransfer.LevelWindow D Gam X ∧ ExactWindows D bN ∧ CountWindows (withGam D Gam) c5 Gam ∧ cE5 + 6 ≤ c5 ∧ c5 + 3 ≤ C.cCount
def LevelWin (D : Data U0 W Top m f) (c5 : ℝ) : Prop :=
  6 ≤ m ∧ 8 * (f : ℝ) ≤ D.b ∧ (∀ u0 j ρ, 1 ≤ D.w u0 j ρ * D.v / Real.pi) ∧ 16 * D.L ≤ D.lg ∧ (m : ℝ) ^ 2 ≤ D.k ∧
  2 * c5 + 2 ≤ 15 * (m : ℝ)
def SlopesFromSizeAndCount : Prop :=
  ∀ (D : Data U0 W Top m f) (C : Consts) (cZ cL cE5 c5 Sc LZ Gam : ℝ) (X : ∀ u0, W u0 → ℝ)
    (bN : U0 → Fin m → Fin f → ℝ), Step4In D C cZ cL c5 Sc LZ → Step5In D C cE5 c5 Gam X bN →
    D.Slopes C ∧ Count5 D C ∧ LogTUp D (c5 + 1)
def LevelOfCount : Prop :=
  ∀ (D : Data U0 W Top m f) (C : Consts) (cE5 c5 Gam : ℝ) (X : ∀ u0, W u0 → ℝ) (bN : U0 → Fin m → Fin f → ℝ),
    Step5In D C cE5 c5 Gam X bN → LevelWin D c5 → D.L = Real.log D.b → 1 ≤ D.b →
    ∀ u0 (u : W u0), 4 * (f : ℝ) ≤ D.T u0 u ∧
      4 * (f : ℝ) / D.T u0 u * D.b ^ 2 + (f : ℝ) * Real.log (D.T u0 u - 1) / (D.T u0 u - 2) ≤ 1 ∧
      (m : ℝ) * D.L / 2 ≤ Real.log (D.T u0 u)
end DefsB
section DefsB2
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}
def Inputs6b (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (Rw : ∀ u0, Rows (Fm u0))
    (O : SizeCountLevelObjects H W m TT) (η θ eK K logOm C0 cZ cL cE5 c5 : ℝ) (g₁ g₂ : ℕ) : Prop :=
  (∀ u0, (Fm u0).LatHyp (sgX G C.cHH)) ∧
  (∀ u0, Fam6.PlaceIn (Fm u0) (PhiSet (H := H)).card (bTx G.x G.ε) g₁ g₂ (XppH H G)) ∧
  (∀ u0 u, muMaxDef ((Fm u0).b u) ((Fm u0).X u) ((Fm u0).M u) ≤ muMaxDef ((Fm u0).bf u) ((Fm u0).Xf u) ((Fm u0).Mf u)) ∧
  28 ≤ C.cSl1 ∧
  (∀ u0 u, 0 < (Fm u0).du u) ∧ G.eBar ≤ 1 / 4 ∧
  DivIn G C TT T2 a Fm Rw logOm C0 g₁ g₂ ∧
  Step4In (mkData G C.cHH D ell N TT T2 a w Fm) C cZ cL c5 O.Sc O.LZ ∧
  Step5In (mkData G C.cHH D ell N TT T2 a w Fm) C cE5 c5 O.Gam O.X O.bN ∧
  (IndexWindows (mkData G C.cHH D ell N TT T2 a w Fm) O.aM O.Wt O.bt ∧
    ∀ u0 u, (Fm u0).lam u ≤ lambdaIndex (mkData G C.cHH D ell N TT T2 a w Fm) O.aM (O.VV u0 u) O.Wt O.bt) ∧
  LevelWin (mkData G C.cHH D ell N TT T2 a w Fm) c5 ∧
  (Real.log g₁ ≤ XppH H G ∧ Real.log g₂ ≤ XppH H G ∧ (c5 + 1) * (m : ℝ) * Real.log (bTx G.x G.ε) ≤ XppH H G) ∧
  (∀ u0, (Fm u0).del ≤ G.delBar ∧ 5 * sgX G C.cHH + 3 * Real.sqrt (Fm u0).deF ≤ G.etaBar ∧
    2 * (Fm u0).e0 ≤ G.eBar) ∧
  ErrWindows (mkData G C.cHH D ell N TT T2 a w Fm) C (XppH H G) eK K ∧
  GrowthInequalitySizes TT T2 a w N G.x (bTx G.x G.ε) (bpTx G.x G.ε) η (XpTx G.x G.ε) θ ∧
  CostWindows G.x (fPl H) (bTx G.x G.ε) η θ ∧
  RestSize G.ε G.x (Fintype.card H) TT.card T2.card m (bTx G.x G.ε) G.k (aTx G.x G.ε)
def Inputs6bTo6a : Prop :=
  ∀ (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (Rw : ∀ u0, Rows (Fm u0))
    (O : SizeCountLevelObjects H W m TT) (η θ eK K logOm C0 cZ cL cE5 c5 : ℝ) (g₁ g₂ : ℕ),
    Inputs6b D ell G C N TT T2 a w Fm Rw O η θ eK K logOm C0 cZ cL cE5 c5 g₁ g₂ →
    Inputs6a D ell G C 7 N TT T2 a w Fm Rw η θ eK K logOm C0 g₁ g₂
end DefsB2
def Chain6bCore (A c' Cord eD eL K cHH eK CL eW KW ε x : ℝ) : Prop :=
  ∃ (e q d : ℕ) (_ : Fact q.Prime) (_ : Fact d.Prime) (Ω : Type) (_ : Fintype Ω)
    (W : Ω → HA e → Type) (_ : ∀ o u0, Fintype (W o u0)) (_ : ∀ o u0, Nonempty (W o u0)) (m : ℕ)
    (G : Glob) (C : Consts) (N : ℕ)
    (TT T2 : Finset (HA e)) (a : Ω → HA e → ℝ) (w : Ω → HA e → Fin m → E0 × HA e → ℝ)
    (Fm : ∀ o u0, Fam (W o u0) m) (Rw : ∀ o u0, Rows (Fm o u0)) (O : ∀ o, SizeCountLevelObjects (HA e) (W o) m TT)
    (Lp : HA e → Ω → LossP (HA e) m)
    (P : PrimeWindowSizeBounds.Par) (π : Ω → ℝ) (s sB : Finset ℕ) (BAD : ℕ → HA e → Prop) (Sig : ℕ → Ω → ℝ) (η : ℝ)
    (g₁ g₂ : ℕ) (logOm C0 cZ cL cE5 c5 : ℝ),
    G.x = x ∧ G.ε = ε ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧ P.e₂ = e ∧
    ((2 ^ e : ℕ) : ℝ) ≤ x ^ A ∧ PrimePairBounds ε CL x q d ∧
    G.v = hostV e q d ∧ g₁.Prime ∧ g₂.Prime ∧ G.lg = Real.log ((g₁ : ℝ) * (g₂ : ℝ)) ∧
    PerHost e q d logOm ∧
    LossHyp (hostData e q d) G C N TT a w Fm Lp P π s sB BAD Sig Cord eW KW ∧
    ∀ o, 0 < π o →
      Inputs6b (hostData e q d) (hostEll e q d) G C N TT T2 (a o) (w o) (Fm o) (Rw o) (O o) η
        (Real.exp (-c' * x ^ (ε / 8))) eK K logOm C0 cZ cL cE5 c5 g₁ g₂
def Core6bToCore6a : Prop :=
  ∀ A c' Cord eD eL K cHH eK CL eW KW ε x : ℝ, Chain6bCore A c' Cord eD eL K cHH eK CL eW KW ε x →
    Chain6aCore A c' Cord eD eL K cHH eK CL eW KW ε x
def Chain6b : Prop :=
  NoRealZeroSmall → LogNE → ∃ Cord c' : ℝ, 0 ≤ Cord ∧ 0 < c' ∧ ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ A K cHH eK CL eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x → Chain6bCore A c' Cord eD eL K cHH eK CL eW KW ε x) →
    RiemannHypothesis
structure FamC (I : Type) (m : ℕ) where

  K : Type
  [indexKFirst : Field K]
  [indexKSecond : NumberField K]
  [indexKThird : StarRing K]
  [indexKFourth : IsTotallyComplex K]

  Wd : Type
  [indexWFirst : AddCommGroup Wd]
  [indexWSecond : Module K Wd]
  [indexWThird : Module (𝓞 K) Wd]
  [indexWFourth : IsScalarTower (𝓞 K) K Wd]

  Dall : ℕ

  D : ℕ

  D1 : ℕ

  V : I → Type
  [indexVFirst : ∀ i, AddCommGroup (V i)]
  [indexVSecond : ∀ i, Module K (V i)]
  [indexVThird : ∀ i, Module (𝓞 K) (V i)]
  [indexVFourth : ∀ i, IsScalarTower (𝓞 K) K (V i)]

  r : I → ℕ

  Vf : I → Type
  [indexFFirst : ∀ i, AddCommGroup (Vf i)]
  [indexFSecond : ∀ i, Module K (Vf i)]
  [indexFThird : ∀ i, Module (𝓞 K) (Vf i)]
  [indexFFourth : ∀ i, IsScalarTower (𝓞 K) K (Vf i)]

  d : I → ℕ
  b' : Basis (Fin D) K Wd
  X' : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ

  cc : Submodule (𝓞 K) Wd
  b : ∀ i, Basis (Fin (r i)) K (V i)
  X : ∀ i, InfinitePlace K → Matrix (Fin (r i)) (Fin (r i)) ℂ

  M : ∀ i, Submodule (𝓞 K) (V i)

  N0 : ∀ i, Submodule (𝓞 K) (V i)
  bf : ∀ i, Basis (Fin (d i)) K (Vf i)
  Xf : ∀ i, InfinitePlace K → Matrix (Fin (d i)) (Fin (d i)) ℂ

  Mf : ∀ i, Submodule (𝓞 K) (Vf i)

  j : ∀ i, V i →ₗ[K] Vf i

  σ : I → slopeLatticeData.FinPl K →₀ ℤ

  τ : slopeLatticeData.FinPl K →₀ ℤ

  B : ∀ i, V i →ₗ[K] Wd

  v : InfinitePlace K

  Y : ∀ i, Matrix (Fin (r i)) (Fin (r i)) ℂ

  Y' : Matrix (Fin D) (Fin D) ℂ

  Pf : ∀ u, Matrix (Fin Dall) (Fin (d u)) ℂ

  Vr : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ

  ga : I → ℝ

  c : I → ℂ

  Vrow : Matrix (Fin Dall) (Fin Dall) ℂ

  U : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ

  J : Matrix (Fin Dall) (Fin D) ℂ

  J1 : Matrix (Fin Dall) (Fin D1) ℂ

  S : Finset (slopeLatticeData.FinPl K)
  gain : Fin m → slopeLatticeData.FinPl K → ℝ
  Fj : Fin m → slopeLatticeData.FinPl K → ℝ
  Ej : I → Fin m → slopeLatticeData.FinPl K → ℝ

  iop : ℕ → ℝ

  T : I → ℕ

  h : I → ℝ

  lam : I → ℝ
  Dstar : ℝ
  η0 : ℝ
  η1 : ℝ
  e0 : ℝ
attribute [instance] FamC.indexKFirst FamC.indexKSecond FamC.indexKThird FamC.indexKFourth FamC.indexWFirst FamC.indexWSecond FamC.indexWThird FamC.indexWFourth
  FamC.indexVFirst FamC.indexVSecond FamC.indexVThird FamC.indexVFourth FamC.indexFFirst FamC.indexFSecond FamC.indexFThird FamC.indexFFourth
namespace FamC
variable {I : Type} {m : ℕ} (F : FamC I m)
abbrev toFam : Fam I m where
  K := F.K
  Wd := F.Wd
  κ := Fin F.D
  κ₁ := Fin F.D1
  V := F.V
  ι := fun i => Fin (F.r i)
  Vf := F.Vf
  ιf := fun i => Fin (F.d i)
  b' := F.b'
  X' := F.X'
  cc := F.cc
  b := F.b
  X := F.X
  M := F.M
  N0 := F.N0
  bf := F.bf
  Xf := F.Xf
  Mf := F.Mf
  σ := F.σ
  τ := F.τ
  B := F.B
  v := F.v
  Y := F.Y
  Y' := F.Y'
  Ball := fun u => HilbertSchmidtUnitaryInvariance.BfS F.Pf F.c F.Vrow F.J F.J1 u * HilbertSchmidtUnitaryInvariance.VrS F.Vr F.U u
  γ := HilbertSchmidtUnitaryInvariance.gaTw F.ga F.c
  Bf := HilbertSchmidtUnitaryInvariance.BfS F.Pf F.c F.Vrow F.J F.J1
  Vr := HilbertSchmidtUnitaryInvariance.VrS F.Vr F.U
  S := F.S
  gain := F.gain
  Fj := F.Fj
  Ej := F.Ej
  iop := F.iop
  T := F.T
  h := F.h
  lam := F.lam
  Dstar := F.Dstar
  η0 := F.η0
  η1 := F.η1
  e0 := F.e0
def LatIn [Fintype I] (Rw : Rows F.toFam) (sg Gam C0S delB : ℝ) : Prop :=
  (∀ w, IsUnit (F.X' w).det) ∧ (∀ i w, IsUnit (F.X i w).det) ∧
  F.cc.FG ∧ Submodule.span F.K (F.cc : Set F.Wd) = ⊤ ∧
  (∀ i, (F.toFam.N' i).FG) ∧ (∀ i, Submodule.span F.K (F.toFam.N' i : Set (F.V i)) = ⊤) ∧
  (∀ i, ∀ φ ∈ F.toFam.N' i, ∃ β : Module.Dual F.K (Fin Rw.D → F.K), Rw.ψ β = F.B i φ ∧
    ∀ x ∈ Rw.R, β x ∈ Set.range (algebraMap (𝓞 F.K) F.K)) ∧
  (∀ i, F.B i ≠ 0 → htMap (F.b i) (F.X i) F.b' F.X' (F.B i) ≤ F.h i) ∧
  ∃ de del : ℝ, del ≤ delB ∧
    HilbertSchmidtUnitaryInvariance.ChainHyp F.Pf F.Vr F.ga F.c F.Vrow F.U F.J F.J1
      (fun i => (LinearMap.toMatrix (F.b i) F.b' (F.B i)).map F.v.embedding) F.Y' F.Y
      F.Dstar sg F.η0 F.η1 F.e0 de del C0S Gam
def SubIn : Prop :=
  ∀ u : I, (∀ w, IsUnit (F.Xf u w).det) ∧ Function.Injective (F.j u) ∧
    htMap (F.b u) (F.X u) (F.bf u) (F.Xf u) (F.j u) ≤ 0 ∧
    (F.M u).map ((F.j u).restrictScalars (𝓞 F.K)) = DiagonalSublatticeLength.latV (F.Mf u) (LinearMap.range (F.j u))
end FamC
def LatOfChain : Prop :=
  ∀ (I : Type) [Fintype I] (m : ℕ) (F : FamC I m) (Rw : Rows F.toFam) (sg Gam C0S delB : ℝ),
    RowsAreDual F.toFam Rw.XE Rw.R Rw.ψ → F.LatIn Rw sg Gam C0S delB →
    F.toFam.LatHyp sg ∧ F.toFam.del ≤ delB ∧ Fintype.card I = ⌈C0S * Gam ^ 2 / sg⌉₊
def MuMaxOfSub : Prop :=
  ∀ (I : Type) (m : ℕ) (F : FamC I m), F.SubIn → ∀ u : I, (∀ w, IsUnit (F.X u w).det) → (F.M u).FG → (F.Mf u).FG →
    F.M u ≠ ⊥ → muMaxDef (F.b u) (F.X u) (F.M u) ≤ muMaxDef (F.bf u) (F.Xf u) (F.Mf u)
section DefsC
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}
def Inputs6c (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fc : ∀ u0, FamC (W u0) m)
    (Rw : ∀ u0, Rows (Fc u0).toFam) (O : SizeCountLevelObjects H W m TT) (η θ eK K logOm C0 cZ cL cE5 c5 C0S : ℝ) (g₁ g₂ : ℕ) : Prop :=
  (∀ u0, (Fc u0).LatIn (Rw u0) (sgX G C.cHH) O.Gam C0S G.delBar) ∧
  (∀ u0, Fam6.PlaceIn (Fc u0).toFam (PhiSet (H := H)).card (bTx G.x G.ε) g₁ g₂ (XppH H G)) ∧
  (∀ u0, (Fc u0).SubIn) ∧
  28 ≤ C.cSl1 ∧
  (∀ u0 u, 0 < (Fc u0).r u) ∧ G.eBar ≤ 1 / 4 ∧
  DivIn G C TT T2 a (fun u0 => (Fc u0).toFam) Rw logOm C0 g₁ g₂ ∧
  Step4In (mkData G C.cHH D ell N TT T2 a w (fun u0 => (Fc u0).toFam)) C cZ cL c5 O.Sc O.LZ ∧
  Step5In (mkData G C.cHH D ell N TT T2 a w (fun u0 => (Fc u0).toFam)) C cE5 c5 O.Gam O.X O.bN ∧
  (IndexWindows (mkData G C.cHH D ell N TT T2 a w (fun u0 => (Fc u0).toFam)) O.aM O.Wt O.bt ∧
    ∀ u0 u, (Fc u0).lam u
      ≤ lambdaIndex (mkData G C.cHH D ell N TT T2 a w (fun u0 => (Fc u0).toFam)) O.aM (O.VV u0 u) O.Wt O.bt) ∧
  LevelWin (mkData G C.cHH D ell N TT T2 a w (fun u0 => (Fc u0).toFam)) c5 ∧
  (Real.log g₁ ≤ XppH H G ∧ Real.log g₂ ≤ XppH H G ∧ (c5 + 1) * (m : ℝ) * Real.log (bTx G.x G.ε) ≤ XppH H G) ∧
  (∀ u0, 5 * sgX G C.cHH + 3 * Real.sqrt (Fc u0).toFam.deF ≤ G.etaBar ∧ 2 * (Fc u0).e0 ≤ G.eBar) ∧
  ErrWindows (mkData G C.cHH D ell N TT T2 a w (fun u0 => (Fc u0).toFam)) C (XppH H G) eK K ∧
  GrowthInequalitySizes TT T2 a w N G.x (bTx G.x G.ε) (bpTx G.x G.ε) η (XpTx G.x G.ε) θ ∧
  CostWindows G.x (fPl H) (bTx G.x G.ε) η θ ∧
  RestSize G.ε G.x (Fintype.card H) TT.card T2.card m (bTx G.x G.ε) G.k (aTx G.x G.ε)
def Inputs6cTo6b : Prop :=
  ∀ (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fc : ∀ u0, FamC (W u0) m)
    (Rw : ∀ u0, Rows (Fc u0).toFam) (O : SizeCountLevelObjects H W m TT) (η θ eK K logOm C0 cZ cL cE5 c5 C0S : ℝ) (g₁ g₂ : ℕ),
    Inputs6c D ell G C N TT T2 a w Fc Rw O η θ eK K logOm C0 cZ cL cE5 c5 C0S g₁ g₂ →
    Inputs6b D ell G C N TT T2 a w (fun u0 => (Fc u0).toFam) Rw O η θ eK K logOm C0 cZ cL cE5 c5 g₁ g₂
end DefsC
def Chain6cCore (A c' Cord eD eL K cHH eK CL eW KW ε x : ℝ) : Prop :=
  ∃ (e q d : ℕ) (_ : Fact q.Prime) (_ : Fact d.Prime) (Ω : Type) (_ : Fintype Ω)
    (W : Ω → HA e → Type) (_ : ∀ o u0, Fintype (W o u0)) (_ : ∀ o u0, Nonempty (W o u0)) (m : ℕ)
    (G : Glob) (C : Consts) (N : ℕ)
    (TT T2 : Finset (HA e)) (a : Ω → HA e → ℝ) (w : Ω → HA e → Fin m → E0 × HA e → ℝ)
    (Fc : ∀ o u0, FamC (W o u0) m) (Rw : ∀ o u0, Rows (Fc o u0).toFam) (O : ∀ o, SizeCountLevelObjects (HA e) (W o) m TT)
    (Lp : HA e → Ω → LossP (HA e) m)
    (P : PrimeWindowSizeBounds.Par) (π : Ω → ℝ) (s sB : Finset ℕ) (BAD : ℕ → HA e → Prop) (Sig : ℕ → Ω → ℝ) (η : ℝ)
    (g₁ g₂ : ℕ) (logOm C0 cZ cL cE5 c5 C0S : ℝ),
    G.x = x ∧ G.ε = ε ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧ P.e₂ = e ∧
    ((2 ^ e : ℕ) : ℝ) ≤ x ^ A ∧ PrimePairBounds ε CL x q d ∧
    G.v = hostV e q d ∧ g₁.Prime ∧ g₂.Prime ∧ G.lg = Real.log ((g₁ : ℝ) * (g₂ : ℝ)) ∧
    PerHost e q d logOm ∧
    LossHyp (hostData e q d) G C N TT a w (fun o u0 => (Fc o u0).toFam) Lp P π s sB BAD Sig Cord eW KW ∧
    ∀ o, 0 < π o →
      Inputs6c (hostData e q d) (hostEll e q d) G C N TT T2 (a o) (w o) (Fc o) (Rw o) (O o) η
        (Real.exp (-c' * x ^ (ε / 8))) eK K logOm C0 cZ cL cE5 c5 C0S g₁ g₂
def Core6cToCore6b : Prop :=
  ∀ A c' Cord eD eL K cHH eK CL eW KW ε x : ℝ, Chain6cCore A c' Cord eD eL K cHH eK CL eW KW ε x →
    Chain6bCore A c' Cord eD eL K cHH eK CL eW KW ε x
def Chain6c : Prop :=
  NoRealZeroSmall → LogNE → ∃ Cord c' : ℝ, 0 ≤ Cord ∧ 0 < c' ∧ ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ A K cHH eK CL eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x → Chain6cCore A c' Cord eD eL K cHH eK CL eW KW ε x) →
    RiemannHypothesis
def E8 (x ε : ℝ) : ℝ := Real.exp (-(x ^ (ε / 8)))
def E7 (x ε : ℝ) : ℝ := Real.exp (-(x ^ (ε / 7)))
def glob6 (x ε k v : ℝ) (g₁ g₂ : ℕ) (cHH : ℝ) : Glob where
  x := x
  ε := ε
  k := k
  La := Real.log (aTx x ε * (2 * v))
  v := v
  lg := Real.log ((g₁ : ℝ) * (g₂ : ℝ))
  delBar := E7 x ε
  etaBar := 6 * x ^ (-cHH)
  eBar := 2 * E8 x ε ^ 2
namespace FamC
variable {I : Type} {m : ℕ} (F : FamC I m)
def TraceIn [Fintype I] (Rw : Rows F.toFam) (x ε sg Gam C0S : ℝ) : Prop :=
  ((∀ w, IsUnit (F.X' w).det) ∧ (∀ i w, IsUnit (F.X i w).det) ∧
    F.cc.FG ∧ Submodule.span F.K (F.cc : Set F.Wd) = ⊤ ∧
    (∀ i, (F.toFam.N' i).FG) ∧ (∀ i, Submodule.span F.K (F.toFam.N' i : Set (F.V i)) = ⊤)) ∧
  (∀ i, ∀ φ ∈ F.toFam.N' i, ∃ β : Module.Dual F.K (Fin Rw.D → F.K), Rw.ψ β = F.B i φ ∧
    ∀ x ∈ Rw.R, β x ∈ Set.range (algebraMap (𝓞 F.K) F.K)) ∧
  (∀ i, F.B i ≠ 0 → htMap (F.b i) (F.X i) F.b' F.X' (F.B i) ≤ F.h i) ∧
  ((∀ u, 0 < F.ga u) ∧ 0 < F.Dstar ∧ HilbertSchmidtNormSquare.InputS F.Pf F.ga F.Dstar F.η0 F.η1 F.e0 ∧
    -1 ≤ F.η0 ∧ F.η0 ≤ E8 x ε ∧ F.η1 ≤ E8 x ε ∧ 0 ≤ F.e0 ∧ Real.sqrt F.e0 ≤ E8 x ε) ∧
  (0 < C0S ∧ 0 < Gam ∧ Fintype.card I = ⌈C0S * Gam ^ 2 / sg⌉₊) ∧
  HilbertSchmidtNormSquare.Isom F.Vr ∧
  ((∀ u, F.c u ≠ 0) ∧ HilbertSchmidtUnitaryInvariance.IsUni F.Vrow ∧ (∀ u, HilbertSchmidtUnitaryInvariance.IsUni (F.U u)) ∧ IsUnit F.Y'.det ∧ (∀ u, IsUnit (F.Y u).det) ∧
    ∀ u, F.Y'⁻¹ * (LinearMap.toMatrix (F.b u) F.b' (F.B u)).map F.v.embedding * F.Y u
      = F.c u • (F.Jᴴ * (F.Vrow * HilbertSchmidtNormSquare.Bram F.Pf F.Vr u * F.U u))) ∧
  (HilbertSchmidtUnitaryInvariance.OrthFrame F.J F.J1 ∧ (1 - E7 x ε) * (F.Dall : ℝ) ≤ (F.D : ℝ))
end FamC
section DefsD
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}
def Sizes6 (x ε eK K k : ℝ) (m N : ℕ) (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (η κ off : ℝ) (btH : H → ℝ) (sg Gam C0S : ℝ) (g₁ g₂ : ℕ) : Prop :=
  (x ^ ((1 : ℝ) / 2 - ε) ≤ (m : ℝ) ∧ (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2) ∧ x * (m : ℝ) ≤ k ∧ 0 ≤ eK ∧ k ≤ x ^ eK ∧
    k ≤ (Fintype.card H : ℝ) ^ 2 * x ^ ((1 : ℝ) / 2 - ε)) ∧
  (x ^ (-(ε / 8)) * (Fintype.card H : ℝ) / 2 ≤ (TT.card : ℝ) ∧ x ^ (-ε) ≤ (T2.card : ℝ) / (Fintype.card H : ℝ)) ∧
  (∀ t ∈ TT, |a t / bTx x ε - x| ≤ 1) ∧
  (0 ≤ η ∧ η ≤ Real.exp (x ^ (ε / 4)) ∧ 0 ≤ κ ∧ κ ≤ 1 / 4 ∧
    (off = bpTx x ε / x ∨ off = (⌊bpTx x ε / x⌋ : ℝ)) ∧
    (∀ t ∈ TT, bpTx x ε ≤ btH t ∧ btH t ≤ bpTx x ε + κ * bpTx x ε) ∧
    LSmall.NodeWindows TT T2 (bTx x ε) η (bpTx x ε / (x * (Fintype.card H : ℝ))) off btH w) ∧
  (∀ u0 j t ρ, t ∈ TT → InPhi ρ → a t / w u0 j ρ ≤ N) ∧
  C0S * Gam ^ 2 / sg + 1 ≤ (2 : ℝ) ^ (k - 3) ∧
  (8 * x ^ ε ≤ Real.log g₁ ∧ Real.log g₁ ≤ K * x ^ ε ∧ 8 * x ^ ε ≤ Real.log g₂ ∧ Real.log g₂ ≤ K * x ^ ε)
def Inputs6d (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (x ε k v : ℝ) (C : Consts) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fc : ∀ u0, FamC (W u0) m)
    (Rw : ∀ u0, Rows (Fc u0).toFam) (O : SizeCountLevelObjects H W m TT) (η eK K logOm C0 cZ cL cE5 c5 C0S κ off : ℝ)
    (btH : H → ℝ) (g₁ g₂ : ℕ) : Prop :=
  (∀ u0, (Fc u0).TraceIn (Rw u0) x ε (x ^ (-C.cHH)) O.Gam C0S) ∧
  (∀ u0, Fam6.PlaceIn (Fc u0).toFam (PhiSet (H := H)).card (bTx x ε) g₁ g₂ (XppTx x ε (Fintype.card H : ℝ))) ∧
  (∀ u0, (Fc u0).SubIn) ∧
  (∀ u0 u, 0 < (Fc u0).r u) ∧
  DivIn (glob6 x ε k v g₁ g₂ C.cHH) C TT T2 a (fun u0 => (Fc u0).toFam) Rw logOm C0 g₁ g₂ ∧
  (PropZ (mkData (glob6 x ε k v g₁ g₂ C.cHH) C.cHH D ell N TT T2 a w (fun u0 => (Fc u0).toFam)) cZ O.Sc O.LZ ∧
    0 ≤ cZ ∧ 0 ≤ cL ∧ 0 ≤ O.Sc ∧ O.Sc ≤ Real.exp (x ^ (ε / 4)) ∧ O.LZ ≤ cL * Real.log (aTx x ε * (2 * v)) ∧
    cSlopeZ cZ cL (c5 + 1) ≤ C.cSlope) ∧
  (ExactCoeff5 (mkData (glob6 x ε k v g₁ g₂ C.cHH) C.cHH D ell N TT T2 a w (fun u0 => (Fc u0).toFam)) cE5 O.X O.bN ∧
    (∀ u0 (u : W u0), Real.log (O.X u0 u) ≤ c5 * (m : ℝ) * x ^ ε) ∧
    Variation5 (mkData (glob6 x ε k v g₁ g₂ C.cHH) C.cHH D ell N TT T2 a w (fun u0 => (Fc u0).toFam)) c5 O.X ∧
    SectionsFourToSixTransfer.LevelWindow (mkData (glob6 x ε k v g₁ g₂ C.cHH) C.cHH D ell N TT T2 a w (fun u0 => (Fc u0).toFam)) O.Gam O.X ∧
    1 ≤ O.Gam ∧ Real.log O.Gam / (((PhiSet (H := H)).card : ℝ) * k) ≤ 1 ∧ 0 ≤ c5 ∧ cE5 + 6 ≤ c5 ∧ c5 + 3 ≤ C.cCount ∧
    ∀ u0 j ρ, 0 < O.bN u0 j ρ ∧ w u0 j (ePhi ρ) ≤ O.bN u0 j ρ * (1 + 1 / x) ∧ Real.log (O.bN u0 j ρ) ≤ 2 * x ^ ε) ∧
  (2 ≤ C0S ∧ ∀ u0 (u : W u0), 0 < O.dst u0 u ∧
    O.X u0 u ^ (((PhiSet (H := H)).card : ℝ) * k) = (Fc u0).Dstar / O.dst u0 u ∧
    ((Fc u0).d u : ℝ) = O.dst u0 u * (((Fc u0).T u : ℝ) ^ k - 1) ^ (PhiSet (H := H)).card) ∧
  (O.aM ≤ 2 * aTx x ε ∧ (∀ t, O.Wt t ≤ 2 * bpTx x ε) ∧ (∀ t : TT, O.bt t = btH t) ∧
    ∀ u0 u, (Fc u0).lam u
      ≤ lambdaIndex (mkData (glob6 x ε k v g₁ g₂ C.cHH) C.cHH D ell N TT T2 a w (fun u0 => (Fc u0).toFam)) O.aM (O.VV u0 u)
          O.Wt O.bt) ∧
  Sizes6 x ε eK K k m N TT T2 a w η κ off btH (x ^ (-C.cHH)) O.Gam C0S g₁ g₂
end DefsD
def Inputs6dTo6c : Prop :=
  ∀ ε A c' K cHH eK : ℝ, 0 < ε → ε < 1 / 4 → 0 < A → 0 < c' → ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x →
  ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (W : H → Type) [∀ u0, Fintype (W u0)] (m : ℕ)
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (k v : ℝ) (C : Consts) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fc : ∀ u0, FamC (W u0) m)
    (Rw : ∀ u0, Rows (Fc u0).toFam) (O : SizeCountLevelObjects H W m TT) (η logOm C0 cZ cL cE5 c5 C0S κ off : ℝ)
    (btH : H → ℝ) (g₁ g₂ : ℕ),
    (Fintype.card H : ℝ) ≤ x ^ A → Real.pi ≤ v → Real.log (2 * v) ≤ x ^ (ε / 3) →
    ConstsBound C K → 28 ≤ C.cSl1 → 1 ≤ C.cHH → C.cHH ≤ cHH →
    Inputs6d D ell x ε k v C N TT T2 a w Fc Rw O η eK K logOm C0 cZ cL cE5 c5 C0S κ off btH g₁ g₂ →
    Inputs6c D ell (glob6 x ε k v g₁ g₂ C.cHH) C N TT T2 a w Fc Rw O η (Real.exp (-c' * x ^ (ε / 8))) eK K logOm C0 cZ cL
      cE5 c5 C0S g₁ g₂
def WordsOfCount : Prop :=
  ∀ (X Gam T k dst Dstar d C0S : ℝ) (f : ℕ), 0 < X → 1 ≤ Gam → 1 ≤ f → 1 ≤ k →
    X * Gam ^ (-(2 / ((f : ℝ) * k))) ≤ T → 4 * (f : ℝ) ≤ T → 0 < dst → 0 < Dstar →
    X ^ ((f : ℝ) * k) = Dstar / dst → d = dst * (T ^ k - 1) ^ f → 2 ≤ C0S → Dstar / Gam ^ 2 / C0S ≤ d
def HostVEv : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ e q d : ℕ, ((2 ^ e : ℕ) : ℝ) ≤ x ^ A →
    X1 ε x ^ (1 / 2 : ℝ) < (q : ℝ) → (q : ℝ) ≤ X1 ε x → X2 ε x ^ (1 / 2 : ℝ) < (d : ℝ) → (d : ℝ) ≤ X2 ε x →
    Real.pi ≤ hostV e q d ∧ Real.log (2 * hostV e q d) ≤ x ^ (ε / 3)
def Chain6Core (A Cord eD eL K cHH eK CL eW KW ε x : ℝ) : Prop :=
  ∃ (e q d : ℕ) (_ : Fact q.Prime) (_ : Fact d.Prime) (Ω : Type) (_ : Fintype Ω)
    (W : Ω → HA e → Type) (_ : ∀ o u0, Fintype (W o u0)) (_ : ∀ o u0, Nonempty (W o u0)) (m : ℕ)
    (k : ℝ) (C : Consts) (N : ℕ)
    (TT T2 : Finset (HA e)) (a btH : Ω → HA e → ℝ) (w : Ω → HA e → Fin m → E0 × HA e → ℝ)
    (Fc : ∀ o u0, FamC (W o u0) m) (Rw : ∀ o u0, Rows (Fc o u0).toFam) (O : ∀ o, SizeCountLevelObjects (HA e) (W o) m TT)
    (Lp : HA e → Ω → LossP (HA e) m)
    (P : PrimeWindowSizeBounds.Par) (π : Ω → ℝ) (s sB : Finset ℕ) (BAD : ℕ → HA e → Prop) (Sig : ℕ → Ω → ℝ) (η κ off : ℝ)
    (g₁ g₂ : ℕ) (logOm C0 cZ cL cE5 c5 C0S : ℝ),
    C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ 1 ≤ C.cHH ∧ C.cHH ≤ cHH ∧ ConstsBound C K ∧ 28 ≤ C.cSl1 ∧
    P.e₂ = e ∧ P.η = η ∧ (∀ o, (O o).Sc = P.Sc) ∧
    ((2 ^ e : ℕ) : ℝ) ≤ x ^ A ∧ PrimePairBounds ε CL x q d ∧
    g₁.Prime ∧ g₂.Prime ∧
    PerHost e q d logOm ∧
    LossHyp (hostData e q d) (glob6 x ε k (hostV e q d) g₁ g₂ C.cHH) C N TT a w (fun o u0 => (Fc o u0).toFam) Lp P π s sB
      BAD Sig Cord eW KW ∧
    ∀ o, 0 < π o →
      Inputs6d (hostData e q d) (hostEll e q d) x ε k (hostV e q d) C N TT T2 (a o) (w o) (Fc o) (Rw o) (O o) η eK K logOm
        C0 cZ cL cE5 c5 C0S κ off (btH o) g₁ g₂
def Core6ToCore6c : Prop :=
  ∀ ε A c' K cHH eK : ℝ, 0 < ε → ε < 1 / 4 → 0 < A → 0 < c' → ∃ x₁ : ℝ, ∀ Cord eD eL CL eW KW x : ℝ, x₁ ≤ x →
    Chain6Core A Cord eD eL K cHH eK CL eW KW ε x → Chain6cCore A c' Cord eD eL K cHH eK CL eW KW ε x
def Chi8NoRealZero : Prop :=
  ∀ σ : ℝ, 0 < σ → σ < 1 → DirichletCharacter.LFunction chi8 (σ : ℂ) ≠ 0
def Chain6 : Prop :=
  Chi8NoRealZero → ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ A K cHH eK CL eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x → Chain6Core A Cord eD eL K cHH eK CL eW KW ε x) →
    RiemannHypothesis
def Chain6At : Prop :=
  Chi8NoRealZero → ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK CL eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → Chain6Core A Cord eD eL K cHH eK CL eW KW ε x →
      Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε)
def Chain6Closed : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ A K cHH eK CL eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x → Chain6Core A Cord eD eL K cHH eK CL eW KW ε x) →
    RiemannHypothesis
def Chain6AtClosed : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK CL eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → Chain6Core A Cord eD eL K cHH eK CL eW KW ε x →
      Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε)
def WordsUpOfCount : Prop :=
  ∀ (X Gam T k dst Dstar d C0S : ℝ) (f : ℕ), 0 < X → 1 ≤ Gam → 1 ≤ f → 1 ≤ k →
    T ≤ X * Gam ^ (-(2 / ((f : ℝ) * k))) * (1 + 1 / ((f : ℝ) * k)) → 4 * (f : ℝ) ≤ T → 0 < dst → 0 < Dstar →
    X ^ ((f : ℝ) * k) = Dstar / dst → d = dst * (T ^ k - 1) ^ f → 3 ≤ C0S → d ≤ C0S * (Dstar / Gam ^ 2)
namespace Fam6
variable {I : Type} {m : ℕ} (F : Fam I m)
def GainIn (Ps : Finset ℕ) (cl : ℕ → DeficitSplitLemmas.PClass) (T a : ℝ) : Prop :=
  ∀ w ∈ F.S, prBelow w ∈ Ps → cl (prBelow w) = DeficitSplitLemmas.PClass.served →
    ∀ j : Fin m, 0 ≤ F.gain j w ∧ F.gain j w ≤ 4 * T * a / (prBelow w : ℝ)
def PlaceIn' (f : ℕ) (g₁ g₂ : ℕ) (Xpp : ℝ) : Prop :=
  (∀ w ∈ F.S, 0 ≤ F.τ w) ∧ (∀ w, w ∉ F.S → F.τ w = 0) ∧ (∀ w ∈ F.S, 0 ≤ F.iop (prBelow w)) ∧
  (∀ w ∈ F.S, ∀ w' : slopeLatticeData.FinPl F.K, prBelow w' = prBelow w → w' ∈ F.S) ∧
  ∀ u : I,
    (F.M u).FG ∧ Submodule.span F.K (F.M u : Set (F.V u)) = ⊤ ∧
    (F.Mf u).FG ∧ Submodule.span F.K (F.Mf u : Set (F.Vf u)) = ⊤ ∧ F.N0 u ≤ F.ItM u ∧
    rkK (F.N0 u) = rkK (F.M u) ∧
    (∀ w, w ∉ F.S → F.σ u w = 0 ∧ F.lenN u w = 0) ∧
    F.T u ∈ F.Pr ∧ (∀ w ∈ F.ST u, F.τ w = 0) ∧
    F.du u = F.dM u * (1 - 1 / ((F.T u : ℝ) - 1)) ^ f ∧
    (∀ w ∈ F.S \ F.ST u, F.lenR u w ≤ F.dM u * (F.tauR w + F.iop (prBelow w))) ∧
    (∀ w ∈ F.ST u, F.lenR u w ≤ F.dM u * F.lam u) ∧ 0 ≤ F.lam u ∧
    (∀ w ∈ F.S, F.σ u w = ⌊ramE w * F.sgw u w⌋) ∧
    (∀ w ∈ F.S, Xpp < (prBelow w : ℝ) → prBelow w ≠ g₁ → prBelow w ≠ g₂ → prBelow w ≠ F.T u → F.sgw u w = 0) ∧
    muDef (F.b u) (F.X u) (F.M u) = muDef (F.bf u) (F.Xf u) (F.Mf u)
      - (f : ℝ) * Real.log ((F.T u : ℝ) - 1) / ((F.T u : ℝ) - 2)
end Fam6
def TaOfPrimeWindows : Prop :=
  ∀ (ι κ τ : Type) (P : PrimeWindowSizeBounds.Par) (e K : ℝ), PrimeWindowSizeBounds.Windows P e K → PrimeWindowSizeBounds.LargeX P.x P.ε e K →
    ∀ (Ps : Finset ℕ) (J : Finset κ) (TT : Finset τ) (D : PrimeWindowSizeBounds.LD ι κ τ), (∀ p ∈ Ps, p.Prime) → TT.Nonempty →
    PrimeWindowSizeBounds.ParametersHyp P Ps J TT D →
    (∀ p ∈ Ps, D.cl p = DeficitSplitLemmas.PClass.served → ∀ j ∈ J, D.gain j p ≤ 4 * (TT.card : ℝ) * P.a / p) →
    (J.card : ℝ) ≤ P.x → (TT.card : ℝ) ≤ P.n →
    2 * ∑ w ∈ D.W, D.l w * D.tauW w ≤ P.b ^ 2
section DefsD'
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}
def Inputs6d' (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (x ε k v : ℝ) (C : Consts) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fc : ∀ u0, FamC (W u0) m)
    (Rw : ∀ u0, Rows (Fc u0).toFam) (O : SizeCountLevelObjects H W m TT) (η eK K logOm C0 cZ cL cE5 c5 C0S κ off : ℝ)
    (btH : H → ℝ) (g₁ g₂ : ℕ) : Prop :=
  (∀ u0, (Fc u0).TraceIn (Rw u0) x ε (x ^ (-C.cHH)) O.Gam C0S) ∧
  (∀ u0, Fam6.PlaceIn' (Fc u0).toFam (PhiSet (H := H)).card g₁ g₂ (XppTx x ε (Fintype.card H : ℝ))) ∧
  (∀ u0, (Fc u0).SubIn) ∧
  (∀ u0 u, 0 < (Fc u0).r u) ∧
  DivIn (glob6 x ε k v g₁ g₂ C.cHH) C TT T2 a (fun u0 => (Fc u0).toFam) Rw logOm C0 g₁ g₂ ∧
  (PropZ (mkData (glob6 x ε k v g₁ g₂ C.cHH) C.cHH D ell N TT T2 a w (fun u0 => (Fc u0).toFam)) cZ O.Sc O.LZ ∧
    0 ≤ cZ ∧ 0 ≤ cL ∧ 0 ≤ O.Sc ∧ O.Sc ≤ Real.exp (x ^ (ε / 4)) ∧ O.LZ ≤ cL * Real.log (aTx x ε * (2 * v)) ∧
    cSlopeZ cZ cL (c5 + 1) ≤ C.cSlope) ∧
  (ExactCoeff5 (mkData (glob6 x ε k v g₁ g₂ C.cHH) C.cHH D ell N TT T2 a w (fun u0 => (Fc u0).toFam)) cE5 O.X O.bN ∧
    (∀ u0 (u : W u0), Real.log (O.X u0 u) ≤ c5 * (m : ℝ) * x ^ ε) ∧
    Variation5 (mkData (glob6 x ε k v g₁ g₂ C.cHH) C.cHH D ell N TT T2 a w (fun u0 => (Fc u0).toFam)) c5 O.X ∧
    SectionsFourToSixTransfer.LevelWindow (mkData (glob6 x ε k v g₁ g₂ C.cHH) C.cHH D ell N TT T2 a w (fun u0 => (Fc u0).toFam)) O.Gam O.X ∧
    1 ≤ O.Gam ∧ Real.log O.Gam / (((PhiSet (H := H)).card : ℝ) * k) ≤ 1 ∧ 0 ≤ c5 ∧ cE5 + 6 ≤ c5 ∧ c5 + 3 ≤ C.cCount ∧
    ∀ u0 j ρ, 0 < O.bN u0 j ρ ∧ w u0 j (ePhi ρ) ≤ O.bN u0 j ρ * (1 + 1 / x) ∧ Real.log (O.bN u0 j ρ) ≤ 2 * x ^ ε) ∧
  (3 ≤ C0S ∧ ∀ u0 (u : W u0), 0 < O.dst u0 u ∧
    O.X u0 u ^ (((PhiSet (H := H)).card : ℝ) * k) = (Fc u0).Dstar / O.dst u0 u ∧
    ((Fc u0).d u : ℝ) = O.dst u0 u * (((Fc u0).T u : ℝ) ^ k - 1) ^ (PhiSet (H := H)).card) ∧
  (O.aM ≤ 2 * aTx x ε ∧ (∀ t, O.Wt t ≤ 2 * bpTx x ε) ∧ (∀ t : TT, O.bt t = btH t) ∧
    ∀ u0 u, (Fc u0).lam u
      ≤ lambdaIndex (mkData (glob6 x ε k v g₁ g₂ C.cHH) C.cHH D ell N TT T2 a w (fun u0 => (Fc u0).toFam)) O.aM (O.VV u0 u)
          O.Wt O.bt) ∧
  Sizes6 x ε eK K k m N TT T2 a w η κ off btH (x ^ (-C.cHH)) O.Gam C0S g₁ g₂
end DefsD'
def Chain6Core' (A Cord eD eL K cHH eK CL eW KW ε x : ℝ) : Prop :=
  ∃ (e q d : ℕ) (_ : Fact q.Prime) (_ : Fact d.Prime) (Ω : Type) (_ : Fintype Ω)
    (W : Ω → HA e → Type) (_ : ∀ o u0, Fintype (W o u0)) (_ : ∀ o u0, Nonempty (W o u0)) (m : ℕ)
    (k : ℝ) (C : Consts) (N : ℕ)
    (TT T2 : Finset (HA e)) (a btH : Ω → HA e → ℝ) (w : Ω → HA e → Fin m → E0 × HA e → ℝ)
    (Fc : ∀ o u0, FamC (W o u0) m) (Rw : ∀ o u0, Rows (Fc o u0).toFam) (O : ∀ o, SizeCountLevelObjects (HA e) (W o) m TT)
    (Lp : HA e → Ω → LossP (HA e) m)
    (P : PrimeWindowSizeBounds.Par) (π : Ω → ℝ) (s sB : Finset ℕ) (BAD : ℕ → HA e → Prop) (Sig : ℕ → Ω → ℝ) (η κ off : ℝ)
    (g₁ g₂ : ℕ) (logOm C0 cZ cL cE5 c5 C0S : ℝ),
    C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ 1 ≤ C.cHH ∧ C.cHH ≤ cHH ∧ ConstsBound C K ∧ 28 ≤ C.cSl1 ∧
    P.e₂ = e ∧ P.η = η ∧ (∀ o, (O o).Sc = P.Sc) ∧
    ((2 ^ e : ℕ) : ℝ) ≤ x ^ A ∧ PrimePairBounds ε CL x q d ∧
    g₁.Prime ∧ g₂.Prime ∧
    PerHost e q d logOm ∧
    LossHyp (hostData e q d) (glob6 x ε k (hostV e q d) g₁ g₂ C.cHH) C N TT a w (fun o u0 => (Fc o u0).toFam) Lp P π s sB
      BAD Sig Cord eW KW ∧
    ∀ o, 0 < π o →
      (∀ u0, Fam6.GainIn (Fc o u0).toFam (inertPs (hostData e q d) N) (Lp u0 o).cl (TT.card : ℝ) (aTx x ε)) ∧
      Inputs6d' (hostData e q d) (hostEll e q d) x ε k (hostV e q d) C N TT T2 (a o) (w o) (Fc o) (Rw o) (O o) η eK K logOm
        C0 cZ cL cE5 c5 C0S κ off (btH o) g₁ g₂
def Core6'ToCore6 : Prop :=
  ∀ ε eW KW : ℝ, 0 < ε → ε < 1 / 4 → ∃ x₁ : ℝ, ∀ A Cord eD eL K cHH eK CL x : ℝ, x₁ ≤ x →
    Chain6Core' A Cord eD eL K cHH eK CL eW KW ε x → Chain6Core A Cord eD eL K cHH eK CL eW KW ε x
def Chain6' : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ A K cHH eK CL eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x → Chain6Core' A Cord eD eL K cHH eK CL eW KW ε x) →
    RiemannHypothesis
def Chain6At' : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK CL eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → Chain6Core' A Cord eD eL K cHH eK CL eW KW ε x →
      Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε)
section Top6
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {m : ℕ}
def TopAtLevel6 (D : ArithData H) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (T : H → ℕ)
    (G : Glob) (logOm lg C0 eDiv : ℝ) : Prop :=
  ∀ u0, (∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w u0 j)) ≤
    (∑ t ∈ TT, ((m : ℝ) * (Formalism.LatticeIndexTer.ph (a t) - a t * logOm) - a t * Real.log (T u0 : ℝ)))
      + (m : ℝ) * (∑ t ∈ TT, a t) * lg
      + (50 * C0 + 10) * ((TT.card : ℝ) * (G.x * Real.exp (G.x ^ G.ε)) * G.La
          + (m : ℝ) * (budgetAtPoint H G m + NcTx G T2) * G.x ^ (eDiv * G.ε))
def ExponentSixBoundOfLeadingBound : Prop :=
  ∀ (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (T : H → ℕ) (C0 : ℝ), C.cDiv = 50 * C0 + 10 →
    TopAtLevel D ell G C N TT T2 a w T →
    TopAtLevel6 D N TT T2 a w T G
      (Real.eulerMascheroniConstant + Real.log (Real.pi / G.v) - (ell chC).re) G.lg C0 C.eDiv
end Top6
def exactMain6 {U0 : Type} {m f : ℕ} (k v lg : ℝ) (bN : U0 → Fin m → Fin f → ℝ) (u0 : U0) : ℝ :=
  (((m : ℝ) - 1) + (m : ℝ) * ((m : ℝ) - 1) / (2 * k)) * Real.log (v / Real.pi)
    - (((m : ℝ) - 1) / (2 * k)) * Real.log (2 * v)
    + ((m : ℝ) + (m : ℝ) * ((m : ℝ) - 1) / (2 * k)) * lg
    + ((k - 1) / k) * ((1 / (f : ℝ)) * ∑ ρ : Fin f, ∑ j : Fin m, Real.log (bN u0 j ρ))
def TopIn6 (A Cord K eK CL eW KW ε x C0S : ℝ) (C : Consts) : Prop :=
  ∃ (e q d : ℕ) (_ : Fact q.Prime) (_ : Fact d.Prime) (N : ℕ) (TT T2 : Finset (HA e)) (m : ℕ) (a btH : HA e → ℝ)
    (w : HA e → Fin m → E0 × HA e → ℝ) (bN : HA e → Fin m → Fin (PhiSet (H := HA e)).card → ℝ) (k : ℝ)
    (η κ off C0 cE5 c5 : ℝ) (T : HA e → ℕ) (P : PrimeWindowSizeBounds.Par) (g₁ g₂ : ℕ),
    FrobeniusOrbits.HostHyp q d ∧
    1 ≤ C.cHH ∧ ConstsBound C K ∧ 28 ≤ C.cSl1 ∧
    P.e₂ = e ∧ P.η = η ∧ ((2 ^ e : ℕ) : ℝ) ≤ x ^ A ∧ PrimePairBounds ε CL x q d ∧
    g₁.Prime ∧ g₂.Prime ∧
    LossSide (hostData e q d) (glob6 x ε k (hostV e q d) g₁ g₂ C.cHH) C N TT a w P Cord eW KW ∧
    1 ≤ x ∧ 1 ≤ k ∧ 1 ≤ m ∧ 0 ≤ Real.log (aTx x ε * (2 * hostV e q d)) ∧
    50 * C0 + 10 ≤ C.cDiv ∧ 9 * C0 ^ 2 + 6 * C0 + 20 ≤ C.cE ∧ 7 * C0 ^ 2 + 18 ≤ C.cH ∧
    2 * (c5 + 1) ≤ C.cSlope ∧ 0 ≤ P.Sc ∧ P.Sc ≤ Real.exp (x ^ (ε / 4)) ∧
    0 ≤ c5 ∧ cE5 + 6 ≤ c5 ∧ c5 + 3 ≤ C.cCount ∧
    (∀ u0, (T u0).Prime) ∧ (∀ u0, 4 * (PhiSet (H := HA e)).card ≤ T u0) ∧
    (∀ u0, ((PhiSet (H := HA e)).card : ℝ) / ((T u0 : ℝ) - 1) ≤ E7 x ε) ∧
    (∀ u0, exactMain6 k (hostV e q d) (Real.log ((g₁ : ℝ) * (g₂ : ℝ))) bN u0 - cE5 * x ^ ε ≤ Real.log (T u0 : ℝ)) ∧
    (∀ u0, Real.log (T u0 : ℝ) ≤ c5 * (m : ℝ) * x ^ ε) ∧
    (∀ u0 j ρ, 0 < bN u0 j ρ ∧ w u0 j (ePhi ρ) ≤ bN u0 j ρ * (1 + 1 / x) ∧ Real.log (bN u0 j ρ) ≤ 2 * x ^ ε) ∧
    TopAtLevel6 (hostData e q d) N TT T2 a w T (glob6 x ε k (hostV e q d) g₁ g₂ C.cHH)
      (Real.eulerMascheroniConstant + Real.log (Real.pi / hostV e q d) - (hostEll e q d chC).re)
      (Real.log ((g₁ : ℝ) * (g₂ : ℝ))) C0 C.eDiv ∧
    Sizes6 x ε eK K k m N TT T2 a w η κ off btH (x ^ (-C.cHH)) 1 C0S g₁ g₂
def Chain6CoreOfTop : Prop :=
  ∀ (A Cord K eK CL eW KW ε x C0S : ℝ) (C : Consts), 2 ≤ C0S → TopIn6 A Cord K eK CL eW KW ε x C0S C →
    Chain6Core A Cord C.eDiv C.eLoss K C.cHH eK CL eW KW ε x
def Chain6Core'OfTop : Prop :=
  ∀ (A Cord K eK CL eW KW ε x C0S : ℝ) (C : Consts), 3 ≤ C0S → TopIn6 A Cord K eK CL eW KW ε x C0S C →
    Chain6Core' A Cord C.eDiv C.eLoss K C.cHH eK CL eW KW ε x
end Formalism.LFunctionChainParameters.LChain6


