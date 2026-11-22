-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_Chain2aCoreNoAnalytic
-- name    : Formalism_SizeWindowBrackets_Chain2aCoreNoAnalytic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:56:48.96881+00:00
-- url     : https://prove2.me/theorems/f9bcffb1-3e21-4e9f-8d53-3378ae6aa717
-- title:
--   Chain2a Core No Analytic
-- statement:
--   Definitions and structural lemmas for Chain2a Core No Analytic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/Chain2aCoreNoAnalytic.lean

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_SlopeHypothesesRounded
import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.HN
noncomputable section
namespace Formalism.LFunctionChainParameters.LChain2
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
instance decFinPl (K : Type) [Field K] [NumberField K] : DecidableEq (slopeLatticeData.FinPl K) := Classical.decEq _
section Places
variable {K : Type} [Field K] [NumberField K]
def prBelow (w : slopeLatticeData.FinPl K) : ℕ := Ideal.absNorm (w.1.under ℤ)
def ramE (w : slopeLatticeData.FinPl K) : ℝ := (w.1.ramificationIdx ℤ : ℝ)
def lE (w : slopeLatticeData.FinPl K) : ℝ := slopeLatticeData.ell w * ramE w
end Places
def UnitRulePl : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    (∀ w : slopeLatticeData.FinPl K, (prBelow w).Prime ∧ 0 < ramE w) ∧
    ∀ (S : Finset (slopeLatticeData.FinPl K)) (p : ℕ), p.Prime → (∀ w : slopeLatticeData.FinPl K, prBelow w = p → w ∈ S) →
      ∑ w ∈ S.filter (fun w => prBelow w = p), lE w = Real.log (p : ℝ)
structure Fam (I : Type) (m : ℕ) where

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

  κ : Type
  [firstRealIndex : Fintype κ]
  [secondRealIndex : DecidableEq κ]

  κ₁ : Type
  [firstRationalIndex : Fintype κ₁]
  [secondRationalIndex : DecidableEq κ₁]

  V : I → Type
  [indexVFirst : ∀ i, AddCommGroup (V i)]
  [indexVSecond : ∀ i, Module K (V i)]
  [indexVThird : ∀ i, Module (𝓞 K) (V i)]
  [indexVFourth : ∀ i, IsScalarTower (𝓞 K) K (V i)]

  ι : I → Type
  [indexCFirst : ∀ i, Fintype (ι i)]
  [indexCSecond : ∀ i, DecidableEq (ι i)]

  Vf : I → Type
  [indexFFirst : ∀ i, AddCommGroup (Vf i)]
  [indexFSecond : ∀ i, Module K (Vf i)]
  [indexFThird : ∀ i, Module (𝓞 K) (Vf i)]
  [indexFFourth : ∀ i, IsScalarTower (𝓞 K) K (Vf i)]

  ιf : I → Type
  [indexDFirst : ∀ i, Fintype (ιf i)]
  [indexDSecond : ∀ i, DecidableEq (ιf i)]
  b' : Basis κ K Wd
  X' : InfinitePlace K → Matrix κ κ ℂ

  cc : Submodule (𝓞 K) Wd
  b : ∀ i, Basis (ι i) K (V i)
  X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ

  M : ∀ i, Submodule (𝓞 K) (V i)

  N0 : ∀ i, Submodule (𝓞 K) (V i)
  bf : ∀ i, Basis (ιf i) K (Vf i)
  Xf : ∀ i, InfinitePlace K → Matrix (ιf i) (ιf i) ℂ

  Mf : ∀ i, Submodule (𝓞 K) (Vf i)

  σ : I → slopeLatticeData.FinPl K →₀ ℤ

  τ : slopeLatticeData.FinPl K →₀ ℤ

  B : ∀ i, V i →ₗ[K] Wd

  v : InfinitePlace K
  Y : ∀ i, Matrix (ι i) (ι i) ℂ
  Y' : Matrix κ κ ℂ
  Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ
  γ : I → ℝ
  Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ
  Vr : ∀ i, Matrix (ιf i) (ι i) ℂ

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
attribute [instance] Fam.indexKFirst Fam.indexKSecond Fam.indexKThird Fam.indexKFourth Fam.indexWFirst Fam.indexWSecond Fam.indexWThird Fam.indexWFourth Fam.firstRealIndex Fam.secondRealIndex Fam.firstRationalIndex Fam.secondRationalIndex
  Fam.indexVFirst Fam.indexVSecond Fam.indexVThird Fam.indexVFourth Fam.indexCFirst Fam.indexCSecond Fam.indexFFirst Fam.indexFSecond Fam.indexFThird Fam.indexFFourth Fam.indexDFirst Fam.indexDSecond
namespace Fam
variable {I : Type} {m : ℕ} (F : Fam I m)
def N' (u : I) : Submodule (𝓞 F.K) (F.V u) := slopeLatticeData.modLat (F.σ u) (F.N0 u)
def ItM (u : I) : Submodule (𝓞 F.K) (F.V u) :=
  Formalism.HermitianLatticesTheory.idealSmul ((slopeLatticeData.idealPow F.τ : FractionalIdeal (nonZeroDivisors (𝓞 F.K)) F.K) :
    Submodule (𝓞 F.K) F.K) (F.M u)
def du (u : I) : ℝ := (Fintype.card (F.ι u) : ℝ)
def dM (u : I) : ℝ := (Fintype.card (F.ιf u) : ℝ)
def tauR (w : slopeLatticeData.FinPl F.K) : ℝ := (F.τ w : ℝ) / ramE w
def sgR (u : I) (w : slopeLatticeData.FinPl F.K) : ℝ := (F.σ u w : ℝ) / ramE w
def lenN (u : I) (w : slopeLatticeData.FinPl F.K) : ℕ := (slopeLatticeData.lenAt w (F.ItM u) (F.N0 u)).toNat
def lenR (u : I) (w : slopeLatticeData.FinPl F.K) : ℝ := ((F.lenN u w : ℝ) + F.du u * (F.τ w : ℝ)) / ramE w
def sgw (u : I) (w : slopeLatticeData.FinPl F.K) : ℝ := UnitWeightPartition.sgw Finset.univ F.gain F.Fj (F.Ej u) w
def ST (u : I) : Finset (slopeLatticeData.FinPl F.K) := F.S.filter (fun w => prBelow w = F.T u)
def Pr : Finset ℕ := F.S.image prBelow
def Ga : ℝ := UnitWeightPartition.Ga F.S Finset.univ lE F.gain F.tauR
def Fo : ℝ := UnitWeightPartition.Fo F.S Finset.univ lE F.Fj
def Ta : ℝ := UnitWeightPartition.Ta F.S lE F.tauR
def EeJ (u : I) (j : Fin m) : ℝ := 2 * ∑ w ∈ F.S, lE w * F.Ej u j w
def IO : ℝ := ∑ p ∈ F.Pr, Real.log (p : ℝ) * F.iop p
def Rd (u : I) : ℝ := ∑ w ∈ F.S, 2 * lE w * (F.sgw u w - F.sgR u w)
def del : ℝ := 1 - (Fintype.card F.κ : ℝ) / (Fintype.card (F.κ ⊕ F.κ₁) : ℝ)
def deF [Fintype I] : ℝ := 1 - MatrixLatticeEstimates.RsG F.ι / MatrixLatticeEstimates.RsG F.ιf
def LatHyp [Fintype I] (sg : ℝ) : Prop :=
  MatrixLatticeEstimates.LatGeom F.b' F.X' F.cc F.b F.X F.N' F.B F.h F.v F.Y F.Y' F.Ball F.del ∧
  (∀ i, 0 < F.γ i) ∧ (∀ i, F.Ball i = F.Bf i * F.Vr i) ∧ (∀ i, (F.Vr i)ᴴ * F.Vr i = 1) ∧
  0 < F.Dstar ∧ 0 < sg ∧ sg ≤ 1 / 20 ∧ F.Dstar / sg ≤ MatrixLatticeEstimates.RsG F.ιf ∧
  -1 ≤ F.η0 ∧ F.η0 ≤ sg / 2 ∧ F.η1 ≤ sg / 2 ∧ 0 ≤ F.e0 ∧ Real.sqrt F.e0 ≤ sg / 2 ∧
  MatrixLatticeEstimates.InputSG F.Bf F.γ F.Dstar F.η0 F.η1 F.e0
def PlaceHyp (f : ℕ) (bb : ℝ) : Prop :=
  (∀ w ∈ F.S, 0 ≤ F.τ w) ∧ (∀ w, w ∉ F.S → F.τ w = 0) ∧ (∀ w ∈ F.S, 0 ≤ F.iop (prBelow w)) ∧
  (∀ w ∈ F.S, ∀ w' : slopeLatticeData.FinPl F.K, prBelow w' = prBelow w → w' ∈ F.S) ∧
  F.Ta ≤ bb ^ 2 ∧
  ∀ u : I,
    (F.M u).FG ∧ Submodule.span F.K (F.M u : Set (F.V u)) = ⊤ ∧
    (F.Mf u).FG ∧ Submodule.span F.K (F.Mf u : Set (F.Vf u)) = ⊤ ∧ F.N0 u ≤ F.ItM u ∧
    rkK (F.N0 u) = rkK (F.M u) ∧
    (∀ w, w ∉ F.S → F.σ u w = 0 ∧ F.lenN u w = 0) ∧
    4 * (f : ℝ) ≤ (F.T u : ℝ) ∧ F.T u ∈ F.Pr ∧ (∀ w ∈ F.ST u, F.τ w = 0) ∧
    F.du u = F.dM u * (1 - 1 / ((F.T u : ℝ) - 1)) ^ f ∧
    (∀ w ∈ F.S \ F.ST u, F.lenR u w ≤ F.dM u * (F.tauR w + F.iop (prBelow w))) ∧
    (∀ w ∈ F.ST u, F.lenR u w ≤ F.dM u * F.lam u) ∧ 0 ≤ F.lam u ∧
    (∀ w ∈ F.S, F.sgR u w ≤ F.sgw u w) ∧
    muDef (F.b u) (F.X u) (F.M u) = muDef (F.bf u) (F.Xf u) (F.Mf u)
      - (f : ℝ) * Real.log ((F.T u : ℝ) - 1) / ((F.T u : ℝ) - 2) ∧
    muMaxDef (F.b u) (F.X u) (F.M u) ≤ muMaxDef (F.bf u) (F.Xf u) (F.Mf u) ∧
    4 * (f : ℝ) / (F.T u : ℝ) * bb ^ 2
      + (f : ℝ) * Real.log ((F.T u : ℝ) - 1) / ((F.T u : ℝ) - 2) ≤ 1
end Fam
structure Glob where

  x : ℝ

  ε : ℝ

  k : ℝ

  La : ℝ

  v : ℝ

  lg : ℝ

  delBar : ℝ

  etaBar : ℝ

  eBar : ℝ
section Data
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}
def ePhi : Fin (PhiSet (H := H)).card ≃ PhiSet (H := H) := (PhiSet (H := H)).equivFin.symm
def sgX (G : Glob) (cHH : ℝ) : ℝ := G.x ^ (-cHH)
def XppH (H : Type) [Fintype H] (G : Glob) : ℝ := XppTx G.x G.ε (Fintype.card H : ℝ)
def mkData (G : Glob) (cHH : ℝ) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H)
    (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) :
    Data H W TT m (PhiSet (H := H)).card where
  x := G.x
  ε := G.ε
  a := aTx G.x G.ε
  b := bTx G.x G.ε
  b' := bpTx G.x G.ε
  k := G.k
  L := Real.log (bTx G.x G.ε)
  La := G.La
  B0 := (2 * (Fintype.card H : ℝ)) * m * bTx G.x G.ε * G.x ^ G.ε
  Nc := (T2.card : ℝ) * G.k * bTx G.x G.ε * G.x ^ G.ε
    / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * G.x ^ (-G.ε)))
  gam := Real.eulerMascheroniConstant
  LpL := (ell chC).re
  v := G.v
  lg := G.lg
  logGam := 0
  aT := fun t => a t
  w := fun u0 j ρ => w u0 j (ePhi ρ)
  d := fun u0 u => (Fm u0).du u
  T := fun u0 u => ((Fm u0).T u : ℝ)
  muN := fun u0 u => muDef ((Fm u0).b u) ((Fm u0).X u) ((Fm u0).N' u)
  muMaxN := fun u0 u => muMaxDef ((Fm u0).b u) ((Fm u0).X u) ((Fm u0).N' u)
  h := fun u0 u => (Fm u0).h u
  muM := fun u0 u => muDef ((Fm u0).bf u) ((Fm u0).Xf u) ((Fm u0).Mf u)
  muMaxM := fun u0 u => muMaxDef ((Fm u0).bf u) ((Fm u0).Xf u) ((Fm u0).Mf u)
  EeJ := fun u0 u j => (Fm u0).EeJ u j
  muCC := fun u0 => muDef (Fm u0).b' (Fm u0).X' (Fm u0).cc
  muMinCC := fun u0 => muMinDef (Fm u0).b' (Fm u0).X' (Fm u0).cc
  Fo := fun u0 => (Fm u0).Fo
  Ga := fun u0 => (Fm u0).Ga
  Ta := fun u0 => (Fm u0).Ta
  ASK := fun u0 => ∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w u0 j)
  IO := fun u0 => (Fm u0).IO
  HH := fun _ => G.x ^ cHH * bTx G.x G.ε
  del := fun u0 => (Fm u0).del
  η := fun u0 => 5 * sgX G cHH + 3 * Real.sqrt (Fm u0).deF
  e := fun u0 => 2 * (Fm u0).e0
  delBar := G.delBar
  etaBar := G.etaBar
  eBar := G.eBar
def SizesPl (G : Glob) (C : Consts) (cT : ℝ) (TT : Finset H) (Fm : ∀ u0, Fam (W u0) m) : Prop :=
  4 ≤ C.cSl1 ∧ 4 * cT ≤ C.cSl1 ∧
  ∀ u0 (u : W u0),
    (Fm u0).lam u ≤ cT * (TT.card : ℝ) * (m : ℝ) * (aTx G.x G.ε / G.k + bpTx G.x G.ε) ∧
    (Fm u0).Rd u ≤ C.cSl1 * XppH H G
def DefinedFields : Prop :=
  ∀ (G : Glob) (cHH : ℝ) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H)
    (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m),
    (∀ u0 u, (mkData G cHH D ell N TT T2 a w Fm).d u0 u = (Fintype.card ((Fm u0).ι u) : ℝ)) ∧
    (∀ u0 u, (mkData G cHH D ell N TT T2 a w Fm).muN u0 u
      = muDef ((Fm u0).b u) ((Fm u0).X u) (slopeLatticeData.modLat ((Fm u0).σ u) ((Fm u0).N0 u))) ∧
    (∀ u0 u, (mkData G cHH D ell N TT T2 a w Fm).muMaxN u0 u
      = muMaxDef ((Fm u0).b u) ((Fm u0).X u) (slopeLatticeData.modLat ((Fm u0).σ u) ((Fm u0).N0 u))) ∧
    (∀ u0 u, (mkData G cHH D ell N TT T2 a w Fm).muM u0 u = muDef ((Fm u0).bf u) ((Fm u0).Xf u) ((Fm u0).Mf u)) ∧
    (∀ u0 u, (mkData G cHH D ell N TT T2 a w Fm).muMaxM u0 u
      = muMaxDef ((Fm u0).bf u) ((Fm u0).Xf u) ((Fm u0).Mf u)) ∧
    (∀ u0, (mkData G cHH D ell N TT T2 a w Fm).muCC u0 = muDef (Fm u0).b' (Fm u0).X' (Fm u0).cc) ∧
    (∀ u0, (mkData G cHH D ell N TT T2 a w Fm).muMinCC u0 = muMinDef (Fm u0).b' (Fm u0).X' (Fm u0).cc) ∧
    (∀ u0, (mkData G cHH D ell N TT T2 a w Fm).Ga u0
      = 2 * ∑ w ∈ (Fm u0).S, slopeLatticeData.ell w * ramE w * ((∑ j, (Fm u0).gain j w) - ((Fm u0).τ w : ℝ) / ramE w)) ∧
    (∀ u0, (mkData G cHH D ell N TT T2 a w Fm).Fo u0
      = 2 * ∑ j, ∑ w ∈ (Fm u0).S, slopeLatticeData.ell w * ramE w * (Fm u0).Fj j w) ∧
    (∀ u0 u, (mkData G cHH D ell N TT T2 a w Fm).Ee u0 u
      = ∑ j, 2 * ∑ w ∈ (Fm u0).S, slopeLatticeData.ell w * ramE w * (Fm u0).Ej u j w) ∧
    (∀ u0, (mkData G cHH D ell N TT T2 a w Fm).IO u0
      = ∑ p ∈ (Fm u0).S.image prBelow, Real.log (p : ℝ) * (Fm u0).iop p) ∧
    (∀ u0, (mkData G cHH D ell N TT T2 a w Fm).s u0
      = WeightedMeanLemmas.sF (fun u => (Fintype.card ((Fm u0).ι u) : ℝ))
          (fun u => muDef ((Fm u0).b u) ((Fm u0).X u) ((Fm u0).N' u)) (Fm u0).h)
variable [∀ u0, Nonempty (W u0)]
def SlopesOfPlaces : Prop :=
  ∀ (G : Glob) (C : Consts) (cT : ℝ) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H)
    (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m),
    0 < G.x → 0 < G.k →
    (∀ u0 u v, IsUnit ((Fm u0).X u v).det) → (∀ u0 u, 0 < (Fm u0).du u) →
    (∀ u0, (Fm u0).PlaceHyp (PhiSet (H := H)).card (bTx G.x G.ε)) → SizesPl G C cT TT Fm →
    QuotientSlopeBoundsWith (mkData G C.cHH D ell N TT T2 a w Fm) C (XppH H G)
def SlopeIneqOfFam : Prop :=
  ∀ (G : Glob) (cHH : ℝ) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H)
    (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m),
    (∀ u0, (Fm u0).LatHyp (sgX G cHH)) →
    (∀ u0 u, 3 / 4 * (Fm u0).dM u ≤ (Fm u0).du u ∧ (Fm u0).du u ≤ (Fm u0).dM u) →
    (mkData G cHH D ell N TT T2 a w Fm).SlopeIneq
def RanksOfPlaces : Prop :=
  ∀ (I : Type) (F : Fam I m) (f : ℕ) (bb : ℝ), 1 ≤ f → 2 ≤ bb ^ 2 → (∀ u, 0 < F.du u) → F.PlaceHyp f bb →
    ∀ u, 3 / 4 * F.dM u ≤ F.du u ∧ F.du u ≤ F.dM u
def InputsB (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m)
    (η θ eK K CL : ℝ) : Prop :=
  (∀ u0, (Fm u0).LatHyp (sgX G C.cHH)) ∧
  (∀ u0, (Fm u0).PlaceHyp (PhiSet (H := H)).card (bTx G.x G.ε)) ∧
  SizesPl G C cT TT Fm ∧
  0 < G.v ∧ (∀ u0 u, 0 < (Fm u0).du u) ∧ G.eBar ≤ 1 / 4 ∧
  (mkData G C.cHH D ell N TT T2 a w Fm).DIV C ∧
  EComp5 (mkData G C.cHH D ell N TT T2 a w Fm) C ∧
  (mkData G C.cHH D ell N TT T2 a w Fm).HComp C ∧
  Count5 (mkData G C.cHH D ell N TT T2 a w Fm) C ∧
  (mkData G C.cHH D ell N TT T2 a w Fm).Slopes C ∧
  (∀ u0, (mkData G C.cHH D ell N TT T2 a w Fm).s u0 - muMinDef (Fm u0).b' (Fm u0).X' (Fm u0).cc
    ≤ G.x ^ C.cHH * bTx G.x G.ε) ∧
  (∀ u0, (Fm u0).del ≤ G.delBar ∧ 5 * sgX G C.cHH + 3 * Real.sqrt (Fm u0).deF ≤ G.etaBar ∧
    2 * (Fm u0).e0 ≤ G.eBar) ∧
  ErrWindows (mkData G C.cHH D ell N TT T2 a w Fm) C (XppH H G) eK K ∧
  GrowthInequalityRemainingHyps D ell N TT T2 a w G.x G.ε (bTx G.x G.ε) (bpTx G.x G.ε) η (XpTx G.x G.ε) θ CL ∧
  CostWindows G.x (fPl H) (bTx G.x G.ε) η θ ∧
  RestSize G.ε G.x (Fintype.card H) TT.card T2.card m (bTx G.x G.ε) G.k (aTx G.x G.ε)
def Inputs2 (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m)
    (η θ eK K CL : ℝ) : Prop :=
  InputsB D ell G C cT N TT T2 a w Fm η θ eK K CL ∧ LossBounds (mkData G C.cHH D ell N TT T2 a w Fm) C
def HidaSettingOfHyp : Prop :=
  ∀ (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m)
    (η θ eK K CL : ℝ), InputsB D ell G C cT N TT T2 a w Fm η θ eK K CL →
    (mkData G C.cHH D ell N TT T2 a w Fm).HidaSetting C ∧
    QuotientSlopeBoundsWith (mkData G C.cHH D ell N TT T2 a w Fm) C (XppH H G) ∧
    (mkData G C.cHH D ell N TT T2 a w Fm).SlopeIneq ∧
    (mkData G C.cHH D ell N TT T2 a w Fm).HHBound C ∧
    (mkData G C.cHH D ell N TT T2 a w Fm).FParams
end Data
def Chain2aCore (eD eL K cHH eK CL ε x : ℝ) : Prop :=
  ∃ (H : Type) (_ : AddCommGroup H) (_ : Fintype H) (_ : DecidableEq H)
    (W : H → Type) (_ : ∀ u0, Fintype (W u0)) (_ : ∀ u0, Nonempty (W u0)) (m : ℕ)
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (η θ : ℝ),
    G.x = x ∧ G.ε = ε ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧ HostFacts D ∧
    Inputs2 D ell G C cT N TT T2 a w Fm η θ eK K CL
def hostEll (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (ψ : AddChar (E0 × LHost.HA e) ℂ) : ℂ :=
  haveI : NeZero (LHost.hostN e q d) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ two_ne_zero) (Fact.out : q.Prime).ne_zero)
      (Fact.out : d.Prime).ne_zero⟩
  haveI : NeZero (LHost.dirChar (LHost.recMap e q d) ψ).conductor :=
    ⟨DirichletCharacter.conductor_ne_zero _⟩
  deriv (DirichletCharacter.LFunction (LHost.dirChar (LHost.recMap e q d) ψ).primitiveCharacter) 1
    / DirichletCharacter.LFunction (LHost.dirChar (LHost.recMap e q d) ψ).primitiveCharacter 1
def Chain2Core (eD eL K cHH eK CL ε x : ℝ) : Prop :=
  ∃ (e q d : ℕ) (_ : Fact q.Prime) (_ : Fact d.Prime)
    (W : LHost.HA e → Type) (_ : ∀ u0, Fintype (W u0)) (_ : ∀ u0, Nonempty (W u0)) (m : ℕ)
    (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset (LHost.HA e)) (a : LHost.HA e → ℝ) (w : LHost.HA e → Fin m → E0 × LHost.HA e → ℝ)
    (Fm : ∀ u0, Fam (W u0) m) (η θ : ℝ),
    FrobeniusOrbits.HostHyp q d ∧ G.x = x ∧ G.ε = ε ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧
    Inputs2 (LHost.hostData e q d) (hostEll e q d) G C cT N TT T2 a w Fm η θ eK K CL
def Core2aToCore : Prop :=
  ∀ eD eL K cHH eK CL ε x : ℝ, Chain2aCore eD eL K cHH eK CL ε x → ChainCore eD eL K cHH eK CL ε x
def Core2ToCore2a : Prop :=
  ∀ eD eL K cHH eK CL ε x : ℝ, Chain2Core eD eL K cHH eK CL ε x → Chain2aCore eD eL K cHH eK CL ε x
def Chain2a : Prop :=
  ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ K cHH eK CL x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → Chain2aCore eD eL K cHH eK CL ε x) →
    RiemannHypothesis
def Chain2 : Prop :=
  ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ K cHH eK CL x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → Chain2Core eD eL K cHH eK CL ε x) →
    RiemannHypothesis
structure LossP (H : Type) (m : ℕ) where

  cl : ℕ → DeficitSplitLemmas.PClass

  TTp : ℕ → Finset H

  gainP : Fin m → ℕ → ℝ

  tauP : ℕ → ℝ

  lo : ℕ → ℝ

  fl : ℕ → ℝ

  L₁ : ℕ → ℝ
section Loss
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {Ω : Type} {W : Ω → H → Type} {m : ℕ}
def inertPs (D : ArithData H) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (N + 1)).filter (IsInert D)
def gD (D : ArithData H) (i : ℕ) : E0 × H :=
  if InPhi (i • D.frob D.d) then i • D.frob D.d + sgc0 else i • D.frob D.d
abbrev PlAll (Fm : ∀ o u0, Fam (W o u0) m) : Type := Σ (o : Ω) (u0 : H), slopeLatticeData.FinPl (Fm o u0).K
def plEmb (Fm : ∀ o u0, Fam (W o u0) m) (o : Ω) (u0 : H) : slopeLatticeData.FinPl (Fm o u0).K ↪ PlAll Fm :=
  (Function.Embedding.sigmaMk (β := fun u0 => slopeLatticeData.FinPl (Fm o u0).K) u0).trans
    (Function.Embedding.sigmaMk (β := fun o => Σ u0 : H, slopeLatticeData.FinPl (Fm o u0).K) o)
def ldOf (D : ArithData H) (N : ℕ) (a : Ω → H → ℝ) (w : Ω → H → Fin m → E0 × H → ℝ)
    (Fm : ∀ o u0, Fam (W o u0) m) (Lp : H → Ω → LossP H m) (u0 : H) (o : Ω) :
    PrimeWindowSizeBounds.LD (PlAll Fm) (Fin m) H where
  W := (Fm o u0).S.map (plEmb Fm o u0)
  below := fun z => prBelow z.2.2
  l := fun z => lE z.2.2
  cl := (Lp u0 o).cl
  TTp := (Lp u0 o).TTp
  Iex := fun _ _ p => (Finset.Icc 1 N).filter (fun i => ¬ InPhi (i • D.frob p))
  at_ := a o
  wz := fun j t p i => w o u0 j (partner t (i • D.frob p))
  Id := fun _ _ => Finset.Icc 1 N
  wd := fun j t i => w o u0 j (partner t (gD D i))
  gainW := fun j z => (Fm z.1 z.2.1).gain j z.2.2
  tauW := fun z => (Fm z.1 z.2.1).tauR z.2.2
  gain := (Lp u0 o).gainP
  tau := (Lp u0 o).tauP
  lo := (Lp u0 o).lo
  fl := (Lp u0 o).fl
  L₁ := (Lp u0 o).L₁
def LdIdent : Prop :=
  ∀ (D : ArithData H), HostFacts D → ∀ (N : ℕ) (TT : Finset H) (a : Ω → H → ℝ) (w : Ω → H → Fin m → E0 × H → ℝ)
    (Fm : ∀ o u0, Fam (W o u0) m) (Lp : H → Ω → LossP H m) (u0 : H) (o : Ω),
    (ldOf D N a w Fm Lp u0 o).ASK D.d (inertPs D N) Finset.univ TT
      = ∑ t ∈ TT, ∑ j : Fin m, ASK D N (a o t) t (w o u0 j) ∧
    (ldOf D N a w Fm Lp u0 o).Ga Finset.univ = (Fm o u0).Ga
variable [Fintype Ω] [∀ o u0, Fintype (W o u0)]
def LossHyp (D : ArithData H) (G : Glob) (C : Consts) (N : ℕ) (TT : Finset H) (a : Ω → H → ℝ)
    (w : Ω → H → Fin m → E0 × H → ℝ) (Fm : ∀ o u0, Fam (W o u0) m) (Lp : H → Ω → LossP H m)
    (P : PrimeWindowSizeBounds.Par) (π : Ω → ℝ) (s sB : Finset ℕ) (BAD : ℕ → H → Prop) (Sig : ℕ → Ω → ℝ) (Cord eW KW : ℝ) : Prop :=
  P.x = G.x ∧ P.ε = G.ε ∧ P.k = G.k ∧ P.d = D.d ∧ P.Cord = Cord ∧
  PrimeWindowSizeBounds.Windows P eW KW ∧
  PrimeWindowSizeBounds.WindowSettingHypotheses P π (inertPs D N) s sB (Finset.univ : Finset (Fin m)) TT BAD Sig
    (fun u0 p o => (Fm o u0).iop p) (ldOf D N a w Fm Lp) ∧
  (∀ o u0, (∀ p ∈ (Fm o u0).Pr, p ∉ s → (Fm o u0).iop p = 0) ∧ ∀ p ∈ s, 0 ≤ (Fm o u0).iop p) ∧
  3 * P.C + 13 ≤ C.cLoss ∧ 0 ≤ C.eLoss
def LossesOfWindow : Prop :=
  ∀ (D : ArithData H), HostFacts D → ∀ (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (N : ℕ)
    (TT T2 : Finset H) (a : Ω → H → ℝ)
    (w : Ω → H → Fin m → E0 × H → ℝ) (Fm : ∀ o u0, Fam (W o u0) m) (Lp : H → Ω → LossP H m)
    (P : PrimeWindowSizeBounds.Par) (π : Ω → ℝ) (s sB : Finset ℕ) (BAD : ℕ → H → Prop) (Sig : ℕ → Ω → ℝ) (Cord eW KW : ℝ) (o : Ω),
    LossHyp D G C N TT a w Fm Lp P π s sB BAD Sig Cord eW KW → 1 ≤ G.x →
    PrimeWindowSizeBounds.LossesWithinWindowUnit P (inertPs D N) s (Finset.univ : Finset (Fin m)) TT (fun u0 p o => (Fm o u0).iop p)
      (ldOf D N a w Fm Lp) o →
    LossBounds (mkData G C.cHH D ell N TT T2 (a o) (w o) (Fm o)) C
end Loss
def Chain2cCore (Cord eD eL K cHH eK CL eW KW ε x : ℝ) : Prop :=
  ∃ (e q d : ℕ) (_ : Fact q.Prime) (_ : Fact d.Prime) (Ω : Type) (_ : Fintype Ω)
    (W : Ω → LHost.HA e → Type) (_ : ∀ o u0, Fintype (W o u0)) (_ : ∀ o u0, Nonempty (W o u0)) (m : ℕ)
    (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset (LHost.HA e)) (a : Ω → LHost.HA e → ℝ) (w : Ω → LHost.HA e → Fin m → E0 × LHost.HA e → ℝ)
    (Fm : ∀ o u0, Fam (W o u0) m) (Lp : LHost.HA e → Ω → LossP (LHost.HA e) m)
    (P : PrimeWindowSizeBounds.Par) (π : Ω → ℝ) (s sB : Finset ℕ) (BAD : ℕ → LHost.HA e → Prop) (Sig : ℕ → Ω → ℝ) (η θ : ℝ),
    FrobeniusOrbits.HostHyp q d ∧ G.x = x ∧ G.ε = ε ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧ P.e₂ = e ∧
    LossHyp (LHost.hostData e q d) G C N TT a w Fm Lp P π s sB BAD Sig Cord eW KW ∧
    ∀ o, 0 < π o →
      InputsB (LHost.hostData e q d) (hostEll e q d) G C cT N TT T2 (a o) (w o) (Fm o) η θ eK K CL
def Core2cToCore2 : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ ε eW KW : ℝ, 0 < ε → ε < 1 / 4 → ∃ x₁ : ℝ, ∀ eD eL K cHH eK CL x : ℝ, x₁ ≤ x →
    Chain2cCore Cord eD eL K cHH eK CL eW KW ε x → Chain2Core eD eL K cHH eK CL ε x
def Chain2c : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ K cHH eK CL eW KW x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → Chain2cCore Cord eD eL K cHH eK CL eW KW ε x) →
    RiemannHypothesis
def hostV (e q d : ℕ) : ℝ := (2 : ℝ) ^ ((e : ℝ) - (2 : ℝ) ^ (-(e : ℝ))) * Real.sqrt ((q : ℝ) * (d : ℝ))
def PerHost (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (logOm : ℝ) : Prop :=
  logOm = Real.eulerMascheroniConstant + Real.log (Real.pi / hostV e q d) - (hostEll e q d chC).re
def DivAt {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} (Dd : Data U0 W Top m f) (C : Consts)
    (logOm : ℝ) : Prop :=
  ∀ u0 (u : W u0), Dd.muCC u0 + Dd.h u0 u - Dd.Fo u0 ≤
    (∑ t, ((m : ℝ) * (ph (Dd.aT t) - Dd.aT t * logOm) - Dd.aT t * Real.log (Dd.T u0 u)))
      + C.cDiv * Dd.nT * Dd.a * Dd.La + C.cDiv * (m : ℝ) * (Dd.B0 + Dd.Nc) * Dd.x ^ (C.eDiv * Dd.ε)
section DataD
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}
def InputsD (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m)
    (η θ eK K CL logOm : ℝ) : Prop :=
  (∀ u0, (Fm u0).LatHyp (sgX G C.cHH)) ∧
  (∀ u0, (Fm u0).PlaceHyp (PhiSet (H := H)).card (bTx G.x G.ε)) ∧
  SizesPl G C cT TT Fm ∧
  (∀ u0 u, 0 < (Fm u0).du u) ∧ G.eBar ≤ 1 / 4 ∧
  DivAt (mkData G C.cHH D ell N TT T2 a w Fm) C logOm ∧
  EComp5 (mkData G C.cHH D ell N TT T2 a w Fm) C ∧
  (mkData G C.cHH D ell N TT T2 a w Fm).HComp C ∧
  Count5 (mkData G C.cHH D ell N TT T2 a w Fm) C ∧
  (mkData G C.cHH D ell N TT T2 a w Fm).Slopes C ∧
  (∀ u0, (mkData G C.cHH D ell N TT T2 a w Fm).s u0 - muMinDef (Fm u0).b' (Fm u0).X' (Fm u0).cc
    ≤ G.x ^ C.cHH * bTx G.x G.ε) ∧
  (∀ u0, (Fm u0).del ≤ G.delBar ∧ 5 * sgX G C.cHH + 3 * Real.sqrt (Fm u0).deF ≤ G.etaBar ∧
    2 * (Fm u0).e0 ≤ G.eBar) ∧
  ErrWindows (mkData G C.cHH D ell N TT T2 a w Fm) C (XppH H G) eK K ∧
  GrowthInequalityRemainingHyps D ell N TT T2 a w G.x G.ε (bTx G.x G.ε) (bpTx G.x G.ε) η (XpTx G.x G.ε) θ CL ∧
  CostWindows G.x (fPl H) (bTx G.x G.ε) η θ ∧
  RestSize G.ε G.x (Fintype.card H) TT.card T2.card m (bTx G.x G.ε) G.k (aTx G.x G.ε)
def InputsDIff : Prop :=
  ∀ (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m)
    (η θ eK K CL : ℝ),
    InputsB D ell G C cT N TT T2 a w Fm η θ eK K CL ↔
      (0 < G.v ∧ InputsD D ell G C cT N TT T2 a w Fm η θ eK K CL
        (Real.eulerMascheroniConstant + Real.log (Real.pi / G.v) - (ell chC).re))
end DataD
def Chain2dCore (Cord eD eL K cHH eK CL eW KW ε x : ℝ) : Prop :=
  ∃ (e q d : ℕ) (_ : Fact q.Prime) (_ : Fact d.Prime) (Ω : Type) (_ : Fintype Ω)
    (W : Ω → LHost.HA e → Type) (_ : ∀ o u0, Fintype (W o u0)) (_ : ∀ o u0, Nonempty (W o u0)) (m : ℕ)
    (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset (LHost.HA e)) (a : Ω → LHost.HA e → ℝ) (w : Ω → LHost.HA e → Fin m → E0 × LHost.HA e → ℝ)
    (Fm : ∀ o u0, Fam (W o u0) m) (Lp : LHost.HA e → Ω → LossP (LHost.HA e) m)
    (P : PrimeWindowSizeBounds.Par) (π : Ω → ℝ) (s sB : Finset ℕ) (BAD : ℕ → LHost.HA e → Prop) (Sig : ℕ → Ω → ℝ) (η θ : ℝ)
    (g₁ g₂ : ℕ) (logOm : ℝ),
    FrobeniusOrbits.HostHyp q d ∧ G.x = x ∧ G.ε = ε ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧ P.e₂ = e ∧
    G.v = hostV e q d ∧ g₁.Prime ∧ g₂.Prime ∧ G.lg = Real.log ((g₁ : ℝ) * (g₂ : ℝ)) ∧
    PerHost e q d logOm ∧
    LossHyp (LHost.hostData e q d) G C N TT a w Fm Lp P π s sB BAD Sig Cord eW KW ∧
    ∀ o, 0 < π o →
      InputsD (LHost.hostData e q d) (hostEll e q d) G C cT N TT T2 (a o) (w o) (Fm o) η θ eK K CL logOm
def Core2dToCore2c : Prop :=
  ∀ Cord eD eL K cHH eK CL eW KW ε x : ℝ, Chain2dCore Cord eD eL K cHH eK CL eW KW ε x →
    Chain2cCore Cord eD eL K cHH eK CL eW KW ε x
def Chain2d : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ K cHH eK CL eW KW x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → Chain2dCore Cord eD eL K cHH eK CL eW KW ε x) →
    RiemannHypothesis
def LevelPrime : Prop :=
  ∀ (f : ℕ) (bb : ℝ), 1 ≤ f → ∀ n0 : ℕ, ∃ T : ℕ, T.Prime ∧ n0 ≤ T ∧ 4 * f ≤ T ∧
    4 * (f : ℝ) / (T : ℝ) * bb ^ 2 + (f : ℝ) * Real.log ((T : ℝ) - 1) / ((T : ℝ) - 2) ≤ 1
def FamModel : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (_ : InfinitePlace K)
    (m f T p₁ t₁ Mw : ℕ) (bb sg hb : ℝ),
    1 ≤ m → 1 ≤ f → T.Prime → p₁.Prime → p₁ ≠ T → 4 * f ≤ T →
    4 * (f : ℝ) / (T : ℝ) * bb ^ 2 + (f : ℝ) * Real.log ((T : ℝ) - 1) / ((T : ℝ) - 2) ≤ 1 →
    2 * ((t₁ : ℝ) * Real.log (p₁ : ℝ)) ≤ bb ^ 2 → 0 < sg → sg ≤ 1 / 20 → 1 / sg ≤ (Mw : ℝ) →
    ∃ F : Fam (Fin Mw) m, F.LatHyp sg ∧ F.PlaceHyp f bb ∧
      (∀ u, 0 < F.du u ∧ F.du u < F.dM u ∧ F.T u = T ∧ hb ≤ F.h u ∧ 0 < F.Rd u) ∧ 0 < F.del ∧
      (∃ w ∈ F.S, prBelow w = p₁) ∧
      (∀ w ∈ F.S, prBelow w = p₁ → F.tauR w = (t₁ : ℝ) ∧ ∀ u, F.sgR u w = (t₁ : ℝ))
section DataL
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}
def InputsL (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) : Prop :=
  (∀ u0, (Fm u0).LatHyp (sgX G C.cHH)) ∧
  (∀ u0, (Fm u0).PlaceHyp (PhiSet (H := H)).card (bTx G.x G.ε)) ∧
  SizesPl G C cT TT Fm ∧
  0 < G.v ∧ (∀ u0 u, 0 < (Fm u0).du u) ∧ G.eBar ≤ 1 / 4 ∧
  (mkData G C.cHH D ell N TT T2 a w Fm).DIV C ∧
  EComp5 (mkData G C.cHH D ell N TT T2 a w Fm) C ∧
  (mkData G C.cHH D ell N TT T2 a w Fm).HComp C ∧
  Count5 (mkData G C.cHH D ell N TT T2 a w Fm) C ∧
  (mkData G C.cHH D ell N TT T2 a w Fm).Slopes C ∧
  (∀ u0, (mkData G C.cHH D ell N TT T2 a w Fm).s u0 - muMinDef (Fm u0).b' (Fm u0).X' (Fm u0).cc
    ≤ G.x ^ C.cHH * bTx G.x G.ε) ∧
  (∀ u0, (Fm u0).del ≤ G.delBar ∧ 5 * sgX G C.cHH + 3 * Real.sqrt (Fm u0).deF ≤ G.etaBar ∧
    2 * (Fm u0).e0 ≤ G.eBar)
def InputsBSplit : Prop :=
  ∀ (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m)
    (η θ eK K CL : ℝ),
    InputsB D ell G C cT N TT T2 a w Fm η θ eK K CL ↔
      (InputsL D ell G C cT N TT T2 a w Fm ∧
        ErrWindows (mkData G C.cHH D ell N TT T2 a w Fm) C (XppH H G) eK K ∧
        GrowthInequalityRemainingHyps D ell N TT T2 a w G.x G.ε (bTx G.x G.ε) (bpTx G.x G.ε) η (XpTx G.x G.ε) θ CL ∧
        CostWindows G.x (fPl H) (bTx G.x G.ε) η θ ∧
        RestSize G.ε G.x (Fintype.card H) TT.card T2.card m (bTx G.x G.ε) G.k (aTx G.x G.ε))
end DataL
def ArithDataModel : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (_ : InfinitePlace K)
    (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ)
    (TT T2 : Finset H) (m : ℕ) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (x ε k La v lg cHH eDiv eLoss : ℝ),
    1 ≤ x → 0 < ε → 1 ≤ k → 0 < La → 0 < v → 1 ≤ m → TT.Nonempty → x ^ (-cHH) ≤ 1 / 20 →
    ∃ (Mw : ℕ) (G : Glob) (C : Consts) (cT : ℝ) (Fm : H → Fam (Fin Mw) m),
      0 < Mw ∧ (Mw : ℝ) < x ^ cHH + 1 ∧
      G.x = x ∧ G.ε = ε ∧ G.k = k ∧ G.La = La ∧ G.v = v ∧ G.lg = lg ∧
      G.delBar = 1 / 4 ∧ G.etaBar = 6 * x ^ (-cHH) ∧ G.eBar = 0 ∧
      C.cHH = cHH ∧ C.eDiv = eDiv ∧ C.eLoss = eLoss ∧
      (0 ≤ C.cDiv ∧ 0 ≤ C.cE ∧ 0 ≤ C.cH ∧ 0 ≤ C.cCount ∧ 0 ≤ C.cSlope ∧ 0 ≤ C.cSl1 ∧ 0 ≤ C.cLoss) ∧
      InputsL D ell G C cT N TT T2 a w Fm ∧ LossBounds (mkData G C.cHH D ell N TT T2 a w Fm) C
section DataT
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}
def TopOfInputs2 : Prop :=
  ∀ (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m)
    (η θ eK K CL : ℝ), Inputs2 D ell G C cT N TT T2 a w Fm η θ eK K CL →
    ∀ u0, (∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w u0 j))
      ≤ (mkData G C.cHH D ell N TT T2 a w Fm).Main u0 + ErrX5at (mkData G C.cHH D ell N TT T2 a w Fm) C (XppH H G) u0
end DataT
def StdSlopes : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (n : Type) [Fintype n] [DecidableEq n] [Nonempty n]
    (c : ℝ), 0 < c →
    muDef (Pi.basisFun K n) (fun _ => (c : ℂ) • (1 : Matrix n n ℂ))
      (Submodule.span (𝓞 K) (Set.range (Pi.basisFun K n))) = 2 * Real.log c ∧
    muMaxDef (Pi.basisFun K n) (fun _ => (c : ℂ) • (1 : Matrix n n ℂ))
      (Submodule.span (𝓞 K) (Set.range (Pi.basisFun K n))) = 2 * Real.log c ∧
    muMinDef (Pi.basisFun K n) (fun _ => (c : ℂ) • (1 : Matrix n n ℂ))
      (Submodule.span (𝓞 K) (Set.range (Pi.basisFun K n))) = 2 * Real.log c
def LevelWindow {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {m : ℕ} (G : Glob) (C : Consts)
    (w : H → Fin m → E0 × H → ℝ) (T : H → ℕ) : Prop :=
  ∀ u0, (T u0).Prime ∧ 4 * (PhiSet (H := H)).card ≤ T u0 ∧
    18 * ((PhiSet (H := H)).card : ℝ) / (G.x ^ (-C.cHH)) ^ 2 ≤ (T u0 : ℝ) ∧
    4 * ((PhiSet (H := H)).card : ℝ) / (T u0 : ℝ) * bTx G.x G.ε ^ 2
      + ((PhiSet (H := H)).card : ℝ) * Real.log ((T u0 : ℝ) - 1) / ((T u0 : ℝ) - 2) ≤ 1 ∧
    (∑ j : Fin m, (1 / ((PhiSet (H := H)).card : ℝ)) * ∑ ρ : Fin (PhiSet (H := H)).card,
        Real.log (w u0 j (ePhi ρ) * G.v / Real.pi)) + (m : ℝ) * G.lg
        - C.cCount * (G.La + (m : ℝ) ^ 2 * G.La / G.k) ≤ Real.log (T u0 : ℝ) ∧
    Real.log (T u0 : ℝ) ≤ C.cCount * (m : ℝ) * Real.log (bTx G.x G.ε)
def TopAtLevel {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {m : ℕ} (D : ArithData H)
    (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (T : H → ℕ) : Prop :=
  ∀ u0, (∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w u0 j)) ≤
    (∑ t : TT, ((m : ℝ) * (ph (a t) - a t * (Real.eulerMascheroniConstant + Real.log (Real.pi / G.v) - (ell chC).re))
        - a t * Real.log (T u0 : ℝ)))
      + (m : ℝ) * (∑ t : TT, a t) * G.lg
      + C.cDiv * (Fintype.card TT : ℝ) * aTx G.x G.ε * G.La
      + C.cDiv * (m : ℝ) * ((2 * (Fintype.card H : ℝ)) * m * bTx G.x G.ε * G.x ^ G.ε
          + (T2.card : ℝ) * G.k * bTx G.x G.ε * G.x ^ G.ε
            / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * G.x ^ (-G.ε))))
        * G.x ^ (C.eDiv * G.ε)
def CompletionSigns (G : Glob) (C : Consts) (cT : ℝ) (m : ℕ) : Prop :=
  1 ≤ G.x ∧ 0 < G.ε ∧ 1 ≤ G.k ∧ 0 ≤ G.La ∧ 0 < G.v ∧ 1 ≤ m ∧ G.x ^ (-C.cHH) ≤ 1 / 20 ∧
  (4 ≤ C.cSl1 ∧ 4 * cT ≤ C.cSl1 ∧ 0 ≤ cT ∧ 0 ≤ C.cE ∧ 0 ≤ C.cH ∧ 0 ≤ C.cCount ∧ 0 ≤ C.cSlope ∧ 0 ≤ C.cLoss) ∧
  (1 / 4 ≤ G.delBar ∧ 6 * G.x ^ (-C.cHH) ≤ G.etaBar ∧ 0 ≤ G.eBar ∧ G.eBar ≤ 1 / 4)
def LatticeCompletion : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (_ : InfinitePlace K)
    (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ)
    (TT T2 : Finset H) (m : ℕ) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (G : Glob) (C : Consts) (cT : ℝ) (T : H → ℕ),
    CompletionSigns G C cT m → LevelWindow G C w T → TopAtLevel D ell G C N TT T2 a w T →
    ∃ (Mw : ℕ) (Fm : H → Fam (Fin Mw) m), 0 < Mw ∧ (Mw : ℝ) < G.x ^ C.cHH + 1 ∧ (∀ u0 u, (Fm u0).T u = T u0) ∧
      InputsL D ell G C cT N TT T2 a w Fm ∧ LossBounds (mkData G C.cHH D ell N TT T2 a w Fm) C
def Chain2CoreOfTop : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d → ∀ (N : ℕ)
    (TT T2 : Finset (LHost.HA e)) (m : ℕ) (a : LHost.HA e → ℝ) (w : LHost.HA e → Fin m → E0 × LHost.HA e → ℝ)
    (G : Glob) (C : Consts) (cT η θ eK K CL : ℝ) (T : LHost.HA e → ℕ),
    CompletionSigns G C cT m → LevelWindow G C w T →
    TopAtLevel (LHost.hostData e q d) (hostEll e q d) G C N TT T2 a w T →
    (∀ (Mw : ℕ) (Fm : LHost.HA e → Fam (Fin Mw) m), 0 < Mw → (Mw : ℝ) < G.x ^ C.cHH + 1 →
      ErrWindows (mkData G C.cHH (LHost.hostData e q d) (hostEll e q d) N TT T2 a w Fm) C (XppH (LHost.HA e) G) eK K) →
    GrowthInequalityRemainingHyps (LHost.hostData e q d) (hostEll e q d) N TT T2 a w G.x G.ε (bTx G.x G.ε) (bpTx G.x G.ε) η
      (XpTx G.x G.ε) θ CL →
    CostWindows G.x (fPl (LHost.HA e)) (bTx G.x G.ε) η θ →
    RestSize G.ε G.x (Fintype.card (LHost.HA e)) TT.card T2.card m (bTx G.x G.ε) G.k (aTx G.x G.ε) →
    Chain2Core C.eDiv C.eLoss K C.cHH eK CL G.ε G.x
section LossC
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {m : ℕ}
def LossSide (D : ArithData H) (G : Glob) (C : Consts) (N : ℕ) (TT : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (P : PrimeWindowSizeBounds.Par) (Cord eW KW : ℝ) : Prop :=
  P.x = G.x ∧ P.ε = G.ε ∧ P.k = G.k ∧ P.d = D.d ∧ P.Cord = Cord ∧
  PrimeWindowSizeBounds.Windows P eW KW ∧ PrimeWindowSizeBounds.LargeX P.x P.ε eW KW ∧
  3 * P.C + 13 ≤ C.cLoss ∧ 0 ≤ C.eLoss ∧ TT.Nonempty ∧
  (∀ t ∈ TT, 0 ≤ a t ∧ a t ≤ P.a * (1 + P.th)) ∧
  (∀ u0 j, ∀ t ∈ TT, ∀ p ∈ inertPs D N, ∀ i ∈ Finset.Icc 1 N, ¬ InPhi (i • D.frob p) →
    P.wpp ≤ w u0 j (partner t (i • D.frob p))) ∧
  (∀ u0 j, ∀ t ∈ TT, ∀ i ∈ Finset.Icc 1 N, 0 ≤ w u0 j (partner t (gD D i)))
end LossC
def LossCompletion : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (_ : InfinitePlace K)
    (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H), HostFacts D →
    ∀ (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ)
    (TT T2 : Finset H) (m : ℕ) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (G : Glob) (C : Consts) (cT : ℝ) (T : H → ℕ)
    (P : PrimeWindowSizeBounds.Par) (Cord eW KW : ℝ),
    CompletionSigns G C cT m → LevelWindow G C w T → TopAtLevel D ell G C N TT T2 a w T →
    LossSide D G C N TT a w P Cord eW KW →
    ∃ (Mw : ℕ) (Fm : H → Fam (Fin Mw) m) (Lp : H → Unit → LossP H m),
      0 < Mw ∧ (Mw : ℝ) < G.x ^ C.cHH + 1 ∧ (∀ u0 u, (Fm u0).T u = T u0) ∧
      InputsL D ell G C cT N TT T2 a w Fm ∧
      LossHyp (W := fun _ _ => Fin Mw) D G C N TT (fun _ : Unit => a) (fun _ => w) (fun _ => Fm) Lp P (fun _ => 1) ∅ ∅
        (fun _ _ => False) (fun _ _ => 0) Cord eW KW
def Chain2cCoreOfTop : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d → ∀ (N : ℕ)
    (TT T2 : Finset (LHost.HA e)) (m : ℕ) (a : LHost.HA e → ℝ) (w : LHost.HA e → Fin m → E0 × LHost.HA e → ℝ)
    (G : Glob) (C : Consts) (cT η θ eK K CL : ℝ) (T : LHost.HA e → ℕ) (P : PrimeWindowSizeBounds.Par) (Cord eW KW : ℝ),
    CompletionSigns G C cT m → LevelWindow G C w T →
    TopAtLevel (LHost.hostData e q d) (hostEll e q d) G C N TT T2 a w T →
    LossSide (LHost.hostData e q d) G C N TT a w P Cord eW KW → P.e₂ = e →
    (∀ (Mw : ℕ) (Fm : LHost.HA e → Fam (Fin Mw) m), 0 < Mw → (Mw : ℝ) < G.x ^ C.cHH + 1 →
      ErrWindows (mkData G C.cHH (LHost.hostData e q d) (hostEll e q d) N TT T2 a w Fm) C (XppH (LHost.HA e) G) eK K) →
    GrowthInequalityRemainingHyps (LHost.hostData e q d) (hostEll e q d) N TT T2 a w G.x G.ε (bTx G.x G.ε) (bpTx G.x G.ε) η
      (XpTx G.x G.ε) θ CL →
    CostWindows G.x (fPl (LHost.HA e)) (bTx G.x G.ε) η θ →
    RestSize G.ε G.x (Fintype.card (LHost.HA e)) TT.card T2.card m (bTx G.x G.ε) G.k (aTx G.x G.ε) →
    Chain2cCore Cord C.eDiv C.eLoss K C.cHH eK CL eW KW G.ε G.x
def Chain2dCoreOfTop : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d → ∀ (N : ℕ)
    (TT T2 : Finset (LHost.HA e)) (m : ℕ) (a : LHost.HA e → ℝ) (w : LHost.HA e → Fin m → E0 × LHost.HA e → ℝ)
    (G : Glob) (C : Consts) (cT η θ eK K CL : ℝ) (T : LHost.HA e → ℕ) (P : PrimeWindowSizeBounds.Par) (Cord eW KW : ℝ) (g₁ g₂ : ℕ),
    G.v = hostV e q d → g₁.Prime → g₂.Prime → G.lg = Real.log ((g₁ : ℝ) * (g₂ : ℝ)) →
    CompletionSigns G C cT m → LevelWindow G C w T →
    TopAtLevel (LHost.hostData e q d) (hostEll e q d) G C N TT T2 a w T →
    LossSide (LHost.hostData e q d) G C N TT a w P Cord eW KW → P.e₂ = e →
    (∀ (Mw : ℕ) (Fm : LHost.HA e → Fam (Fin Mw) m), 0 < Mw → (Mw : ℝ) < G.x ^ C.cHH + 1 →
      ErrWindows (mkData G C.cHH (LHost.hostData e q d) (hostEll e q d) N TT T2 a w Fm) C (XppH (LHost.HA e) G) eK K) →
    GrowthInequalityRemainingHyps (LHost.hostData e q d) (hostEll e q d) N TT T2 a w G.x G.ε (bTx G.x G.ε) (bpTx G.x G.ε) η
      (XpTx G.x G.ε) θ CL →
    CostWindows G.x (fPl (LHost.HA e)) (bTx G.x G.ε) η θ →
    RestSize G.ε G.x (Fintype.card (LHost.HA e)) TT.card T2.card m (bTx G.x G.ε) G.k (aTx G.x G.ε) →
    Chain2dCore Cord C.eDiv C.eLoss K C.cHH eK CL eW KW G.ε G.x
def Chain2aCoreNoAnalytic (eD eL K cHH eK ε x : ℝ) : Prop :=
  ∃ (H : Type) (_ : AddCommGroup H) (_ : Fintype H) (_ : DecidableEq H)
    (W : H → Type) (_ : ∀ u0, Fintype (W u0)) (_ : ∀ u0, Nonempty (W u0)) (m : ℕ)
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (η θ : ℝ),
    G.x = x ∧ G.ε = ε ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧ HostFacts D ∧
    InputsL D ell G C cT N TT T2 a w Fm ∧
    ErrWindows (mkData G C.cHH D ell N TT T2 a w Fm) C (XppH H G) eK K ∧
    GrowthInequalitySizes TT T2 a w N G.x (bTx G.x G.ε) (bpTx G.x G.ε) η (XpTx G.x G.ε) θ ∧ 0 < θ ∧
    CostWindows G.x (fPl H) (bTx G.x G.ε) η θ ∧
    RestSize G.ε G.x (Fintype.card H) TT.card T2.card m (bTx G.x G.ε) G.k (aTx G.x G.ε) ∧
    LossBounds (mkData G C.cHH D ell N TT T2 a w Fm) C
def Chain2aCoreSplit : Prop :=
  ∀ eD eL K cHH eK CL ε x : ℝ, Chain2aCore eD eL K cHH eK CL ε x ↔
    ∃ (H : Type) (_ : AddCommGroup H) (_ : Fintype H) (_ : DecidableEq H)
      (W : H → Type) (_ : ∀ u0, Fintype (W u0)) (_ : ∀ u0, Nonempty (W u0)) (m : ℕ)
      (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
      (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (η θ : ℝ),
      G.x = x ∧ G.ε = ε ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧ HostFacts D ∧
      InputsL D ell G C cT N TT T2 a w Fm ∧
      ErrWindows (mkData G C.cHH D ell N TT T2 a w Fm) C (XppH H G) eK K ∧
      GrowthInequalitySizes TT T2 a w N G.x (bTx G.x G.ε) (bpTx G.x G.ε) η (XpTx G.x G.ε) θ ∧
      CostWindows G.x (fPl H) (bTx G.x G.ε) η θ ∧
      RestSize G.ε G.x (Fintype.card H) TT.card T2.card m (bTx G.x G.ε) G.k (aTx G.x G.ε) ∧
      LossBounds (mkData G C.cHH D ell N TT T2 a w Fm) C ∧
      ThinScales D ell (XpTx G.x G.ε) θ ∧ ValuesAtX D ell G.x G.ε CL
def Chain2aSizesModelEv : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → Chain2aCoreNoAnalytic 1 1 4 1 15 ε x
end Formalism.LFunctionChainParameters.LChain2


