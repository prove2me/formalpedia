-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChainLatticeSizesModelEventually
-- name    : Formalism_SizeWindowBrackets_ChainSlopeWindows_ChainLatticeSizesModelEventually
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:25:44.376031+00:00
-- url     : https://prove2.me/theorems/476bf957-5506-4663-9756-d9ff33cd8ce5
-- title:
--   Chain Lattice Sizes Model Eventually
-- statement:
--   Definitions and structural lemmas for Chain Lattice Sizes Model Eventually, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ChainLatticeSizesModelEventually.lean

import Definitions.Def_Formalism_SizeWindowBrackets_Chain2aCoreNoAnalytic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SlopeInequalityOfLattices
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ProjectiveLines
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
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
section Places
variable {K : Type} [Field K] [NumberField K]
end Places
namespace Fam
variable {I : Type} {m : ℕ} (F : Fam I m)
def prim (u : I) : LatticeToWeightTransfer.PPrim (slopeLatticeData.FinPl F.K) m where
  S := F.S
  ST := F.ST u
  l := lE
  gain := F.gain
  F := F.Fj
  E := F.Ej u
  tau := F.tauR
  io := fun w => F.iop (prBelow w)
  len := F.lenR u
  sg' := F.sgR u
  dM := F.dM u
  du := F.du u
  muMu := muDef (F.b u) (F.X u) (F.M u)
  muMaxMu := muMaxDef (F.b u) (F.X u) (F.M u)
  Rd := F.Rd u
  lam := F.lam u
  Pr := F.Pr
  pr := prBelow
  iop := F.iop
end Fam
def restr {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ} (D : Data U0 W Top m f) (u0 : U0) :
    Data Unit (fun _ => W u0) Top m f where
  x := D.x
  ε := D.ε
  a := D.a
  b := D.b
  b' := D.b'
  k := D.k
  L := D.L
  La := D.La
  B0 := D.B0
  Nc := D.Nc
  gam := D.gam
  LpL := D.LpL
  v := D.v
  lg := D.lg
  logGam := D.logGam
  aT := D.aT
  w := fun _ => D.w u0
  d := fun _ => D.d u0
  T := fun _ => D.T u0
  muN := fun _ => D.muN u0
  muMaxN := fun _ => D.muMaxN u0
  h := fun _ => D.h u0
  muM := fun _ => D.muM u0
  muMaxM := fun _ => D.muMaxM u0
  EeJ := fun _ => D.EeJ u0
  muCC := fun _ => D.muCC u0
  muMinCC := fun _ => D.muMinCC u0
  Fo := fun _ => D.Fo u0
  Ga := fun _ => D.Ga u0
  Ta := fun _ => D.Ta u0
  ASK := fun _ => D.ASK u0
  IO := fun _ => D.IO u0
  HH := fun _ => D.HH u0
  del := fun _ => D.del u0
  η := fun _ => D.η u0
  e := fun _ => D.e u0
  delBar := D.delBar
  etaBar := D.etaBar
  eBar := D.eBar
section Data
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}
variable [∀ u0, Nonempty (W u0)]
end Data
section Loss
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {Ω : Type} {W : Ω → H → Type} {m : ℕ}
variable [Fintype Ω] [∀ o u0, Fintype (W o u0)]
end Loss
section DataD
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}
end DataD
section ModelLemmas
open Formalism.LFunctionChainParameters.ProjectiveLineModels (stdLat inclMat)
variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
def inclL (κ κ₁ : Type) : (κ → K) →ₗ[K] (κ ⊕ κ₁ → K) where
  toFun x := Sum.elim x 0
  map_add' x y := by ext (a | a) <;> simp
  map_smul' r x := by ext (a | a) <;> simp
open Classical in

def plOver (p : ℕ) : Finset (slopeLatticeData.FinPl K) :=
  if h : {w : slopeLatticeData.FinPl K | prBelow w = p}.Finite then h.toFinset else ∅
def tau0 (p₁ t₁ : ℕ) : slopeLatticeData.FinPl K →₀ ℤ :=
  Finsupp.onFinset (plOver K p₁)
    (fun w => if w ∈ plOver K p₁ then ((w.1.ramificationIdx ℤ : ℕ) : ℤ) * (t₁ : ℤ) else 0)
    (fun w hw => by
      by_contra h
      exact hw (if_neg h))
def dT (f T : ℕ) : ℝ := (f : ℝ) * Real.log ((T : ℝ) - 1) / ((T : ℝ) - 2)
def modelFam (v : InfinitePlace K) (m f T p₁ t₁ Mw : ℕ) (hb : ℝ) : Fam (Fin Mw) m where
  K := K
  Wd := Fin ((T - 2) ^ f) → K
  κ := Fin ((T - 2) ^ f)
  κ₁ := Fin ((T - 1) ^ f - (T - 2) ^ f)
  V := fun _ => Fin ((T - 2) ^ f) → K
  ι := fun _ => Fin ((T - 2) ^ f)
  Vf := fun _ => Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f) → K
  ιf := fun _ => Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f)
  b' := Pi.basisFun K _
  X' := fun _ => 1
  cc := stdLat K _
  b := fun _ => Pi.basisFun K _
  X := fun _ _ => ((Real.exp (-(dT f T) / 2) : ℝ) : ℂ) • 1
  M := fun _ => stdLat K _
  N0 := fun _ => Formalism.HermitianLatticesTheory.idealSmul
    ((slopeLatticeData.idealPow (tau0 K p₁ t₁) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) (stdLat K _)
  bf := fun _ => Pi.basisFun K _
  Xf := fun _ _ => 1
  Mf := fun _ => stdLat K _
  σ := fun _ => tau0 K p₁ t₁
  τ := tau0 K p₁ t₁
  B := fun _ => LinearMap.id
  v := v
  Y := fun _ => 1
  Y' := 1
  Ball := fun _ => inclMat _ _
  γ := fun _ => 1
  Bf := fun _ => 1
  Vr := fun _ => inclMat _ _
  S := plOver K p₁ ∪ plOver K T
  gain := fun _ w => (tau0 K p₁ t₁ w : ℝ) / ramE w + 1
  Fj := fun _ _ => 1 / 2
  Ej := fun _ _ _ => 1 / 4
  iop := fun _ => 1
  T := fun _ => T
  h := fun _ => max (htMap (Pi.basisFun K (Fin ((T - 2) ^ f)))
    (fun _ => ((Real.exp (-(dT f T) / 2) : ℝ) : ℂ) • 1) (Pi.basisFun K (Fin ((T - 2) ^ f))) (fun _ => 1)
    LinearMap.id) hb
  lam := fun _ => 1
  Dstar := ((T - 1) ^ f : ℕ)
  η0 := 0
  η1 := 0
  e0 := 0
section Model
variable (v : InfinitePlace K) (m f T p₁ t₁ Mw : ℕ) (hb : ℝ)
end Model
section Model2
variable (v : InfinitePlace K) (m f T p₁ t₁ Mw : ℕ) (hb : ℝ)
end Model2
end ModelLemmas
section DataL
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}
end DataL
section DataT
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}
end DataT
section StdSlopes
open Formalism.LFunctionChainParameters.ProjectiveLineModels (stdLat)
section RankOne
variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
end RankOne
variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  (n : Type) [Fintype n] [DecidableEq n]
def standardSpanAlt (s : Finset n) : Submodule (𝓞 K) (n → K) :=
  Submodule.span (𝓞 K) ((Pi.basisFun K n) '' (s : Set n))
variable {K n}
variable (K n)
end StdSlopes
open Formalism.LFunctionChainParameters.ProjectiveLineModels (stdLat inclMat)
section Coll
variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
def bump (m : ℕ) (c : ℝ) (w : slopeLatticeData.FinPl K) : ℝ :=
  if prBelow w = 2 then c / (2 * (m : ℝ) * Real.log 2) else 0
def collFam (v : InfinitePlace K) (m f T Mw : ℕ) (hb gG gE : ℝ) : Fam (Fin Mw) m where
  K := K
  Wd := Fin ((T - 2) ^ f) → K
  κ := Fin ((T - 2) ^ f)
  κ₁ := Fin ((T - 1) ^ f - (T - 2) ^ f)
  V := fun _ => Fin ((T - 2) ^ f) → K
  ι := fun _ => Fin ((T - 2) ^ f)
  Vf := fun _ => Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f) → K
  ιf := fun _ => Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f)
  b' := Pi.basisFun K _
  X' := fun _ => 1
  cc := stdLat K _
  b := fun _ => Pi.basisFun K _
  X := fun _ _ => ((Real.exp (-(dT f T) / 2) : ℝ) : ℂ) • 1
  M := fun _ => stdLat K _
  N0 := fun _ => Formalism.HermitianLatticesTheory.idealSmul
    ((slopeLatticeData.idealPow (tau0 K 2 0) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) (stdLat K _)
  bf := fun _ => Pi.basisFun K _
  Xf := fun _ _ => 1
  Mf := fun _ => stdLat K _
  σ := fun _ => tau0 K 2 0
  τ := tau0 K 2 0
  B := fun _ => LinearMap.id
  v := v
  Y := fun _ => 1
  Y' := 1
  Ball := fun _ => inclMat _ _
  γ := fun _ => 1
  Bf := fun _ => 1
  Vr := fun _ => inclMat _ _
  S := plOver K 2 ∪ plOver K T
  gain := fun _ w => bump K m gG w
  Fj := fun _ w => bump K m (gE - gG) w
  Ej := fun _ _ w => bump K m gE w
  iop := fun _ => 0
  T := fun _ => T
  h := fun _ => max (htMap (Pi.basisFun K (Fin ((T - 2) ^ f)))
    (fun _ => ((Real.exp (-(dT f T) / 2) : ℝ) : ℂ) • 1) (Pi.basisFun K (Fin ((T - 2) ^ f))) (fun _ => 1)
    LinearMap.id) hb
  lam := fun _ => 0
  Dstar := ((T - 1) ^ f : ℕ)
  η0 := 0
  η1 := 0
  e0 := 0
variable (v : InfinitePlace K) (m f T Mw : ℕ) (hb gG gE : ℝ)
def hbT (f T : ℕ) : ℝ :=
  muDef (Pi.basisFun K (Fin ((T - 2) ^ f))) (fun _ => ((Real.exp (-(dT f T) / 2) : ℝ) : ℂ) • 1) (stdLat K _)
    - muMinDef (Pi.basisFun K (Fin ((T - 2) ^ f))) (fun _ => 1) (stdLat K _)
end Coll
section Lm
variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
def lm_S (Q : Finset ℕ) : Finset (slopeLatticeData.FinPl K) := Q.biUnion (plOver K)
def lmFam (v : InfinitePlace K) (m f T Mw : ℕ) (hb gE : ℝ) (Q : Finset ℕ) (gn : Fin m → ℕ → ℝ) : Fam (Fin Mw) m where
  K := K
  Wd := Fin ((T - 2) ^ f) → K
  κ := Fin ((T - 2) ^ f)
  κ₁ := Fin ((T - 1) ^ f - (T - 2) ^ f)
  V := fun _ => Fin ((T - 2) ^ f) → K
  ι := fun _ => Fin ((T - 2) ^ f)
  Vf := fun _ => Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f) → K
  ιf := fun _ => Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f)
  b' := Pi.basisFun K _
  X' := fun _ => 1
  cc := stdLat K _
  b := fun _ => Pi.basisFun K _
  X := fun _ _ => ((Real.exp (-(dT f T) / 2) : ℝ) : ℂ) • 1
  M := fun _ => stdLat K _
  N0 := fun _ => Formalism.HermitianLatticesTheory.idealSmul
    ((slopeLatticeData.idealPow (tau0 K 2 0) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) (stdLat K _)
  bf := fun _ => Pi.basisFun K _
  Xf := fun _ _ => 1
  Mf := fun _ => stdLat K _
  σ := fun _ => tau0 K 2 0
  τ := tau0 K 2 0
  B := fun _ => LinearMap.id
  v := v
  Y := fun _ => 1
  Y' := 1
  Ball := fun _ => inclMat _ _
  γ := fun _ => 1
  Bf := fun _ => 1
  Vr := fun _ => inclMat _ _
  S := lm_S K Q
  gain := fun j w => gn j (prBelow w)
  Fj := fun j w => bump K m gE w - gn j (prBelow w)
  Ej := fun _ _ w => bump K m gE w
  iop := fun _ => 0
  T := fun _ => T
  h := fun _ => max (htMap (Pi.basisFun K (Fin ((T - 2) ^ f)))
    (fun _ => ((Real.exp (-(dT f T) / 2) : ℝ) : ℂ) • 1) (Pi.basisFun K (Fin ((T - 2) ^ f))) (fun _ => 1)
    LinearMap.id) hb
  lam := fun _ => 0
  Dstar := ((T - 1) ^ f : ℕ)
  η0 := 0
  η1 := 0
  e0 := 0
variable (v : InfinitePlace K) (m f T Mw : ℕ) (hb gE : ℝ) (Q : Finset ℕ) (gn : Fin m → ℕ → ℝ)
end Lm
section LmLoss
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {m : ℕ}
def lm_gn (D : ArithData H) (N : ℕ) (TT : Finset H) (a : H → ℝ) (w : Fin m → E0 × H → ℝ) (Xpp : ℝ) (j : Fin m)
    (p : ℕ) : ℝ :=
  if p ∈ inertPs D N ∧ (p : ℝ) ≤ Xpp then
    ∑ t ∈ TT, DeficitSplitLemmas.askAt ((Finset.Icc 1 N).filter (fun i => ¬ InPhi (i • D.frob p))) (a t) p
      (fun i => w j (partner t (i • D.frob p)))
  else 0
def lm_Lp (D : ArithData H) (N : ℕ) (TT : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (P : PrimeWindowSizeBounds.Par)
    (u0 : H) : LossP H m where
  cl := fun p => if (p : ℝ) ≤ P.Xpp then DeficitSplitLemmas.PClass.served else DeficitSplitLemmas.PClass.high
  TTp := fun _ => TT
  gainP := lm_gn D N TT a (w u0) P.Xpp
  tauP := fun _ => 0
  lo := fun _ => 0
  fl := fun _ => 0
  L₁ := fun p => Real.logb p P.K₀ + 1
end LmLoss
section LmMain
variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v0 : InfinitePlace K)
  {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {m : ℕ}
  (D : ArithData H) (N : ℕ) (TT : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (P : PrimeWindowSizeBounds.Par) (T : H → ℕ)
  (Mw : ℕ) (gE : ℝ)
def lm_Q (u0 : H) : Finset ℕ := insert 2 (insert (T u0) (inertPs D N))
def lm_Fm : H → Fam (Fin Mw) m := fun u0 =>
  lmFam K v0 m (PhiSet (H := H)).card (T u0) Mw (hbT K (PhiSet (H := H)).card (T u0)) gE (lm_Q D N T u0)
    (lm_gn D N TT a (w u0) P.Xpp)
def lm_ld (u0 : H) : PrimeWindowSizeBounds.LD (PlAll (Ω := Unit) (W := fun _ _ => Fin Mw) (fun _ => lm_Fm K v0 D N TT a w P T Mw gE))
    (Fin m) H :=
  ldOf (Ω := Unit) (W := fun _ _ => Fin Mw) D N (fun _ => a) (fun _ => w) (fun _ => lm_Fm K v0 D N TT a w P T Mw gE)
    (fun u0 _ => lm_Lp D N TT a w P u0) u0 ()
variable {D N T}
variable (D N T)
end LmMain
section LmMain2
variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v0 : InfinitePlace K)
  {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {m : ℕ}
  (D : ArithData H) (N : ℕ) (TT : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (P : PrimeWindowSizeBounds.Par) (T : H → ℕ)
  (Mw : ℕ) (gE : ℝ)
end LmMain2
def evG (x ε lg : ℝ) : Glob :=
  ⟨x, ε, ModelText.kTx x ε, Real.log (aTx x ε) + x ^ (ε / 3), Real.pi, lg, 1 / 4, 6 * x ^ (-(1 : ℝ)), 0⟩
def evC : Consts := ⟨1, 1, 1, 1, 4, 1, 4, 1, 1, 1⟩
section EvModel
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end EvModel
end Formalism.LFunctionChainParameters.LChain2


