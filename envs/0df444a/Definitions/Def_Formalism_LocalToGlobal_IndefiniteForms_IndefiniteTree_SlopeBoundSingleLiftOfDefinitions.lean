-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_SlopeBoundSingleLiftOfDefinitions
-- name    : Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_SlopeBoundSingleLiftOfDefinitions
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T11:28:46.949548+00:00
-- url     : https://prove2.me/theorems/ab0fdf34-a29f-4495-b0ab-3833e72d7ff5
-- title:
--   Slope Bound Single Lift Of Definitions
-- statement:
--   Definitions and structural lemmas for Slope Bound Single Lift Of Definitions, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/SlopeBoundSingleLiftOfDefinitions.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefExample
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_IndefiniteTreeX
import Definitions.Def_Formalism_MeanHeightDescent_DivisionInequalityWithCovolume
import Definitions.Def_Formalism_MeanHeightDescent_CovolumeFullAssemblyWeighted
import Definitions.Def_Formalism_ThetaSupremumBounds_LiftOperatorBoundOfFockJet
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_main
import Theorems.Thm_UpperTheory_Reformulated_B_SelectionLemmas_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module NumberField Formalism.HN
noncomputable section
namespace Formalism.L2.Indef.Tree
structure SlopeBoundParameters where

  Pl : Type

  fPl : Fintype Pl

  x : ℝ

  eps : ℝ

  rd : ℝ

  v : ℝ

  dN : ℕ

  dimNeZero : NeZero dN

  χ : DirichletCharacter ℂ dN

  Z : ℝ

  logOmK : ℝ

  logOm : ℝ

  f : ℝ

  m : ℝ

  k : ℝ

  S : ℝ

  η : ℝ

  R : ℝ

  PPp : ℝ

  PPpp : ℝ

  PP : ℝ

  PPT : ℝ

  Zpg : ℝ

  nV : ℝ

  Nr : ℝ

  g12 : ℝ
attribute [instance] SlopeBoundParameters.fPl SlopeBoundParameters.dimNeZero
def LcOf {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) : ℝ :=
  (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re
def leadingConstant {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) : ℝ :=
  (deriv (DirichletCharacter.LFunction χ) 0 / DirichletCharacter.LFunction χ 0).re
def eulerConstantTerm (n : ℕ) : ℝ :=
  (∑ q ∈ reducedForms (-(n : ℤ)), Real.log (4 * Real.pi * (formRoot (-(n : ℤ)) q).im *
    ‖ModularForm.eta (formRoot (-(n : ℤ)) q)‖ ^ 4)) / ((reducedForms (-(n : ℤ))).card : ℝ)
namespace SlopeBoundParameters
variable (P : SlopeBoundParameters)
def L : ℝ := P.x ^ P.eps
def b : ℝ := Real.exp P.L
def a : ℝ := P.x * P.b
def La : ℝ := Real.log (P.a * P.rd)
def lrd : ℝ := Real.log P.rd
def llx : ℝ := Real.log (Real.log P.x)
def dK : ℝ := (P.dN : ℝ)
def Lc : ℝ := LcOf P.χ
def L0 : ℝ := leadingConstant P.χ
def A1 : ℝ := eulerConstantTerm P.dN
def LL0 : ℝ := Real.log (P.b * P.rd) * P.llx + |P.Lc| + Real.log P.x
def B0 : ℝ := P.f * P.m * P.b * P.x ^ P.eps
end SlopeBoundParameters
structure SlopeBoundLiftData (K : Type) [Field K] [NumberField K] [StarRing K] (P : SlopeBoundParameters) where

  w : P.Pl → ℝ

  w0 : P.Pl → ℝ

  c1 : P.Pl → ℝ

  ua : P.Pl → ℝ

  kap : ℝ

  q' : ℕ

  pq : ℝ

  ι : Type

  fι : Fintype ι

  nι : Nonempty ι

  DY : ℝ

  A : ℝ

  cs : ℝ

  X : ℝ

  cc : ℝ

  E0 : ℝ

  Qcc : ℝ

  ρ : ℝ

  R1 : ℝ

  R2 : ℝ

  Bn : ℝ

  δ' : ℝ

  h : ι → ℝ

  sl : ι → ℝ

  δc : ι → ℝ

  dc : ι → ℝ

  degc : ι → ℝ

  PPf : ℝ

  mv : ℝ

  muU : ℝ

  nA : ℕ

  nB : ℕ

  nN : ℕ

  XA : InfinitePlace K → Matrix (Fin nA) (Fin nA) ℂ

  XB : InfinitePlace K → Matrix (Fin nB) (Fin nB) ℂ

  XN : InfinitePlace K → Matrix (Fin nN) (Fin nN) ℂ

  LA : Submodule (𝓞 K) (Fin nA → K)

  LB : Submodule (𝓞 K) (Fin nB → K)

  NN : Submodule (𝓞 K) (Fin nN → K)

  Mk : Submodule (𝓞 K) (Fin nN → K)

  φ : (Fin nA → K) →ₗ[K] (Fin nB → K)

  e : (Fin nN → K) →ₗ[K] (Fin nN → K)

  g : ℕ

  PPh : ℝ

  abelian₂ : ℝ

  δ : ℝ

  o' : ℝ

  n2 : ℝ
attribute [instance] SlopeBoundLiftData.fι SlopeBoundLiftData.nι
namespace SlopeBoundLiftData
variable {K : Type} [Field K] [NumberField K] [StarRing K] {P : SlopeBoundParameters} (F : SlopeBoundLiftData K P)
def T : ℝ := ((⌈P.PPT ^ 2 * F.DY ^ 2 * P.k / P.m⌉ : ℤ) : ℝ)
def ε : ℝ := 7 * F.DY ^ 2 / F.T + 3 / 2 * F.DY * F.ρ
def z : ℝ := 7 * (F.DY ^ 2 / F.T + F.DY * F.ρ)
def U : ℝ := ∑ τ, F.ua τ
def Q : ℝ := 2 * (P.PPp + 1 + P.lrd) * F.kap
def cfl (Cf : ℝ) : ℝ :=
  (∑ τ, F.w τ * F.c1 τ) - Cf * F.q' * Real.log P.rd * (∑ τ, F.w τ) - Cf * P.L
def e1 (Ca : ℝ) : ℝ := Ca * P.LL0 * F.E0
def e2 (Cb : ℝ) : ℝ := Cb * P.LL0 * F.E0 + F.T * F.Qcc
def main : ℝ := ∑ σ, F.pq * F.w0 σ * P.logOm
def muA : ℝ := muDef (Pi.basisFun K (Fin F.nA)) F.XA F.LA
def muN : ℝ := muDef (Pi.basisFun K (Fin F.nN)) F.XN F.NN
def good : Submodule (𝓞 K) (Fin F.nN → K) := F.NN ⊓ (LinearMap.range F.e).restrictScalars (𝓞 K)
def bad : Submodule (𝓞 K) (Fin F.nN → K) := F.NN ⊓ (LinearMap.ker F.e).restrictScalars (𝓞 K)
def muG : ℝ := muDef (Pi.basisFun K (Fin F.nN)) F.XN F.good
def mmax : ℝ := muMaxDef (Pi.basisFun K (Fin F.nN)) F.XN F.Mk
end SlopeBoundLiftData
def slopeBoundConstant (Ca Cb Cf Cc C1 Cm : ℝ) : ℝ := 64 * (Ca + Cb + C1 + 3 * Cf) + 8 * Cc + 14 + Cm
def LeafKL (P : SlopeBoundParameters) : Prop :=
  P.Z = Real.log (2 / Real.sqrt P.dK) + (P.A1 + Real.log Real.pi)
def LeafCN (P : SlopeBoundParameters) : Prop :=
  P.Z = Real.log (2 * Real.pi) + P.L0
def LeafFE (P : SlopeBoundParameters) : Prop :=
  P.L0 = -P.Lc - Real.log (P.dK / Real.pi) + Real.eulerMascheroniConstant + Real.log 2
def LeafDiff (P : SlopeBoundParameters) : Prop :=
  P.logOmK = P.A1
def LeafNorm (P : SlopeBoundParameters) : Prop :=
  P.logOm = P.logOmK - Real.log P.rd + Real.log (Real.sqrt P.dK)
section Leaves
variable {K : Type} [Field K] [NumberField K] [StarRing K] {P : SlopeBoundParameters}
def LeafDegFlat (Cc : ℝ) (F : SlopeBoundLiftData K P) : Prop :=
  ∀ τ, |F.c1 τ + F.pq * P.logOm / 2| ≤ Cc * F.q' * Real.log P.rd
def LeafExport (Cf : ℝ) (F : SlopeBoundLiftData K P) : Prop :=
  |(∑ τ, F.w τ * F.c1 τ) - Cf * F.q' * Real.log P.rd * (∑ τ, F.w τ)| ≤ P.PPp * F.kap
def LeafRoot (F : SlopeBoundLiftData K P) : Prop :=
  0 ≤ F.mv ∧ F.mv ≤ P.b / 50
def LeafFlat (Cf : ℝ) (F : SlopeBoundLiftData K P) : Prop :=
  F.muU - 2 * F.mv + 2 * F.cfl Cf ≤ F.muA
def LeafDeg (F : SlopeBoundLiftData K P) : Prop :=
  ∀ c, F.δ' ≤ F.δc c ∧ F.δc c ≤ F.δ' / (1 - F.ρ)
def LeafRho (F : SlopeBoundLiftData K P) : Prop :=
  0 ≤ F.ρ
def LeafShare (F : SlopeBoundLiftData K P) : Prop :=
  ∀ c, F.Bn * F.δc c ≤ F.dc c ∧ (1 - F.z) * F.dc c ≤ F.Bn * F.δc c
def LeafSmall (F : SlopeBoundLiftData K P) : Prop :=
  (∀ c, 0 ≤ F.h c + F.cs) ∧ 0 ≤ F.cc ∧ ∀ c, (1 - F.ρ) * max 0 (F.sl c + F.cs) ≤ F.h c + F.cs + F.cc
def LeafMeans (Ca Cb : ℝ) (F : SlopeBoundLiftData K P) : Prop :=
  0 ≤ F.X ∧ -F.X ≤ (∑ c, F.sl c) / (Fintype.card F.ι : ℝ) ∧
    F.T * F.X ≤ Ca * P.LL0 * (F.U + F.E0) ∧ F.T * F.cc ≤ Cb * P.LL0 * (F.U + F.E0) + F.T * F.Qcc
def LeafHS (F : SlopeBoundLiftData K P) : Prop :=
  0 < F.A ∧ 0 ≤ F.R1 ∧ 0 ≤ F.R2 ∧
    ∀ c, F.Bn * F.δc c * (F.T * F.h c - 3 * (F.DY + 1) * |F.h c| - F.A * Real.log (2 + |F.h c|) - F.R1 -
      2 * F.z * F.R2) ≤ F.degc c
def LeafSum (F : SlopeBoundLiftData K P) : Prop :=
  2 * ((∑ c, F.degc c) / (∑ c, F.dc c) - F.PPf) ≤ F.muU
def CrudeSizeBound (F : SlopeBoundLiftData K P) : Prop :=
  F.cs ≤ P.PPp * (F.kap / F.T + 1)
def LeafEps (F : SlopeBoundLiftData K P) : Prop :=
  F.ε * ((P.PPp + 1 + Real.log P.rd) * F.kap) ≤ P.b / 8
def LeafDescent (F : SlopeBoundLiftData K P) : Prop :=
  F.LA.FG ∧ F.LB.FG ∧ F.NN.FG ∧ F.LA ≠ ⊥ ∧ F.NN ≠ ⊥ ∧
    (∀ v, IsUnit (F.XA v).det) ∧ (∀ v, IsUnit (F.XB v).det) ∧
    Function.Injective F.φ ∧ F.LA.map (F.φ.restrictScalars (𝓞 K)) ≤ F.LB ∧
    htMap (Pi.basisFun K (Fin F.nA)) F.XA (Pi.basisFun K (Fin F.nB)) F.XB F.φ ≤ 2 * F.PPh ∧ 0 ≤ F.PPh ∧
    muDef (Pi.basisFun K (Fin F.nB)) F.XB F.LB = F.muN ∧
    muMinDef (Pi.basisFun K (Fin F.nB)) F.XB F.LB = muMinDef (Pi.basisFun K (Fin F.nN)) F.XN F.NN ∧
    rkK F.LA ≤ rkK F.LB ∧ (1 - F.ε) * (rkK F.LB : ℝ) ≤ (rkK F.LA : ℝ) ∧
    ∃ s : Set (Fin F.nN → K), s ⊆ (F.NN : Set (Fin F.nN → K)) ∧
      (∀ y ∈ s, ∀ v, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin F.nN)) F.XN v y ≤ Real.exp F.abelian₂) ∧
      (F.NN : Set (Fin F.nN → K)) ⊆ (Submodule.span K s : Set (Fin F.nN → K))
def LeafPh (F : SlopeBoundLiftData K P) : Prop :=
  F.PPh ≤ P.PPpp
def LeafGmin (F : SlopeBoundLiftData K P) : Prop :=
  F.abelian₂ ≤ P.PPp * F.kap
def LeafLam (F : SlopeBoundLiftData K P) : Prop :=
  F.mmax ≤ 2 * P.PPp * F.kap
def LeafCut (F : SlopeBoundLiftData K P) : Prop :=
  F.NN.FG ∧ F.Mk.FG ∧ F.NN ≠ ⊥ ∧ (∀ v, IsUnit (F.XN v).det) ∧ 1 ≤ F.g ∧ F.e ∘ₗ F.e = F.e ∧
    (∀ v y y', Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin F.nN)) F.XN v (F.e y) y' =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin F.nN)) F.XN v y (F.e y')) ∧
    (∀ y ∈ F.NN, ((F.g : ℕ) : K) • F.e y ∈ F.NN) ∧ F.NN ≤ F.Mk ∧
    Real.log F.g ≤ 20 * P.f * P.Nr ^ 2 * P.L
def LeafShareBad (F : SlopeBoundLiftData K P) : Prop :=
  0 ≤ F.δ ∧ F.δ ≤ Real.exp (-(P.x ^ (P.eps / 7)))
def LeafBadRows (F : SlopeBoundLiftData K P) : Prop :=
  (rkK F.bad : ℝ) ≤ 3 * F.δ * (rkK F.NN : ℝ)
def LeafMuN (F : SlopeBoundLiftData K P) : Prop :=
  |F.muN| ≤ 2 * P.PPp * F.kap
def LeafRecord {d : ℕ} (XWr : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (M : Submodule (𝓞 K) (Fin d → K))
    (F : SlopeBoundLiftData K P) : Prop :=
  F.muG - 2 * (F.o' + F.n2) ≤ muDef (Pi.basisFun K (Fin d)) XWr M ∧ F.o' ≤ P.PPpp
def LeafNote2 (Cn : ℝ) (F : SlopeBoundLiftData K P) : Prop :=
  0 ≤ F.n2 ∧ F.n2 ≤ Cn * P.f * P.Nr ^ 2 * Real.log (P.Nr * P.rd * P.g12)
def LeafDef (C1 Cf : ℝ) (F : SlopeBoundLiftData K P) : Prop :=
  (∑ τ, F.w τ * F.c1 τ) - C1 * P.LL0 * F.U - P.PP - (2 * P.Zpg * P.nV + Cf * P.L) ≤ F.muN / 2
def LeafMeasure (Cm : ℝ) {D d : ℕ} (XW XWr : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (M : Submodule (𝓞 K) (Fin d → K)) : SlopeBoundParameters → Prop := fun P =>
  (∀ v, IsUnit (XWr v).det) ∧ Formalism.DivisionValues.lcv XW M / (D : ℝ) ≤ Formalism.DivisionValues.lcv XWr M / (D : ℝ) + Cm * P.B0
end Leaves
def PageParams (P : SlopeBoundParameters) : Prop :=
  (∀ n : ℕ, P.χ n = ((jacobiSym n P.dN : ℤ) : ℂ)) ∧ P.χ.IsPrimitive ∧ P.χ.Odd ∧
  1 ≤ P.x ∧ 0 < P.eps ∧ 4 ≤ P.rd ∧ 2 * P.v = P.rd ∧ 0 < P.v ∧ Real.log P.rd ≤ P.L ∧ |P.Lc| ≤ P.L ∧
  Real.log P.x ≤ P.L ∧ 1 ≤ P.llx ∧ 3 ≤ P.x ^ (P.eps / 7) ∧
  (Fintype.card P.Pl : ℝ) ≤ P.f ∧ 1 ≤ P.m ∧ 1 ≤ P.f ∧ 1 ≤ P.k ∧ P.k * P.S ≤ P.b ∧ P.k * P.η ≤ P.b ∧
  0 ≤ P.S ∧ 0 ≤ P.R ∧ P.k * P.R ≤ P.b ∧
  20 * P.f * P.Nr ^ 2 * P.L ≤ P.PPp ∧ P.PPpp ≤ P.b / 8 ∧ P.PP + 2 * P.Zpg * P.nV ≤ P.b / 4
def FacParams {K : Type} [Field K] [NumberField K] [StarRing K] (Cf : ℝ) {P : SlopeBoundParameters} (F : SlopeBoundLiftData K P) : Prop :=
  (∀ τ, P.m * F.w τ / 2 ≤ F.ua τ ∧ F.ua τ ≤ 2 * (P.m * F.w τ + P.k * P.S + P.k * P.η)) ∧ 1 ≤ F.U ∧
  (∀ τ, 0 ≤ F.w τ ∧ F.w τ ≤ 2 * P.b) ∧ (∀ σ, |F.w σ - F.w0 σ| ≤ P.S + P.R) ∧ |F.pq - P.k| ≤ P.m ∧
  0 ≤ (F.q' : ℝ) ∧ (F.q' : ℝ) ≤ P.m ∧ 1 ≤ F.kap ∧ Cf * P.L ≤ F.kap ∧
  24 * F.δ * ((P.PPp + 1 + Real.log P.rd) * F.kap) ≤ P.b / 8 ∧ 2 * F.n2 ≤ P.b / 8
def CompParams {K : Type} [Field K] [NumberField K] [StarRing K] (Ca Cb : ℝ) {P : SlopeBoundParameters} (F : SlopeBoundLiftData K P) : Prop :=
  2 ≤ F.DY ∧ 20 * F.DY ≤ F.T ∧ F.DY ^ 2 / F.T ≤ 1 / 28 ∧ F.DY * F.ρ ≤ 1 / 28 ∧ 0 ≤ F.cs ∧ 0 < F.Bn ∧ 0 < F.δ' ∧
  F.cs * (6 * F.DY + 10 + F.T * (F.z + 2 * F.ρ)) + (F.A * Real.log (max F.A 1) + 4) + F.R1 + 2 * F.z * F.R2 +
    F.PPf + F.e1 Ca + F.e2 Cb ≤ P.b / 8
def ScaleTies {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} (Zs : IndefScale Bs)
    (P : SlopeBoundParameters) (F : Bs.J → SlopeBoundLiftData K P) : Prop :=
  Zs.x = P.x ∧ Zs.b = P.b ∧ (Fintype.card Bs.J : ℝ) = P.m ∧ (∀ j, Zs.l3m j = (F j).main) ∧
    Zs.l3u = P.B0 * P.llx ∧ Function.Injective (fun j => (F j).q') ∧
    ∀ j, ((F j).q' : ℝ) + 1 ≤ P.m ∧ (F j).pq = P.k + P.m - 1 - 2 * ((F j).q' : ℝ)
def PeriodIdentity (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n) : Prop :=
  ∃ Zv : ℝ, Zv = Real.log (2 / Real.sqrt (n : ℝ)) + (eulerConstantTerm n + Real.log Real.pi) ∧
    Zv = Real.log (2 * Real.pi) + leadingConstant χ ∧
    leadingConstant χ = -LcOf χ - Real.log ((n : ℝ) / Real.pi) + Real.eulerMascheroniConstant + Real.log 2
end Formalism.L2.Indef.Tree


