-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_SlopeHypothesesRounded
-- name    : Formalism_SizeWindowBrackets_SlopeHypothesesRounded
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:01:36.972797+00:00
-- url     : https://prove2.me/theorems/2f048480-746c-4590-933f-6813debb3938
-- title:
--   Slope Hypotheses Rounded
-- statement:
--   Definitions and structural lemmas for Slope Hypotheses Rounded, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/SlopeHypothesesRounded.lean

import Definitions.Def_Formalism_SizeWindowBrackets_ClaimGaFree
import Definitions.Def_Formalism_SizeWindowBrackets_QuotientSlopeBoundsWith
import Definitions.Def_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
namespace Formalism.LFunctionChainParameters.LatticeToWeightTransfer
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
structure PData (ι : Type) (m : ℕ) where

  S : Finset ι

  ST : Finset ι
  l : ι → ℝ
  gain : Fin m → ι → ℝ
  F : Fin m → ι → ℝ
  E : Fin m → ι → ℝ
  tau : ι → ℝ
  io : ι → ℝ
  len : ι → ℝ
  sg' : ι → ℝ
  dM : ℝ
  du : ℝ
  de : ℝ
  muMu : ℝ
  muMaxMu : ℝ
  PT : ℝ
  Rd : ℝ
  IOp : ℝ
  LT : ℝ
  RX : ℝ
namespace PData
variable {ι : Type} [DecidableEq ι] {m : ℕ} (p : PData ι m)
def Ga : ℝ := UnitWeightPartition.Ga p.S Finset.univ p.l p.gain p.tau
def Fo : ℝ := UnitWeightPartition.Fo p.S Finset.univ p.l p.F
def Ee : ℝ := UnitWeightPartition.Ee p.S Finset.univ p.l p.E
end PData
section Real
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable {ι : Type} [DecidableEq ι]
variable (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ) (P : ∀ u0, W u0 → PData ι m)
def SlopeHypotheses : Prop :=
  ∀ u0 (u : W u0),
    UnitWeightPartition.HypLow (P u0 u).S (P u0 u).ST Finset.univ (P u0 u).l (P u0 u).gain (P u0 u).F (P u0 u).E
      (P u0 u).tau (P u0 u).io (P u0 u).len (P u0 u).sg' (P u0 u).dM (P u0 u).du (P u0 u).de
      (P u0 u).muMu (D.muN u0 u) (P u0 u).PT (P u0 u).Rd ∧
    UnitWeightPartition.HypLow2 (P u0 u).S (P u0 u).l (P u0 u).tau (P u0 u).io (f : ℝ) (D.T u0 u) (P u0 u).de D.b
      (D.muM u0 u) (P u0 u).muMu (P u0 u).IOp (P u0 u).PT (P u0 u).LT (P u0 u).Rd (P u0 u).RX ∧
    UnitWeightPartition.HypHigh (P u0 u).S Finset.univ (P u0 u).l (P u0 u).gain (P u0 u).F (P u0 u).E
      (P u0 u).tau (P u0 u).sg' (D.muMaxM u0 u) (P u0 u).muMaxMu (D.muMaxN u0 u)
def PlaceSumIdentities : Prop :=
  ∀ u0 (u : W u0), D.Ga u0 = (P u0 u).Ga ∧ D.Fo u0 = (P u0 u).Fo ∧
    ∀ j, D.EeJ u0 u j = 2 * ∑ w ∈ (P u0 u).S, (P u0 u).l w * (P u0 u).E j w
def SlopeSizes : Prop :=
  4 ≤ C.cSl1 ∧ 0 ≤ (m : ℝ) * D.B0 ∧
  ∀ u0 (u : W u0), (P u0 u).IOp ≤ D.IO u0 ∧
    (P u0 u).LT ≤ C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * Real.log (D.T u0 u) ∧
    (P u0 u).RX ≤ C.cSl1 * Xpp
def QuotientSlopeBoundsOfPlaceSums : Prop :=
  SlopeHypotheses D P → PlaceSumIdentities D P → SlopeSizes D C Xpp P → QuotientSlopeBoundsWith D C Xpp
def BridgeEe : Prop :=
  PlaceSumIdentities D P → ∀ u0 (u : W u0), D.Ee u0 u = (P u0 u).Ee
def WordsSharePlaces : Prop :=
  ∀ u0 (u u' : W u0), (P u0 u).S = (P u0 u').S ∧ (P u0 u).l = (P u0 u').l ∧
    (∀ j, ∀ w ∈ (P u0 u).S, (P u0 u).F j w = (P u0 u').F j w) ∧
    ∃ Z : Finset ι,
      (∀ w ∈ (P u0 u).S, w ∉ Z →
        (∀ j, (P u0 u).gain j w = (P u0 u').gain j w) ∧ (P u0 u).tau w = (P u0 u').tau w) ∧
      (∀ w ∈ (P u0 u).S, w ∈ Z →
        (∀ j, (P u0 u).gain j w = 0 ∧ (P u0 u').gain j w = 0) ∧
          (P u0 u).tau w = 0 ∧ (P u0 u').tau w = 0)
def GaFoFree : Prop :=
  WordsSharePlaces P → ∀ u0 (u u' : W u0), (P u0 u).Ga = (P u0 u').Ga ∧ (P u0 u).Fo = (P u0 u').Fo
def IdentOne : Prop :=
  (∀ u0, ∃ u : W u0, D.Ga u0 = (P u0 u).Ga ∧ D.Fo u0 = (P u0 u).Fo) ∧
  ∀ u0 (u : W u0) j, D.EeJ u0 u j = 2 * ∑ w ∈ (P u0 u).S, (P u0 u).l w * (P u0 u).E j w
def QuotientSlopeBoundsOfSharedPlaces : Prop :=
  SlopeHypotheses D P → WordsSharePlaces P → IdentOne D P → SlopeSizes D C Xpp P → QuotientSlopeBoundsWith D C Xpp
end Real
structure PPrim (ι : Type) (m : ℕ) where
  S : Finset ι
  ST : Finset ι
  l : ι → ℝ
  gain : Fin m → ι → ℝ
  F : Fin m → ι → ℝ
  E : Fin m → ι → ℝ
  tau : ι → ℝ
  io : ι → ℝ
  len : ι → ℝ
  sg' : ι → ℝ
  dM : ℝ
  du : ℝ
  muMu : ℝ
  muMaxMu : ℝ
  Rd : ℝ
  lam : ℝ
  Pr : Finset ℕ
  pr : ι → ℕ
  iop : ℕ → ℝ
def PPrim.toPData {ι : Type} {m : ℕ} (q : PPrim ι m) (T : ℝ) : PData ι m where
  S := q.S
  ST := q.ST
  l := q.l
  gain := q.gain
  F := q.F
  E := q.E
  tau := q.tau
  io := q.io
  len := q.len
  sg' := q.sg'
  dM := q.dM
  du := q.du
  de := 1 - q.du / q.dM
  muMu := q.muMu
  muMaxMu := q.muMaxMu
  PT := 4 * q.lam * Real.log T
  Rd := q.Rd
  IOp := ∑ p ∈ q.Pr, Real.log (p : ℝ) * q.iop p
  LT := 4 * q.lam * Real.log T
  RX := q.Rd
section Prim
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable {ι : Type} [DecidableEq ι]
variable (D : Data U0 W Top m f) (C : Consts) (Xpp cT : ℝ) (Q : ∀ u0, W u0 → PPrim ι m)
def toP : ∀ u0, W u0 → PData ι m := fun u0 u => (Q u0 u).toPData (D.T u0 u)
def HypPrim : Prop :=
  ∀ u0 (u : W u0),
    (∀ w ∈ (Q u0 u).S, 0 ≤ (Q u0 u).l w) ∧ 0 < (Q u0 u).dM ∧ 2 < D.T u0 u ∧
    4 * (f : ℝ) ≤ D.T u0 u ∧
    (Q u0 u).du = (Q u0 u).dM * (1 - 1 / (D.T u0 u - 1)) ^ f ∧ (Q u0 u).ST ⊆ (Q u0 u).S ∧
    (∀ w ∈ (Q u0 u).ST, (Q u0 u).tau w = 0) ∧ (∀ w ∈ (Q u0 u).S, 0 ≤ (Q u0 u).tau w) ∧
    (∀ w ∈ (Q u0 u).S, 0 ≤ (Q u0 u).io w) ∧
    (∀ w ∈ (Q u0 u).S \ (Q u0 u).ST,
      (Q u0 u).len w ≤ (Q u0 u).dM * ((Q u0 u).tau w + (Q u0 u).io w)) ∧
    (∀ w ∈ (Q u0 u).ST, (Q u0 u).len w ≤ (Q u0 u).dM * (Q u0 u).lam) ∧ 0 ≤ (Q u0 u).lam ∧
    ∑ w ∈ (Q u0 u).ST, (Q u0 u).l w = Real.log (D.T u0 u) ∧
    (∀ w ∈ (Q u0 u).S,
      (Q u0 u).sg' w ≤ UnitWeightPartition.sgw Finset.univ (Q u0 u).gain (Q u0 u).F (Q u0 u).E w) ∧
    ∑ w ∈ (Q u0 u).S, 2 * (Q u0 u).l w *
      (UnitWeightPartition.sgw Finset.univ (Q u0 u).gain (Q u0 u).F (Q u0 u).E w - (Q u0 u).sg' w) ≤ (Q u0 u).Rd ∧
    D.muN u0 u = (Q u0 u).muMu + UnitWeightPartition.Sg (Q u0 u).S (Q u0 u).l (Q u0 u).sg' (Q u0 u).tau
      - UnitWeightPartition.BeSum (Q u0 u).S (Q u0 u).l (Q u0 u).du (Q u0 u).len (Q u0 u).tau ∧
    D.muMaxN u0 u ≤ (Q u0 u).muMaxMu + UnitWeightPartition.Sg (Q u0 u).S (Q u0 u).l (Q u0 u).sg' (Q u0 u).tau ∧
    (Q u0 u).muMu = D.muM u0 u - (f : ℝ) * Real.log (D.T u0 u - 1) / (D.T u0 u - 2) ∧
    (Q u0 u).muMaxMu ≤ D.muMaxM u0 u ∧
    UnitWeightPartition.Ta (Q u0 u).S (Q u0 u).l (Q u0 u).tau ≤ D.b ^ 2 ∧
    4 * (f : ℝ) / D.T u0 u * D.b ^ 2
      + (f : ℝ) * Real.log (D.T u0 u - 1) / (D.T u0 u - 2) ≤ 1 ∧
    (∀ w ∈ (Q u0 u).S, (Q u0 u).pr w ∈ (Q u0 u).Pr) ∧
    (∀ p ∈ (Q u0 u).Pr, ∑ w ∈ (Q u0 u).S.filter (fun w => (Q u0 u).pr w = p), (Q u0 u).l w
      = Real.log (p : ℝ)) ∧
    (∀ w ∈ (Q u0 u).S, (Q u0 u).io w = (Q u0 u).iop ((Q u0 u).pr w))
def SizesPrim : Prop :=
  4 ≤ C.cSl1 ∧ 4 * cT ≤ C.cSl1 ∧ 0 ≤ (m : ℝ) * D.B0 ∧ 0 ≤ D.a / D.k + D.b' ∧
  ∀ u0 (u : W u0), ∑ p ∈ (Q u0 u).Pr, Real.log (p : ℝ) * (Q u0 u).iop p ≤ D.IO u0 ∧
    (Q u0 u).lam ≤ cT * D.nT * (m : ℝ) * (D.a / D.k + D.b') ∧ (Q u0 u).Rd ≤ C.cSl1 * Xpp
def BridgePrim : Prop :=
  HypPrim D Q → SlopeHypotheses D (toP D Q)
def BridgePrimSizes : Prop :=
  (∀ u0 (u : W u0), 2 < D.T u0 u) → SizesPrim D C Xpp cT Q → SlopeSizes D C Xpp (toP D Q)
def QuotientSlopeBoundsOfPrimitiveData : Prop :=
  HypPrim D Q → PlaceSumIdentities D (toP D Q) → SizesPrim D C Xpp cT Q → QuotientSlopeBoundsWith D C Xpp
end Prim
section Round
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable {ι : Type} [DecidableEq ι]
variable (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ) (P : ∀ u0, W u0 → PData ι m)
  (Ru : ∀ u0, W u0 → ℝ)
def SlopeHypothesesRounded : Prop :=
  ∀ u0 (u : W u0),
    UnitWeightPartition.HypLow (P u0 u).S (P u0 u).ST Finset.univ (P u0 u).l (P u0 u).gain (P u0 u).F (P u0 u).E
      (P u0 u).tau (P u0 u).io (P u0 u).len (P u0 u).sg' (P u0 u).dM (P u0 u).du (P u0 u).de
      (P u0 u).muMu (D.muN u0 u) (P u0 u).PT (P u0 u).Rd ∧
    UnitWeightPartition.HypLow2 (P u0 u).S (P u0 u).l (P u0 u).tau (P u0 u).io (f : ℝ) (D.T u0 u) (P u0 u).de D.b
      (D.muM u0 u) (P u0 u).muMu (P u0 u).IOp (P u0 u).PT (P u0 u).LT (P u0 u).Rd (P u0 u).RX ∧
    (∑ w ∈ (P u0 u).S, 2 * (P u0 u).l w *
        ((P u0 u).sg' w - UnitWeightPartition.sgw Finset.univ (P u0 u).gain (P u0 u).F (P u0 u).E w) ≤ Ru u0 u ∧
      D.muMaxN u0 u ≤ (P u0 u).muMaxMu + UnitWeightPartition.Sg (P u0 u).S (P u0 u).l (P u0 u).sg' (P u0 u).tau ∧
      (P u0 u).muMaxMu ≤ D.muMaxM u0 u)
def SlopeLemmaRounded : Prop :=
  SlopeHypothesesRounded D P Ru → PlaceSumIdentities D P → SlopeSizes D C Xpp P →
    (∀ u0 (u : W u0), Ru u0 u ≤ C.cSl1 * (m : ℝ) * D.B0) → QuotientSlopeBoundsWith D C Xpp
end Round
def RoundUpNeedsTerm : Prop :=
  ∃ (l sg' tau : Unit → ℝ) (gain F E : Fin 1 → Unit → ℝ) (muMaxM muMaxMu muMaxN : ℝ),
    (∀ w, 0 ≤ l w) ∧
    (∀ w, UnitWeightPartition.sgw Finset.univ gain F E w ≤ sg' w ∧ sg' w < UnitWeightPartition.sgw Finset.univ gain F E w + 1) ∧
    muMaxN ≤ muMaxMu + UnitWeightPartition.Sg Finset.univ l sg' tau ∧ muMaxMu ≤ muMaxM ∧
    ¬ (muMaxN ≤ muMaxM + UnitWeightPartition.Ga Finset.univ Finset.univ l gain tau
      + UnitWeightPartition.Fo Finset.univ Finset.univ l F - UnitWeightPartition.Ee Finset.univ Finset.univ l E)
def LatticeSlopeComparison : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (σ τ : slopeLatticeData.FinPl K →₀ ℤ) (M N : Submodule (𝓞 K) V) (β : slopeLatticeData.FinPl K → ℝ), M.FG → M ≠ ⊥ →
      N ≤ Formalism.HermitianLatticesTheory.idealSmul ((slopeLatticeData.idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
        Submodule (𝓞 K) K) M →
      rkK N = rkK M →
      (∀ w : slopeLatticeData.FinPl K, ((slopeLatticeData.lenAt w (Formalism.HermitianLatticesTheory.idealSmul
        ((slopeLatticeData.idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) M)
          N).toNat : ℝ) = (rkK M : ℝ) * β w) →
    ∀ (S : Finset (slopeLatticeData.FinPl K)) (eR l sg' tau len : slopeLatticeData.FinPl K → ℝ),
      (∀ w, w ∉ S → σ w = 0 ∧ τ w = 0 ∧ β w = 0) → (∀ w ∈ S, 0 < eR w) →
      (∀ w ∈ S, l w = slopeLatticeData.ell w * eR w) → (∀ w ∈ S, sg' w = (σ w : ℝ) / eR w) →
      (∀ w ∈ S, tau w = (τ w : ℝ) / eR w) →
      (∀ w ∈ S, len w = (rkK M : ℝ) * (β w + (τ w : ℝ)) / eR w) →
      muMaxDef b X (slopeLatticeData.modLat σ N) ≤ muMaxDef b X M + UnitWeightPartition.Sg S l sg' tau ∧
      muDef b X (slopeLatticeData.modLat σ N) = muDef b X M + UnitWeightPartition.Sg S l sg' tau
        - UnitWeightPartition.BeSum S l (rkK M : ℝ) len tau
section F
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts)
def SideF (u0 : U0) : Prop :=
  0 ≤ D.del u0 ∧ D.del u0 < 1 ∧ 0 ≤ D.η u0 ∧ 0 ≤ D.e u0 ∧ D.e u0 ≤ 1 / 4 ∧
    D.s u0 - D.muMinCC u0 ≤ D.HH u0 ∧ 0 < D.HH u0
def ConclFAt (u0 : U0) : Prop :=
  PhiMonotonicityLemmas.ConclF (D.s u0) (D.muCC u0) (Real.log (Fintype.card (W u0) : ℝ)) (D.del u0) (D.uF u0)
    (D.HH u0) (D.η u0) (D.e u0)
def BridgeSU : Prop :=
  ∀ u0, D.s u0 = WeightedMeanLemmas.sF (D.d u0) (D.muN u0) (D.h u0) ∧
    D.uF u0 = WeightedMeanLemmas.uF (D.d u0) (D.muMaxN u0) (D.muN u0) (D.h u0)
def BridgeF : Prop :=
  D.SlopeIneq ↔ ∀ u0, SideF D u0 → ConclFAt D u0
def LatIdent (u0 : U0) {K Wd κ : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup Wd] [Module K Wd] [Module (𝓞 K) Wd] [IsScalarTower (𝓞 K) K Wd]
    [Fintype κ] [DecidableEq κ]
    {V ι : W u0 → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K Wd) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) Wd)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) : Prop :=
  (∀ u, D.d u0 u = (Fintype.card (ι u) : ℝ)) ∧
  (∀ u, D.muN u0 u = muDef (b u) (X u) (N u)) ∧
  (∀ u, D.muMaxN u0 u = muMaxDef (b u) (X u) (N u)) ∧
  D.muCC u0 = muDef b' X' cc ∧ D.muMinCC u0 = muMinDef b' X' cc
def BridgeFLat : Prop :=
  ∀ (u0 : U0) (K Wd κ κ₁ : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup Wd] [Module K Wd] [Module (𝓞 K) Wd] [IsScalarTower (𝓞 K) K Wd]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁]
    (V ι : W u0 → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K Wd) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) Wd)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] Wd)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : W u0 → ℝ),
    LatIdent D u0 b' X' cc b X N →
    MatrixLatticeEstimates.LatGeom b' X' cc b X N B (D.h u0) v Y Y' Ball (D.del u0) →
    (∀ i, 0 < γ i) → MatrixLatticeEstimates.FrameDeviationLinear Ball γ (D.e u0) → MatrixLatticeEstimates.FrameTraceRatioLinear Ball γ (D.η u0) →
    SideF D u0 → ConclFAt D u0
def BridgeFA : Prop :=
  ∀ (u0 : U0) (K Wd κ κ₁ : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup Wd] [Module K Wd] [Module (𝓞 K) Wd] [IsScalarTower (𝓞 K) K Wd]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁]
    (V ι : W u0 → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K Wd) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) Wd)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] Wd)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : W u0 → ℝ) (Dstar sg η0 η1 e0 : ℝ),
    LatIdent D u0 b' X' cc b X N →
    MatrixLatticeEstimates.LatGeom b' X' cc b X N B (D.h u0) v Y Y' Ball (D.del u0) →
    (∀ i, 0 < γ i) → 0 < Dstar → 0 < sg → sg ≤ 1 / 4 → Dstar / sg ≤ MatrixLatticeEstimates.RsG ι →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → Real.sqrt e0 ≤ sg / 2 →
    MatrixLatticeEstimates.InputSG Ball γ Dstar η0 η1 e0 → D.η u0 = 5 * sg → D.e u0 = e0 →
    SideF D u0 → ConclFAt D u0
def HypS (u0 : U0) {K Wd κ κ₁ : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup Wd] [Module K Wd] [Module (𝓞 K) Wd] [IsScalarTower (𝓞 K) K Wd]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁]
    {V ι : W u0 → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K Wd) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) Wd)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] Wd)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : W u0 → ℝ)
    {ιf : W u0 → Type} [∀ i, Fintype (ιf i)] [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (Dstar sg η0 η1 e0 de : ℝ) : Prop :=
  LatIdent D u0 b' X' cc b X N ∧
  MatrixLatticeEstimates.LatGeom b' X' cc b X N B (D.h u0) v Y Y' Ball (D.del u0) ∧
  (∀ i, 0 < γ i) ∧ (∀ i, Ball i = Bf i * Vr i) ∧ (∀ i, (Vr i)ᴴ * Vr i = 1) ∧
  0 < Dstar ∧ 0 < sg ∧ sg ≤ 1 / 20 ∧ Dstar / sg ≤ MatrixLatticeEstimates.RsG ιf ∧
  -1 ≤ η0 ∧ η0 ≤ sg / 2 ∧ η1 ≤ sg / 2 ∧ 0 ≤ e0 ∧ Real.sqrt e0 ≤ sg / 2 ∧
  0 ≤ de ∧ de ≤ 1 / 4 ∧
  ∑ i, ((Fintype.card (ιf i) : ℝ) - (Fintype.card (ι i) : ℝ)) ≤ de * MatrixLatticeEstimates.RsG ιf ∧
  MatrixLatticeEstimates.InputSG Bf γ Dstar η0 η1 e0 ∧
  D.η u0 = 5 * sg + 3 * Real.sqrt de ∧ D.e u0 = 2 * e0
def BridgeFS : Prop :=
  ∀ (u0 : U0) (K Wd κ κ₁ : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup Wd] [Module K Wd] [Module (𝓞 K) Wd] [IsScalarTower (𝓞 K) K Wd]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁]
    (V ι : W u0 → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K Wd) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) Wd)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] Wd)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : W u0 → ℝ)
    (ιf : W u0 → Type) [∀ i, Fintype (ιf i)] [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (Dstar sg η0 η1 e0 de : ℝ),
    HypS D u0 b' X' cc b X N B v Y Y' Ball γ Bf Vr Dstar sg η0 η1 e0 de →
    SideF D u0 → ConclFAt D u0
def LatForS (u0 : U0) : Prop :=
  ∃ (K Wd κ κ₁ : Type) (_ : Field K) (_ : NumberField K) (_ : StarRing K)
    (_ : IsTotallyComplex K)
    (_ : AddCommGroup Wd) (_ : Module K Wd) (_ : Module (𝓞 K) Wd) (_ : IsScalarTower (𝓞 K) K Wd)
    (_ : Fintype κ) (_ : DecidableEq κ) (_ : Fintype κ₁) (_ : DecidableEq κ₁)
    (V ι : W u0 → Type) (_ : ∀ i, AddCommGroup (V i)) (_ : ∀ i, Module K (V i))
    (_ : ∀ i, Module (𝓞 K) (V i))
    (_ : ∀ i, IsScalarTower (𝓞 K) K (V i)) (_ : ∀ i, Fintype (ι i)) (_ : ∀ i, DecidableEq (ι i))
    (b' : Basis κ K Wd) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) Wd)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] Wd)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : W u0 → ℝ)
    (ιf : W u0 → Type) (_ : ∀ i, Fintype (ιf i)) (_ : ∀ i, DecidableEq (ιf i))
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (Dstar sg η0 η1 e0 de : ℝ),
    HypS D u0 b' X' cc b X N B v Y Y' Ball γ Bf Vr Dstar sg η0 η1 e0 de
def SlopeIneqOfLat : Prop :=
  (∀ u0, LatForS D u0) → D.SlopeIneq
end F
section SizeData₂
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable {ι : Type} [DecidableEq ι]
variable (D : Data U0 W Top m f) (C : Consts) (Xpp cT : ℝ) (P : ∀ u0, W u0 → PData ι m)
  (Q : ∀ u0, W u0 → PPrim ι m)
def MainTermBoundOfSlopeInequality : Prop :=
  D.HidaSetting C → D.DIV C → EComp5 D C → D.HComp C → Count5 D C → D.Slopes C →
    SlopeHypotheses D P → PlaceSumIdentities D P → SlopeSizes D C Xpp P →
    LossBounds D C → D.SlopeIneq → D.HHBound C → D.FParams →
    ∀ u0, D.ASK u0 ≤ D.Main u0 + ErrX5at D C Xpp u0
def MainTermBoundOfSlopeInequalityPrim : Prop :=
  D.HidaSetting C → D.DIV C → EComp5 D C → D.HComp C → Count5 D C → D.Slopes C →
    HypPrim D Q → PlaceSumIdentities D (toP D Q) → SizesPrim D C Xpp cT Q →
    LossBounds D C → D.SlopeIneq → D.HHBound C → D.FParams →
    ∀ u0, D.ASK u0 ≤ D.Main u0 + ErrX5at D C Xpp u0
def MainTermBoundOfLattices : Prop :=
  D.HidaSetting C → D.DIV C → EComp5 D C → D.HComp C → Count5 D C → D.Slopes C →
    SlopeHypotheses D P → PlaceSumIdentities D P → SlopeSizes D C Xpp P →
    LossBounds D C → (∀ u0, LatForS D u0) → D.HHBound C → D.FParams →
    ∀ u0, D.ASK u0 ≤ D.Main u0 + ErrX5at D C Xpp u0
def MainTermBoundOfLatticesPrim : Prop :=
  D.HidaSetting C → D.DIV C → EComp5 D C → D.HComp C → Count5 D C → D.Slopes C →
    HypPrim D Q → PlaceSumIdentities D (toP D Q) → SizesPrim D C Xpp cT Q →
    LossBounds D C → (∀ u0, LatForS D u0) → D.HHBound C → D.FParams →
    ∀ u0, D.ASK u0 ≤ D.Main u0 + ErrX5at D C Xpp u0
end SizeData₂
def MainTermBoundOfLatticesPrimModel : Prop :=
  ∃ (D : Data Unit (fun _ => Fin 20) Unit 1 1) (C : Consts) (Xpp cT : ℝ)
    (Q : ∀ _ : Unit, Fin 20 → PPrim (Fin 3) 1),
    D.HidaSetting C ∧ D.DIV C ∧ EComp5 D C ∧ D.HComp C ∧ Count5 D C ∧ D.Slopes C ∧
    HypPrim D Q ∧ PlaceSumIdentities D (toP D Q) ∧ SizesPrim D C Xpp cT Q ∧
    LossBounds D C ∧ (∀ u0, LatForS D u0) ∧ D.HHBound C ∧ D.FParams ∧
    WordsSharePlaces (toP D Q) ∧ (∀ u0 u, D.d u0 u = (Q u0 u).du) ∧
    (∀ u0 u, ∃ w ∈ (Q u0 u).S, 0 < (Q u0 u).l w ∧ 0 < (Q u0 u).io w ∧ 0 < (Q u0 u).tau w ∧
      (Q u0 u).sg' w < UnitWeightPartition.sgw Finset.univ (Q u0 u).gain (Q u0 u).F (Q u0 u).E w ∧
      (Q u0 u).du * (Q u0 u).tau w < (Q u0 u).len w) ∧
    (∀ u0 u, ∃ w ∈ (Q u0 u).ST, 0 < (Q u0 u).l w ∧ 0 < (Q u0 u).len w)
end Formalism.LFunctionChainParameters.LatticeToWeightTransfer


