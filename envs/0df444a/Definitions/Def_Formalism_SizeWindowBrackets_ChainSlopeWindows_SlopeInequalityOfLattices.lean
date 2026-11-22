-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SlopeInequalityOfLattices
-- name    : Formalism_SizeWindowBrackets_ChainSlopeWindows_SlopeInequalityOfLattices
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:31:51.467313+00:00
-- url     : https://prove2.me/theorems/2e298dea-24f3-428b-bd99-cedf7eeb2acf
-- title:
--   Slope Inequality Of Lattices
-- statement:
--   Definitions and structural lemmas for Slope Inequality Of Lattices, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SlopeInequalityOfLattices.lean

import Definitions.Def_Formalism_SizeWindowBrackets_SlopeHypothesesRounded
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedSlopeExcessDecomposition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
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
section Real
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable {ι : Type} [DecidableEq ι]
variable (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ) (P : ∀ u0, W u0 → PData ι m)
end Real
section Prim
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable {ι : Type} [DecidableEq ι]
variable (D : Data U0 W Top m f) (C : Consts) (Xpp cT : ℝ) (Q : ∀ u0, W u0 → PPrim ι m)
end Prim
section Round
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable {ι : Type} [DecidableEq ι]
variable (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ) (P : ∀ u0, W u0 → PData ι m)
  (Ru : ∀ u0, W u0 → ℝ)
end Round
section F
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts)
end F
section SizeData₂
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  {Top : Type} [Fintype Top] {m f : ℕ}
variable {ι : Type} [DecidableEq ι]
variable (D : Data U0 W Top m f) (C : Consts) (Xpp cT : ℝ) (P : ∀ u0, W u0 → PData ι m)
  (Q : ∀ u0, W u0 → PPrim ι m)
end SizeData₂
namespace Model
def l0 : Fin 3 → ℝ := ![Real.log 2, Real.log 3, Real.log 211]
def gain0 : Fin 1 → Fin 3 → ℝ := fun _ => ![1, 0, 0]
def F0 : Fin 1 → Fin 3 → ℝ := fun _ _ => 1 / 2
def E0 : Fin 1 → Fin 3 → ℝ := fun _ _ => 1 / 4
def tau0 : Fin 3 → ℝ := ![1 / 2, 0, 0]
def io0 : Fin 3 → ℝ := ![1 / 10, 0, 0]
def len0 : Fin 3 → ℝ := ![3 / 5, 0, 1 / 20]
def sg0 : Fin 3 → ℝ := fun w => UnitWeightPartition.sgw Finset.univ gain0 F0 E0 w - ![1 / 10, 0, 0] w
def iop0 : ℕ → ℝ := fun p => if p = 2 then 1 / 10 else 0
def pr0 : Fin 3 → ℕ := ![2, 3, 211]
def SgV : ℝ := UnitWeightPartition.Sg Finset.univ l0 sg0 tau0
def BeV : ℝ := UnitWeightPartition.BeSum Finset.univ l0 1 len0 tau0
def RdV : ℝ := ∑ w : Fin 3, 2 * l0 w * (UnitWeightPartition.sgw Finset.univ gain0 F0 E0 w - sg0 w)
def IOV : ℝ := ∑ p ∈ ({2, 3, 211} : Finset ℕ), Real.log (p : ℝ) * iop0 p
def EeV : ℝ := 2 * ∑ w : Fin 3, l0 w * E0 0 w
def Q0 (μ0 μ1 : ℝ) : PPrim (Fin 3) 1 where
  S := Finset.univ
  ST := {2}
  l := l0
  gain := gain0
  F := F0
  E := E0
  tau := tau0
  io := io0
  len := len0
  sg' := sg0
  dM := 210 / 209
  du := 1
  muMu := μ0 - SgV + BeV
  muMaxMu := μ1 - SgV
  Rd := RdV
  lam := 1 / 20
  Pr := {2, 3, 211}
  pr := pr0
  iop := iop0
def sV (μ0 : ℝ) (h : Fin 20 → ℝ) : ℝ := wmean (fun _ : Fin 20 => (1 : ℝ)) (fun u => μ0 - h u)
def HHV (μ0 μ2 : ℝ) (h : Fin 20 → ℝ) : ℝ := |sV μ0 h - μ2| + 1
def muMV (μ0 : ℝ) : ℝ := (μ0 - SgV + BeV) + 1 * Real.log (211 - 1) / (211 - 2)
def FoV : ℝ := UnitWeightPartition.Fo Finset.univ Finset.univ l0 F0
def LaV (μ0 μ1 : ℝ) (h : Fin 20 → ℝ) : ℝ := |muMV μ0| + |μ1 - SgV| + 2 * ∑ u, |h u|
def NcV (μ0 : ℝ) (h : Fin 20 → ℝ) : ℝ := |μ0| + ∑ u, |h u| + |FoV| + 1 + Real.log 211
def D1 (μ0 μ1 μ2 : ℝ) (h : Fin 20 → ℝ) : Data Unit (fun _ => Fin 20) Unit 1 1 where
  x := HHV μ0 μ2 h
  ε := 0
  a := 1
  b := 1
  b' := 0
  k := 1
  L := Real.log 211
  La := LaV μ0 μ1 h
  B0 := |EeV|
  Nc := NcV μ0 h
  gam := 0
  LpL := 0
  v := Real.pi
  lg := 0
  logGam := 0
  aT := fun _ => 1
  w := fun _ _ _ => 1
  d := fun _ _ => 1
  T := fun _ _ => 211
  muN := fun _ _ => μ0
  muMaxN := fun _ _ => μ1
  h := fun _ => h
  muM := fun _ _ => muMV μ0
  muMaxM := fun _ _ => μ1 - SgV
  EeJ := fun _ _ _ => EeV
  muCC := fun _ => μ0
  muMinCC := fun _ => μ2
  Fo := fun _ => FoV
  Ga := fun _ => UnitWeightPartition.Ga Finset.univ Finset.univ l0 gain0 tau0
  Ta := fun _ => UnitWeightPartition.Ta Finset.univ l0 tau0
  ASK := fun _ => UnitWeightPartition.Ga Finset.univ Finset.univ l0 gain0 tau0
  IO := fun _ => IOV
  HH := fun _ => HHV μ0 μ2 h
  del := fun _ => 0
  η := fun _ => 5 * (1 / 20) + 3 * Real.sqrt 0
  e := fun _ => 2 * 0
  delBar := 0
  etaBar := 1 / 4
  eBar := 0
def C2 : Consts := ⟨1, 1, 1, 1, 1, 1, 4, |IOV|, 1, 1⟩
end Model
namespace Model
end Model
end Formalism.LFunctionChainParameters.LatticeToWeightTransfer


