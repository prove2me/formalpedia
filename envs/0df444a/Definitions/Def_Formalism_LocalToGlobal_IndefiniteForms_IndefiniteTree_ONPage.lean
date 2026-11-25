-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONPage
-- name    : Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONPage
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T17:24:54.184476+00:00
-- url     : https://prove2.me/theorems/dd304562-6ca4-5f3f-afc6-c99d81123126
-- title:
--   ONPage
-- statement:
--   Definitions and structural lemmas for ONPage, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONPage.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
namespace Formalism.L2.Indef.Tree
namespace OnPage
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}
def nH (O : OnObj S P c) : ℝ := O.f / 2
def Xp (O : OnObj S P c) : ℝ := Real.exp (O.x ^ (O.eps / 3))
def aa (O : OnObj S P c) : ℝ := O.x * O.b
def wpp (O : OnObj S P c) : ℝ := aa O / Xp O / (O.x * nH O)
def dl2 (O : OnObj S P c) : ℝ := (O.T2 : ℝ) / nH O
def x0 (ε : ℝ) : ℝ := (2 / ε) ^ (2 / ε)
def ConstC (c : OnConst) : Prop := 1 ≤ c.C
def ConstBad (c : OnConst) : Prop := 14 ≤ c.Cb1 ∧ 66 * c.C + 4 ≤ c.Cb2
def XLarge (O : OnObj S P c) (C2 : ℝ) : Prop := 3 ≤ O.x ∧ 3 * c.C * C2 ≤ O.x ∧ x0 O.eps ≤ O.x
def ExponentSmallBound (O : OnObj S P c) : Prop := 0 < O.eps ∧ O.eps < 1 / 52
def HalfDegreeAtLeastFour (O : OnObj S P c) : Prop := 4 ≤ nH O
def PrimeCongruenceConditions (O : OnObj S P c) : Prop := O.q1.Prime ∧ O.dd.Prime ∧ O.q1 % 8 = 3 ∧ O.dd % 16 = 7
def DegreeAtLeastFortyFour (O : OnObj S P c) : Prop := 44 ≤ O.m ∧ 0 ≤ nH O
def DimensionExceedsDegreeByThree (O : OnObj S P c) : Prop := O.m + 3 ≤ O.k
def RankAndLengthLowerBounds (O : OnObj S P c) : Prop := 9 ≤ O.rr ∧ 10 ≤ O.L
def LeafSZ1 (O : OnObj S P c) : Prop := 0 ≤ O.T ∧ O.T ≤ O.b
def LeafW (O : OnObj S P c) : Prop :=
  ∃ nf : ℕ, (nf : ℝ) = O.f ∧ ∀ j, ∃ ws : Fin nf → ℝ, O.wt j = ∑ τ, ws τ ∧ ∀ τ, 0 ≤ ws τ ∧ ws τ ≤ 2 * O.b
def SupportGapBounds (O : OnObj S P c) : Prop := O.k * O.Sc ≤ wpp O ∧ Xp O * (O.Sc + O.eta) ≤ O.b
def EtaPowerBound (O : OnObj S P c) : Prop := O.eta * O.b ^ ((4 : ℝ) / 5) ≤ wpp O
def LeafSign (O : OnObj S P c) : Prop := 0 ≤ O.Sc ∧ 0 ≤ O.eta
def NodeCountBound (O : OnObj S P c) : Prop := ∃ t : ℝ, 0 ≤ t ∧ O.k + O.m * (t + 1) ≤ Xp O
def LogPrimeProductBound (O : OnObj S P c) : Prop := Real.log ((O.q1 * O.dd : ℕ) : ℝ) ≤ O.m
def ProductWithRatioBound (O : OnObj S P c) : Prop := O.k * O.bp ≤ O.b
def ConductorCongruentPrimePair (O : OnObj S P c) : Prop :=
  O.g1.Prime ∧ O.g2.Prime ∧ (O.g1 : ℝ) ≤ O.b ^ 9 ∧ (O.g2 : ℝ) ≤ O.b ^ 9 ∧ O.g1 ≠ O.g2 ∧
    ∃ M : ℕ, (O.q1 ∣ M ∧ O.dd ∣ M ∧ ∀ p ∈ O.sm, 1 < p ∧ p ∣ M) ∧ O.g1 % M = 1 ∧ O.g2 % M = 1
def SquaredTimeBound (O : OnObj S P c) : Prop := ∃ PP : ℝ, 1 ≤ PP ∧ PP ^ 3 * O.T ^ 2 ≤ O.b
def PowerTwelveBound (O : OnObj S P c) : Prop := (O.f * O.rr * O.L) ^ 12 ≤ O.b
def DiscriminantDegreeBound (O : OnObj S P c) : Prop := 0 ≤ O.DF ∧ ∃ nW : ℝ, 40 ≤ nW ∧ 2 * Real.pi * nW ≤ O.DF ^ 2
def ProductLowerBoundTwist (O : OnObj S P c) : Prop :=
  ∃ PP D : ℝ, 1 ≤ PP ∧ 1 ≤ D ∧ PP ^ 4 * D ^ 3 * O.k * O.f * O.x ≤ O.T * O.m * dl2 O
def TwistDensityBounds (O : OnObj S P c) : Prop := O.x ^ (-O.eps) ≤ dl2 O ∧ ∃ Lw : ℝ, 22 ≤ Lw ∧ dl2 O ≤ 1 / (4 * Lw)
def TimeDiscriminantBound (O : OnObj S P c) (C2 : ℝ) : Prop := O.T * O.DF ≤ 3 * C2 * O.k * O.f * O.b
def TieVd (O : OnObj S P c) : Prop :=
  0 ≤ O.vd ∧ (∑ p ∈ O.sm, Real.log (p : ℝ)) * (2 + O.vd) ≤ 11 * O.L ∧ O.q1 ∉ O.sm ∧ O.dd ∉ O.sm
def SecondRatioDefinition (O : OnObj S P c) : Prop := O.X2 = aa O / wpp O
def TieBp (O : OnObj S P c) : Prop := O.bp = aa O / Xp O
def TieNc (O : OnObj S P c) : Prop := O.Nc = dl2 O * O.k * O.b * O.x ^ (2 * O.eps) / nH O
def PageLeaves (O : OnObj S P c) (C2 : ℝ) : Prop :=
  ExponentSmallBound O ∧ HalfDegreeAtLeastFour O ∧ PrimeCongruenceConditions O ∧ DegreeAtLeastFortyFour O ∧ DimensionExceedsDegreeByThree O ∧ RankAndLengthLowerBounds O ∧ LeafSZ1 O ∧ LeafW O ∧ SupportGapBounds O ∧
    EtaPowerBound O ∧ LeafSign O ∧ NodeCountBound O ∧ LogPrimeProductBound O ∧ ProductWithRatioBound O ∧ ConductorCongruentPrimePair O ∧ SquaredTimeBound O ∧ PowerTwelveBound O ∧
    DiscriminantDegreeBound O ∧ ProductLowerBoundTwist O ∧ TwistDensityBounds O ∧ TimeDiscriminantBound O C2 ∧ TieVd O ∧ SecondRatioDefinition O ∧ TieBp O ∧ TieNc O
abbrev pageC : OnConst := ⟨1, 14, 70⟩
def px : ℝ := (10 : ℝ) ^ (1200 : ℕ)
def pe : ℝ := 1 / 100
variable (K)
abbrev pageO (v0 : InfinitePlace K) (Tw0 : Finset (HeightOneSpectrum (𝓞 K))) : OnObj (exampleIndefiniteData K v0 Tw0 0) Unit pageC where
  nZ := fun _ => 1
  ρ := fun _ => 1
  U := ⊤
  ψ := fun _ => 1
  V₀ := fun _ => ⊤
  e := fun _ => LinearMap.id
  Ms := fun _ => stdLat K 1
  φ := fun _ => LinearMap.id
  Th1 := fun _ _ => stdLat K 1
  Th := fun _ _ => stdLat K 1
  ThK := fun _ _ => stdLat K 1
  Th0 := fun _ _ => stdLat K 1
  ThJ := fun _ _ => stdLat K 1
  X₃ := fun _ _ => stdLat K 1
  σ := fun _ _ => 1
  a := fun _ _ => 1
  E := fun _ _ => 0
  r1 := fun _ _ => 0
  r2 := fun _ _ => 0
  pde := 0
  ε0 := fun _ _ => 0
  nX := fun _ _ => 1
  θ' := fun _ _ => LinearMap.id
  eX := fun _ _ => LinearMap.id
  pr := fun _ _ => LinearMap.id
  Mt := fun _ _ => stdLat K 1
  nnK := fun _ => 1
  Jp := fun _ _ => 0
  k := 47
  m := 44
  f := 256
  bp := px * Real.exp (px ^ pe) / Real.exp (px ^ (pe / 3))
  Sc := 0
  eta := 0
  T := px * 100000
  DF := 16
  X2 := px * Real.exp (px ^ pe) / (px * Real.exp (px ^ pe) / Real.exp (px ^ (pe / 3)) / (px * (256 / 2)))
  x := px
  eps := pe
  vd := 8
  rr := 90
  de2 := 1
  Nc := ((1 : ℕ) : ℝ) / (256 / 2) * 47 * Real.exp (px ^ pe) * px ^ (2 * pe) / (256 / 2)
  wt := fun _ => 0
  th := fun _ => 0
  ad := fun _ => 0
  T2 := 1
  g1 := 118273
  g2 := 275969
  q1 := 11
  dd := 7
  sm := {2}
variable {K}
variable (v0 : InfinitePlace K) (Tw0 : Finset (HeightOneSpectrum (𝓞 K)))
end OnPage
end Formalism.L2.Indef.Tree


