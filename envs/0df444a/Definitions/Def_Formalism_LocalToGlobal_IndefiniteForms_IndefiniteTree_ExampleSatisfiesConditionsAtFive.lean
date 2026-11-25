-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
-- name    : Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T17:16:28.681185+00:00
-- url     : https://prove2.me/theorems/d6db5704-382b-54fc-bdbb-e7234c38ba23
-- title:
--   Example Satisfies Conditions At Five
-- statement:
--   Definitions and structural lemmas for Example Satisfies Conditions At Five, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ExampleSatisfiesConditionsAtFive.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsWeightedConditional
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditions
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ErrSum
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_UnipotentNumeric
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditionsOfExact
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_key
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_vw_conj_nat
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_vw_nat_nonneg
import Theorems.Thm_Formalism_DivisionValues_place_log_sum_vw_nat_nonneg
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_absorb_local_conditions_exact
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_budget_numeric
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_depth_cases
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_local_conditions_global_form
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_local_conditions_weighted_at_place
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_local_sum_exact
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_one_le_ramw
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_place_sum
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ramified_basic_bound
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_share_numeric
import Theorems.Thm_Formalism_L2_Indef_IndefRows_D_pos
import Theorems.Thm_Formalism_L2_Indef_IndefRows_dW_eq
import Theorems.Thm_P2M_Formalism_DivisionValues_lw_nonneg__acf346c58d0a
import Theorems.Thm_PI_PrimeLogOverPWork_l3

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
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
structure OnConst where

  C : ℝ

  Cb1 : ℝ

  Cb2 : ℝ
namespace OnConst
def Cb (c : OnConst) : ℝ := c.Cb1 + c.Cb2 + 4
def CE (c : OnConst) : ℝ := 4 * c.C ^ 2 + 25 * c.C + c.Cb + 44
end OnConst
structure OnObj {Bs : DefBase K} {Df : DefSide Bs} (S : IndefData Df) (P : Type) [Group P] [Finite P] (c : OnConst) where

  nZ : Bs.J → ℕ

  ρ : ∀ j, Representation K P (Fin (nZ j) → K)

  U : Subgroup P

  ψ : P → 𝓞 K

  V₀ : ∀ j, Submodule K (Fin (nZ j) → K)

  e : ∀ j, (Fin (nZ j) → K) →ₗ[K] (Fin (nZ j) → K)

  Ms : ∀ j, Submodule (𝓞 K) (Fin (nZ j) → K)

  φ : ∀ j, (Fin (S.dW j) → K) →ₗ[K] (Fin (nZ j) → K)

  Th1 : HeightOneSpectrum (𝓞 K) → ∀ j, Submodule (𝓞 K) (Fin (nZ j) → K)

  Th : HeightOneSpectrum (𝓞 K) → ∀ j, Submodule (𝓞 K) (Fin (nZ j) → K)

  ThK : HeightOneSpectrum (𝓞 K) → ∀ j, Submodule (𝓞 K) (Fin (nZ j) → K)

  Th0 : HeightOneSpectrum (𝓞 K) → ∀ j, Submodule (𝓞 K) (Fin (nZ j) → K)

  ThJ : HeightOneSpectrum (𝓞 K) → ∀ j, Submodule (𝓞 K) (Fin (nZ j) → K)

  X₃ : HeightOneSpectrum (𝓞 K) → ∀ j, Submodule (𝓞 K) (Fin (nZ j) → K)

  σ : HeightOneSpectrum (𝓞 K) → Bs.J → K

  a : HeightOneSpectrum (𝓞 K) → Bs.J → K

  E : HeightOneSpectrum (𝓞 K) → Bs.J → ℕ

  r1 : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ

  r2 : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ

  pde : ℕ

  ε0 : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ

  nX : HeightOneSpectrum (𝓞 K) → Bs.J → ℕ

  θ' : ∀ v j, (Fin (nX v j) → K) →ₗ[K] (Fin (nZ j) → K)

  eX : ∀ v j, (Fin (nX v j) → K) →ₗ[K] (Fin (nX v j) → K)

  pr : ∀ v j, (Fin (nX v j) → K) →ₗ[K] (Fin (nX v j) → K)

  Mt : ∀ v j, Submodule (𝓞 K) (Fin (nX v j) → K)

  nnK : Bs.J → K

  Jp : Bs.J → ℕ → ℝ

  k : ℝ

  m : ℝ

  f : ℝ

  bp : ℝ

  Sc : ℝ

  eta : ℝ

  T : ℝ

  DF : ℝ

  X2 : ℝ

  x : ℝ

  eps : ℝ

  vd : ℝ

  rr : ℝ

  de2 : ℝ

  Nc : ℝ

  wt : Bs.J → ℝ

  th : ℕ → ℝ

  ad : ℕ → ℝ

  T2 : ℕ

  g1 : ℕ

  g2 : ℕ

  q1 : ℕ

  dd : ℕ

  sm : Finset ℕ
def AtPair {Bs : DefBase K} {Df : DefSide Bs} (S : IndefData Df) (Q : HeightOneSpectrum (𝓞 K) → Prop) : Prop :=
  ∀ w ∈ S.Tw, Q w ∧ Q (conjPl w)
namespace OnObj
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst} (O : OnObj S P c)
def C (_O : OnObj S P c) : ℝ := c.C
def Cb1 (_O : OnObj S P c) : ℝ := c.Cb1
def Cb2 (_O : OnObj S P c) : ℝ := c.Cb2
def Zg (j : Bs.J) : Submodule K (Fin (O.nZ j) → K) := eig (O.ρ j) O.U O.ψ ⊓ O.V₀ j
def eJ (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : Submodule (𝓞 K) (Fin (O.nZ j) → K) :=
  (O.ThJ v j).map ((O.e j).restrictScalars (𝓞 K))
def Im (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : Submodule (𝓞 K) (Fin (O.nZ j) → K) :=
  ((O.Mt v j).map ((O.θ' v j).restrictScalars (𝓞 K))).map ((O.e j).restrictScalars (𝓞 K))
def ImageLattice (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : Submodule (𝓞 K) (Fin (O.nZ j) → K) :=
  (((O.Mt v j).map ((O.eX v j).restrictScalars (𝓞 K))).map ((O.pr v j).restrictScalars (𝓞 K))).map
    ((O.θ' v j).restrictScalars (𝓞 K))
def r (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : ℝ := if plc v = O.pde then O.r2 v j else O.r1 v j
def e0 (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : ℝ := ((O.E v j : ℝ) - (vw v (O.σ v j) : ℝ)) / (ramw v : ℝ)
def vU0 (v : HeightOneSpectrum (𝓞 K)) : ℝ := (vw v ((Nat.card O.U : ℕ) : K) : ℝ) / (ramw v : ℝ)
def xe : ℝ := O.x ^ O.eps
def b : ℝ := Real.exp O.xe
def L : ℝ := Real.log O.b
def B0 : ℝ := O.f * O.m * O.b * O.L
def E1u : ℝ := O.xe * (O.B0 + O.Nc)
def Se : ℝ := O.Sc + O.eta
def Y : ℝ := O.C * O.DF
def A1 (j : Bs.J) : ℝ := O.C * (Real.log O.k * O.m * O.wt j + O.f * O.k * O.Se)
def Akw (j : Bs.J) : ℝ := O.C * O.k * O.wt j
def aE (j : Bs.J) (l : ℕ) : ℝ :=
  O.A1 j / (l : ℝ) + O.Akw j * O.th l + O.T * O.ad l + (if O.X2 < (l : ℝ) then O.Akw j / (l : ℝ) ^ 2 else 0)
def sB (j : Bs.J) : ℝ := O.wt j + O.f * O.Se
def sC (j : Bs.J) : ℝ := O.C * O.m * (2 + O.vd) * (O.wt j + O.f * O.Se)
def β (l : ℕ) : ℝ := if l = O.dd then O.f * O.k * O.bp else 0
def y : ℝ := 1 / (4 * (O.f * O.k) ^ 3)
def d0 (j : Bs.J) : ℝ := (finrank K (eig (O.ρ j) O.U O.ψ) : ℝ)
def Rb (j : Bs.J) : ℝ := 2 * ((O.nZ j : ℝ) * (O.f * O.m * O.b))
def gq (v : HeightOneSpectrum (𝓞 K)) : ℝ := if plc v = O.g1 ∨ plc v = O.g2 then 2 * O.f * O.rr ^ 2 else 0
def nn (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : ℝ := (vw v (O.nnK j) : ℝ) / (ramw v : ℝ)
def Bad : Finset ℕ := insert O.g1 (insert O.g2 (insert O.q1 (insert O.dd O.sm)))
def errP (j : Bs.J) (l : ℕ) : ℝ :=
  if l = O.g1 ∨ l = O.g2 then 4 * O.T + 4 * O.f * O.rr ^ 2
  else if l ∈ O.sm then 2 * O.sC j + 2 * O.T + 2
  else if l = O.q1 ∨ l = O.dd then 2 * (O.sB j + O.T + 1) + 4 * O.β l
  else errGood O.Y O.X2 (O.A1 j) (O.Akw j) (O.Akw j) O.T O.th O.ad l
def errl (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : ℝ := O.errP j (plc v)
def errOn (w : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : ℝ :=
  O.errl w j + (O.r w j / (ramw w : ℝ) + O.r (conjPl w) j / (ramw (conjPl w) : ℝ)) / ((O.U.index : ℝ) * (S.D : ℝ))
def Cb : ℝ := O.Cb1 + O.Cb2 + 4
def EJ : ℝ := 30 * (O.T2 : ℝ) * O.m * O.b * O.xe ^ 2 + 2 * O.m * O.b
def TjId (j : Bs.J) (v : HeightOneSpectrum (𝓞 K)) (t : Bs.Tup) : Prop :=
  (matLat (S.θ j t) (Df.Tl j t)).map ((O.φ j).restrictScalars (𝓞 K)) = O.ImageLattice v j
end OnObj
section Leaves
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}
def LeafMackey (O : OnObj S P c) : Prop := IsMackey O.U O.ψ
def LeafSup (O : OnObj S P c) : Prop :=
  ∀ j, IsLatIn ⊤ (O.Ms j) ∧ ∀ g : P, (O.Ms j).map ((O.ρ j g).restrictScalars (𝓞 K)) ≤ O.Ms j
def LeafProj (O : OnObj S P c) : Prop :=
  ∀ j, O.e j ∘ₗ O.e j = O.e j ∧ LinearMap.range (O.e j) = O.V₀ j
def TieCoord (O : OnObj S P c) : Prop :=
  (∀ j, Function.Injective (O.φ j) ∧ LinearMap.range (O.φ j) = O.Zg j ∧
    (S.M j).map ((O.φ j).restrictScalars (𝓞 K)) = cut (O.Zg j) (O.Ms j)) ∧
  ∀ w ∈ S.Tw, ∀ j, O.TjId j w (S.μ w) ∧ O.TjId j (conjPl w) (S.μ w)
def RankRows (S : IndefData Df) : Prop := 0 < S.D ∧ ∀ j, S.dW j = S.D
def LeafSpan (O : OnObj S P c) : Prop :=
  AtPair S fun v => ∀ j, IsLatIn ⊤ (O.Th v j) ∧ IsLatIn ⊤ (O.ThK v j)
def LeafLemmaS (O : OnObj S P c) : Prop :=
  AtPair S fun v => ∀ j, O.Th v j ≤ O.Ms j ∧
    (∀ g : P, (O.Th v j).map ((O.ρ j g).restrictScalars (𝓞 K)) ≤ O.Th v j) ∧
    O.σ v j ≠ 0 ∧ O.Th v j ≤ sc (O.σ v j) (O.ThK v j)
def LatticeIndexBoundAtPairs (O : OnObj S P c) : Prop :=
  (AtPair S fun v => ∀ j, IsLatIn ⊤ (O.Th1 v j) ∧ O.Th1 v j ≤ O.Th v j ∧ O.a v j ≠ 0 ∧
    vw v (O.a v j) = (O.E v j : ℤ) ∧
    ∀ W : Submodule K (Fin (O.nZ j) → K),
      (lix v (cut W (O.Ms j)) (cut W (O.Th1 v j)) : ℝ) ≤ (O.E v j : ℝ) * (finrank K W : ℝ) + O.r v j) ∧
  0 ≤ O.de2 ∧ O.de2 ≤ 1 ∧ (∀ v j, 0 ≤ O.r1 v j ∧ 0 ≤ O.r2 v j) ∧
  ∀ j, ∀ S' : Finset (HeightOneSpectrum (𝓞 K)),
    ∑ v ∈ S', lw v * O.r1 v j ≤ (O.nZ j : ℝ) * (O.f * O.m * O.b * O.de2) ∧
    ∑ v ∈ S', lw v * O.r2 v j ≤ (O.nZ j : ℝ) * (O.f * O.m * O.b * O.de2)
def LeafData (O : OnObj S P c) : Prop :=
  AtPair S fun v => ∀ j, (O.Th0 v j).FG ∧ O.Th0 v j ≤ (eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 K) ∧
    sc ((Nat.card O.U : ℕ) : K) (cut (eig (O.ρ j) O.U O.ψ) (O.ThK v j)) ≤ O.Th0 v j
def LeafRankJ (O : OnObj S P c) : Prop :=
  AtPair S fun v => ∀ j, IsLatIn (O.Zg j) ((O.Th0 v j).map ((O.e j).restrictScalars (𝓞 K))) ∧
    IsLatIn (O.Zg j) (O.eJ v j) ∧ O.Th0 v j ≤ O.ThJ v j
def LeafIdentity (O : OnObj S P c) : Prop :=
  AtPair S fun v => ∀ j, O.θ' v j ∘ₗ O.eX v j = O.e j ∘ₗ O.θ' v j ∧
    ∀ x ∈ LinearMap.range (O.eX v j), x - O.pr v j x ∈ LinearMap.ker (O.θ' v j)
def LeafTW2 (O : OnObj S P c) : Prop :=
  AtPair S fun v => ∀ j, IsLatIn (O.Zg j) (O.X₃ v j) ∧ IsLatIn (O.Zg j) (O.Im v j) ∧
    Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.X₃ v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Im v j)
def LeafTW1 (O : OnObj S P c) : Prop :=
  (AtPair S fun v => ∀ j, 0 ≤ O.ε0 v j ∧ (lix v (cut (O.Zg j) (O.Ms j)) (O.X₃ v j) : ℝ) ≤
      (lix v (cut (O.Zg j) (O.Ms j)) (O.eJ v j) : ℝ) + (ramw v : ℝ) * O.ε0 v j) ∧
  ∀ w ∈ S.Tw, ∑ j, (O.ε0 w j + O.ε0 (conjPl w) j) ≤ 2 / (plc w : ℝ) ^ 2
def LeafShareI (O : OnObj S P c) : Prop :=
  ∀ j, ∃ ep : ℝ, ep ≤ O.y ∧ (1 - ep) * (O.nZ j : ℝ) ≤ (Nat.card O.U : ℝ) * O.d0 j
def LeafIndexU (O : OnObj S P c) : Prop := (1 - O.y) * (Nat.card O.U : ℝ) ≤ (O.U.index : ℝ)
def LeafBadShare (O : OnObj S P c) : Prop :=
  ∀ j, ∃ del : ℝ, 0 ≤ del ∧ del ≤ 1 / 4 ∧ (1 - del) * O.d0 j ≤ (S.D : ℝ)
def LeafUnip (O : OnObj S P c) : Prop :=
  1 ≤ O.rr ∧ ∀ w ∈ S.Tw, (vw w ((Nat.card O.U : ℕ) : K) : ℝ) =
    (ramw w : ℝ) * (if plc w = O.g1 ∨ plc w = O.g2 then O.f * O.rr * (O.rr - 1) / 2 else 0)
def LeafDepthGood (N : IndefNum Bs) (O : OnObj S P c) : Prop :=
  (∀ l, 0 ≤ O.th l ∧ 0 ≤ O.ad l) ∧
  (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → ∑ p ∈ Q, O.th p * Real.log (p : ℝ) ≤ O.C / O.k) ∧
  (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → O.T * ∑ p ∈ Q, O.ad p * Real.log (p : ℝ) ≤ O.C * (O.m * O.b)) ∧
  ∀ w ∈ S.Tw, ¬ (plc w ∈ O.sm ∨ plc w = O.q1 ∨ plc w = O.dd ∨ plc w = O.g1 ∨ plc w = O.g2) → ∀ j,
    ((plc w : ℝ) ≤ O.Y → O.e0 w j ≤ N.F0 w j + O.aE j (plc w) + 1 ∧
      O.e0 (conjPl w) j ≤ N.F0 w j + O.aE j (plc w) + 1) ∧
    (O.Y < (plc w : ℝ) → O.e0 w j = 0 ∧ O.e0 (conjPl w) j = 0 ∧ 0 ≤ N.F0 w j)
def LeafDepthRam (N : IndefNum Bs) (O : OnObj S P c) : Prop :=
  ∀ w ∈ S.Tw, (plc w = O.q1 ∨ plc w = O.dd) → ∀ j,
    O.e0 w j ≤ O.sB j + O.T + 1 ∧ O.e0 (conjPl w) j ≤ O.sB j + O.T + 1 ∧
    (plc w = O.q1 → N.F0 w j = 0) ∧ (plc w = O.dd → -(2 * (O.f * O.k * O.bp)) ≤ N.F0 w j ∧ N.F0 w j ≤ 0)
def LeafDepth2 (N : IndefNum Bs) (O : OnObj S P c) : Prop :=
  ∀ w ∈ S.Tw, plc w ∈ O.sm → ∀ j,
    O.e0 w j ≤ O.sC j + O.T + 1 ∧ O.e0 (conjPl w) j ≤ O.sC j + O.T + 1 ∧ N.F0 w j = 0
def LeafDepthLevel (N : IndefNum Bs) (O : OnObj S P c) : Prop :=
  ∀ w ∈ S.Tw, (plc w = O.g1 ∨ plc w = O.g2) → ∀ j,
    O.e0 w j ≤ 2 * O.T - O.nn w j ∧ O.e0 (conjPl w) j ≤ 2 * O.T - O.nn (conjPl w) j ∧
    O.nn w j + O.nn (conjPl w) j = -(2 * N.F0 w j)
def LeafPage (O : OnObj S P c) : Prop :=
  1 ≤ O.C ∧ 1 ≤ O.k ∧ 1 ≤ O.m ∧ 8 ≤ O.f ∧ 0 ≤ O.T ∧ 0 ≤ O.Sc ∧ 0 ≤ O.eta ∧ 0 ≤ O.bp ∧ 0 ≤ O.vd ∧ 0 ≤ O.Nc ∧
  O.g1.Prime ∧ O.g2.Prime ∧ O.q1.Prime ∧ O.dd.Prime ∧
  O.g1 ≠ O.g2 ∧ O.q1 ≠ O.dd ∧ O.q1 ≠ O.g1 ∧ O.q1 ≠ O.g2 ∧ O.dd ≠ O.g1 ∧ O.dd ≠ O.g2 ∧
  O.g1 ∉ O.sm ∧ O.g2 ∉ O.sm ∧ O.q1 ∉ O.sm ∧ O.dd ∉ O.sm ∧ 1 ≤ O.x
def LeafSizes (O : OnObj S P c) : Prop :=
  (∀ j, 0 ≤ O.wt j ∧ O.wt j ≤ 2 * O.f * O.b) ∧
  1 < O.Y ∧ Real.log O.Y ≤ 2 * O.L ∧ O.Y ≤ O.m * O.b ∧
  O.k * O.Se * O.L ≤ O.m * O.b ∧
  O.k ≤ O.X2 ∧ Real.log O.k ≤ O.L ∧
  1 ≤ O.L
def LeafX (O : OnObj S P c) : Prop := Real.log O.x ≤ O.xe ∧ (O.T2 : ℝ) ≤ O.f
def LeafBad (O : OnObj S P c) : Prop :=
  0 ≤ O.Cb1 ∧ 0 ≤ O.Cb2 ∧ ∀ j,
    (2 * (O.sB j + O.T + 1) + 4 * (O.f * O.k * O.bp)) * Real.log ((O.q1 * O.dd : ℕ) : ℝ) ≤ O.Cb1 * (O.f * O.m * O.b) ∧
    (∑ p ∈ O.sm, Real.log (p : ℝ)) * (2 * O.sC j + 2 * O.T + 2) ≤ O.Cb2 * (O.f * O.m * O.b * O.L) ∧
    (4 * O.T + 4 * O.f * O.rr ^ 2) * Real.log ((O.g1 * O.g2 : ℕ) : ℝ) ≤ 4 * O.b
def LeafJSum (O : OnObj S P c) : Prop :=
  ∀ j, (∀ l, 0 ≤ O.Jp j l) ∧
    ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → ∑ p ∈ Q, O.Jp j p * Real.log (p : ℝ) ≤ O.EJ
def LeafJExp (N : IndefNum Bs) (O : OnObj S P c) : Prop := ∀ w ∈ S.Tw, ∀ j, N.J0 (S.μ w) w j ≤ O.Jp j (plc w)
def TieErr (O : OnObj S P c) : Prop := ∀ w ∈ S.Tw, ∀ j, S.err0 w j = O.errOn w j
def ErrorConstantMatchesDefinition (N : IndefNum Bs) (O : OnObj S P c) (CE : ℝ) : Prop := ∀ j, N.E1 j = CE * O.E1u
end Leaves
def ONwith {Bs : DefBase K} {Df : DefSide Bs} (S : IndefData Df) (N : IndefNum Bs)
    (err : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ) : Prop :=
  (∀ w ∈ S.Tw, ∑ j, ((S.Iw j (S.μ w) w : ℝ) + (S.Iw j (S.μ w) (conjPl w) : ℝ)) ≤
    (∑ j, (2 * ((ramw w : ℝ) * N.F0 w j) + (ramw w : ℝ) * err w j) +
      (ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2)) * (S.D : ℝ)) ∧
  (∀ w ∈ S.Tw, ∀ j, 0 ≤ err w j) ∧
  ∀ j, ∑ w ∈ S.Tw, lw w * ((ramw w : ℝ) * err w j + (ramw w : ℝ) * N.J0 (S.μ w) w j) ≤ N.E1 j
theorem on_iff_with {Bs : DefBase K} {Df : DefSide Bs} (S : IndefData Df) (N : IndefNum Bs) :
    S.ON N ↔ ONwith S N S.err0 := by
  exact Iff.rfl
theorem rankRows_of {Bs : DefBase K} {Df : DefSide Bs} (R : IndefRows Df) (wf : Df.WF) :
    RankRows R.toIndefData := ⟨R.D_pos, R.dW_eq wf⟩
section Proof
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}
theorem ramw_pos (v : HeightOneSpectrum (𝓞 K)) : (0 : ℝ) < (ramw v : ℝ) := by
  have h : (1 : ℤ) ≤ ramw v := one_le_ramw v
  have h' : (0 : ℤ) < ramw v := by omega
  exact_mod_cast h'
theorem index_pos (U : Subgroup P) : (0 : ℝ) < (U.index : ℝ) := by
  have hne : U.index ≠ 0 := by
    first
    | exact Subgroup.index_ne_zero_of_finite
    | exact Subgroup.FiniteIndex.index_ne_zero
    | (have h := U.card_mul_index
       have hP : 0 < Nat.card P := Nat.card_pos
       intro h0
       rw [h0, mul_zero] at h
       omega)
  exact_mod_cast Nat.pos_of_ne_zero hne
theorem card_pos (U : Subgroup P) : (0 : ℝ) < (Nat.card U : ℝ) := by
  have h : 0 < Nat.card U := Nat.card_pos
  exact_mod_cast h
theorem matLat_one' {d : ℕ} (L : Submodule (𝓞 K) (Fin d → K)) :
    matLat (1 : Matrix (Fin d) (Fin d) K) L = L := by
  unfold matLat
  rw [Matrix.mulVecLin_one]
  first
  | exact Submodule.map_id L
  | (ext x; simp)
theorem local_bound (O : OnObj S P c) (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) (t : Bs.Tup)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O)
    (hC : Function.Injective (O.φ j) ∧ LinearMap.range (O.φ j) = O.Zg j ∧
      (S.M j).map ((O.φ j).restrictScalars (𝓞 K)) = cut (O.Zg j) (O.Ms j))
    (hT : O.TjId j v t)
    (hSp : IsLatIn ⊤ (O.Th v j) ∧ IsLatIn ⊤ (O.ThK v j))
    (hS : O.Th v j ≤ O.Ms j ∧ (∀ g : P, (O.Th v j).map ((O.ρ j g).restrictScalars (𝓞 K)) ≤ O.Th v j) ∧
      O.σ v j ≠ 0 ∧ O.Th v j ≤ sc (O.σ v j) (O.ThK v j))
    (h0 : IsLatIn ⊤ (O.Th1 v j) ∧ O.Th1 v j ≤ O.Th v j ∧ O.a v j ≠ 0 ∧ vw v (O.a v j) = (O.E v j : ℤ) ∧
      ∀ W : Submodule K (Fin (O.nZ j) → K),
        (lix v (cut W (O.Ms j)) (cut W (O.Th1 v j)) : ℝ) ≤ (O.E v j : ℝ) * (finrank K W : ℝ) + O.r v j)
    (hD : (O.Th0 v j).FG ∧ O.Th0 v j ≤ (eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 K) ∧
      sc ((Nat.card O.U : ℕ) : K) (cut (eig (O.ρ j) O.U O.ψ) (O.ThK v j)) ≤ O.Th0 v j)
    (hJ : IsLatIn (O.Zg j) ((O.Th0 v j).map ((O.e j).restrictScalars (𝓞 K))) ∧
      IsLatIn (O.Zg j) (O.eJ v j) ∧ O.Th0 v j ≤ O.ThJ v j)
    (hU : O.θ' v j ∘ₗ O.eX v j = O.e j ∘ₗ O.θ' v j)
    (hK : ∀ x ∈ LinearMap.range (O.eX v j), x - O.pr v j x ∈ LinearMap.ker (O.θ' v j))
    (h2 : IsLatIn (O.Zg j) (O.X₃ v j) ∧ IsLatIn (O.Zg j) (O.Im v j) ∧
      Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.X₃ v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Im v j))
    (h1 : (lix v (cut (O.Zg j) (O.Ms j)) (O.X₃ v j) : ℝ) ≤
      (lix v (cut (O.Zg j) (O.Ms j)) (O.eJ v j) : ℝ) + (ramw v : ℝ) * O.ε0 v j) :
    (idx v (S.M j) (matLat (S.θ j t) (Df.Tl j t)) : ℝ) ≤
      (ramw v : ℝ) * ((O.e0 v j + O.vU0 v) * (S.dW j : ℝ) +
        (O.r v j / (ramw v : ℝ) + (O.nZ j : ℝ) * O.vU0 v) / (O.U.index : ℝ) + O.ε0 v j) := by
  have key := local_conditions_weighted_at_place K (Fin (O.nZ j) → K) v P (O.ρ j) O.U O.ψ hMk (O.V₀ j) (O.e j) (hProj j).1 (hProj j).2
    (O.Ms j) (O.Th1 v j) (O.Th v j) (O.ThK v j) (O.Th0 v j) (O.ThJ v j) (O.X₃ v j)
    (hSup j).1 h0.1 hSp.1 hSp.2 h0.2.1 hS.1 hD.1 hD.2.1 (hSup j).2 hS.2.1 (O.σ v j) hS.2.2.1 hS.2.2.2 hD.2.2
    (O.a v j) (O.E v j) (O.r v j) h0.2.2.1 h0.2.2.2.1 h0.2.2.2.2 hJ.1 hJ.2.1 hJ.2.2 h2.1
    (Fin (O.nX v j) → K) (O.θ' v j) (O.eX v j) (O.pr v j) (O.Mt v j) hU hK h2.2.1 h2.2.2
    ((ramw v : ℝ) * O.ε0 v j) h1 (S.dW j) (O.φ j) hC.1 hC.2.1 (S.M j) (matLat (S.θ j t) (Df.Tl j t)) hC.2.2 hT
  rw [Module.finrank_fin_fun] at key
  have hr : (ramw v : ℝ) ≠ 0 := (ramw_pos v).ne'
  have hi : (O.U.index : ℝ) ≠ 0 := (index_pos O.U).ne'
  have e : (ramw v : ℝ) * ((O.e0 v j + O.vU0 v) * (S.dW j : ℝ) +
        (O.r v j / (ramw v : ℝ) + (O.nZ j : ℝ) * O.vU0 v) / (O.U.index : ℝ) + O.ε0 v j) =
      ((O.E v j : ℝ) - (vw v (O.σ v j) : ℝ) + (vw v ((Nat.card O.U : ℕ) : K) : ℝ)) * (S.dW j : ℝ) +
        (O.r v j + (O.nZ j : ℝ) * (vw v ((Nat.card O.U : ℕ) : K) : ℝ)) / (O.U.index : ℝ) +
          (ramw v : ℝ) * O.ε0 v j := by
    unfold OnObj.e0 OnObj.vU0
    field_simp
    try ring
  first
  | (rw [e]; exact key)
  | linarith [key, e]
theorem L_eq (O : OnObj S P c) : O.L = O.xe := by
  unfold OnObj.L OnObj.b
  exact Real.log_exp _
theorem y_bounds (O : OnObj S P c) (hPg : LeafPage O) : 0 ≤ O.y ∧ O.y ≤ 1 / 8 := by
  obtain ⟨-, hk, -, hf, -⟩ := hPg
  have h1 : 1 ≤ O.f * O.k := by nlinarith
  have h8 : 8 ≤ O.f * O.k := by nlinarith
  have h3 : O.f * O.k ≤ (O.f * O.k) ^ 3 := by
    first
    | exact le_self_pow₀ h1 (by norm_num)
    | exact le_self_pow h1 (by norm_num)
    | nlinarith [mul_le_mul h1 h1 zero_le_one (by linarith)]
  have hpos : 0 < 4 * (O.f * O.k) ^ 3 := by linarith
  unfold OnObj.y
  constructor
  · exact div_nonneg zero_le_one hpos.le
  · rw [div_le_div_iff₀ hpos (by norm_num)]
    linarith
theorem r_nonneg (O : OnObj S P c) (hT0 : LatticeIndexBoundAtPairs O) (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : 0 ≤ O.r v j := by
  obtain ⟨-, -, -, hr, -⟩ := hT0
  unfold OnObj.r
  split_ifs
  · exact (hr v j).2
  · exact (hr v j).1
theorem errorTerm_nonneg (O : OnObj S P c) (hPg : LeafPage O) (hSz : LeafSizes O) (hth : ∀ l, 0 ≤ O.th l ∧ 0 ≤ O.ad l)
    (j : Bs.J) (l : ℕ) : 0 ≤ O.errP j l := by
  obtain ⟨hC, hk, hm, hf, hT, hSc, heta, hbp, hvd, -⟩ := hPg
  have hwt : 0 ≤ O.wt j := (hSz.1 j).1
  have hSe : 0 ≤ O.Se := by
    unfold OnObj.Se
    linarith
  have hfSe : 0 ≤ O.f * O.Se := mul_nonneg (by linarith) hSe
  have hsB : 0 ≤ O.sB j := by
    unfold OnObj.sB
    linarith
  have hsC : 0 ≤ O.sC j := by
    unfold OnObj.sC
    exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)) (by linarith)
  have hβ : ∀ l, 0 ≤ O.β l := by
    intro l
    unfold OnObj.β
    split_ifs
    · exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) hbp
    · exact le_rfl
  have hA1 : 0 ≤ O.A1 j := by
    unfold OnObj.A1
    exact mul_nonneg (by linarith) (add_nonneg (mul_nonneg (mul_nonneg (Real.log_nonneg hk) (by linarith)) hwt)
      (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hSe))
  have hAkw : 0 ≤ O.Akw j := by
    unfold OnObj.Akw
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) hwt
  unfold OnObj.errP
  split_ifs
  · nlinarith [sq_nonneg O.rr]
  · linarith
  · nlinarith [hβ l]
  · unfold errGood
    have hl : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    by_cases hY : (l : ℝ) ≤ O.Y
    · rw [if_pos hY]
      have e1 : 0 ≤ O.A1 j / (l : ℝ) := div_nonneg hA1 hl
      have e2 : 0 ≤ O.Akw j * O.th l := mul_nonneg hAkw (hth l).1
      have e3 : 0 ≤ O.T * O.ad l := mul_nonneg hT (hth l).2
      have e4 : 0 ≤ (if O.X2 < (l : ℝ) then O.Akw j / (l : ℝ) ^ 2 else 0) := by
        split_ifs
        · exact div_nonneg hAkw (by positivity)
        · exact le_rfl
      linarith
    · rw [if_neg hY]
set_option maxHeartbeats 800000 in

theorem bad_sum (O : OnObj S P c) (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O) (j : Bs.J) :
    ∑ p ∈ O.Bad, Real.log (p : ℝ) * O.errP j p ≤ O.Cb * (O.f * O.m * O.b * O.L) := by
  obtain ⟨hC, hk, hm, hf, hT, hSc, heta, hbp, hvd, hNc, pg1, pg2, pq1, pdd, h12, hqd, hqg1, hqg2, hdg1, hdg2,
    hg1s, hg2s, hq1s, hdds, hx⟩ := hPg
  obtain ⟨hwt, hY1, hlY, hYmb, hkSe, hkX, hlk, hL1⟩ := hSz
  obtain ⟨hCb1, hCb2, hB⟩ := hBad
  obtain ⟨hBq, hBs, hBg⟩ := hB j
  have hg1 : O.g1 ∉ insert O.g2 (insert O.q1 (insert O.dd O.sm)) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨h12, Ne.symm hqg1, Ne.symm hdg1, hg1s⟩
  have hg2 : O.g2 ∉ insert O.q1 (insert O.dd O.sm) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨Ne.symm hqg2, Ne.symm hdg2, hg2s⟩
  have hq : O.q1 ∉ insert O.dd O.sm := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hqd, hq1s⟩
  have eg1 : O.errP j O.g1 = 4 * O.T + 4 * O.f * O.rr ^ 2 := by
    unfold OnObj.errP
    rw [if_pos (Or.inl rfl : O.g1 = O.g1 ∨ O.g1 = O.g2)]
  have eg2 : O.errP j O.g2 = 4 * O.T + 4 * O.f * O.rr ^ 2 := by
    unfold OnObj.errP
    rw [if_pos (Or.inr rfl : O.g2 = O.g1 ∨ O.g2 = O.g2)]
  have eq1 : O.errP j O.q1 = 2 * (O.sB j + O.T + 1) := by
    unfold OnObj.errP
    rw [if_neg (show ¬(O.q1 = O.g1 ∨ O.q1 = O.g2) from fun h => h.elim hqg1 hqg2), if_neg hq1s,
      if_pos (Or.inl rfl : O.q1 = O.q1 ∨ O.q1 = O.dd)]
    unfold OnObj.β
    rw [if_neg hqd]
    ring
  have edd : O.errP j O.dd = 2 * (O.sB j + O.T + 1) + 4 * (O.f * O.k * O.bp) := by
    unfold OnObj.errP
    rw [if_neg (show ¬(O.dd = O.g1 ∨ O.dd = O.g2) from fun h => h.elim hdg1 hdg2), if_neg hdds,
      if_pos (Or.inr rfl : O.dd = O.q1 ∨ O.dd = O.dd)]
    unfold OnObj.β
    rw [if_pos rfl]
  have es : ∀ p ∈ O.sm, O.errP j p = 2 * O.sC j + 2 * O.T + 2 := by
    intro p hp
    unfold OnObj.errP
    rw [if_neg (show ¬(p = O.g1 ∨ p = O.g2) by rintro (rfl | rfl); exacts [hg1s hp, hg2s hp]), if_pos hp]
  have hsm : ∑ p ∈ O.sm, Real.log (p : ℝ) * O.errP j p =
      (∑ p ∈ O.sm, Real.log (p : ℝ)) * (2 * O.sC j + 2 * O.T + 2) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun p hp => by rw [es p hp])
  unfold OnObj.Bad
  rw [Finset.sum_insert hg1, Finset.sum_insert hg2, Finset.sum_insert hq, Finset.sum_insert hdds, hsm, eg1, eg2, eq1, edd]
  have hg1p : (0 : ℝ) < O.g1 := by exact_mod_cast pg1.pos
  have hg2p : (0 : ℝ) < O.g2 := by exact_mod_cast pg2.pos
  have hq1p : (0 : ℝ) < O.q1 := by exact_mod_cast pq1.pos
  have hddp : (0 : ℝ) < O.dd := by exact_mod_cast pdd.pos
  have lg : Real.log ((O.g1 * O.g2 : ℕ) : ℝ) = Real.log (O.g1 : ℝ) + Real.log (O.g2 : ℝ) := by
    push_cast
    exact Real.log_mul hg1p.ne' hg2p.ne'
  have lq : Real.log ((O.q1 * O.dd : ℕ) : ℝ) = Real.log (O.q1 : ℝ) + Real.log (O.dd : ℝ) := by
    push_cast
    exact Real.log_mul hq1p.ne' hddp.ne'
  rw [lg] at hBg
  rw [lq] at hBq
  have hlq : 0 ≤ Real.log (O.q1 : ℝ) := Real.log_nonneg (by exact_mod_cast pq1.one_lt.le)
  have hb : 0 < O.b := by
    unfold OnObj.b
    exact Real.exp_pos _
  have hfmb : 0 ≤ O.f * O.m * O.b := mul_nonneg (mul_nonneg (by linarith) (by linarith)) hb.le
  have hfm : 1 ≤ O.f * O.m := one_le_mul_of_one_le_of_one_le (by linarith) hm
  have hfmL : 1 ≤ O.f * O.m * O.L := one_le_mul_of_one_le_of_one_le hfm hL1
  have h1 : O.Cb1 * (O.f * O.m * O.b) ≤ O.Cb1 * (O.f * O.m * O.b * O.L) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hfmb hL1) hCb1
  have h2 : O.b ≤ O.f * O.m * O.b * O.L := by
    calc O.b = O.b * 1 := (mul_one _).symm
      _ ≤ O.b * (O.f * O.m * O.L) := mul_le_mul_of_nonneg_left hfmL hb.le
      _ = O.f * O.m * O.b * O.L := by ring
  have hBn : 0 ≤ O.f * O.k * O.bp := mul_nonneg (mul_nonneg (by linarith) (by linarith)) hbp
  unfold OnObj.Cb
  linarith [mul_nonneg hBn hlq, hBg, hBq, hBs, h1, h2]
theorem on_core (N : IndefNum Bs) (O : OnObj S P c) (CE : ℝ) (hRk : RankRows S)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O) (hC : TieCoord O)
    (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : LatticeIndexBoundAtPairs O) (hD : LeafData O) (hJ : LeafRankJ O)
    (hI : LeafIdentity O) (h2 : LeafTW2 O) (h1 : LeafTW1 O)
    (hSh : LeafShareI O) (hIU : LeafIndexU O) (hBS : LeafBadShare O) (hUn : LeafUnip O)
    (hG : LeafDepthGood N O) (hR : LeafDepthRam N O) (h2p : LeafDepth2 N O) (hL : LeafDepthLevel N O)
    (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hJS : LeafJSum O) (hJE : LeafJExp N O) (hCE : c.CE ≤ CE) (tE1 : ErrorConstantMatchesDefinition N O CE) : ONwith S N O.errOn := by
  obtain ⟨hDpos, hdW⟩ := hRk
  have hPg' := hPg
  obtain ⟨hC1, hk1, hm1, hf8, hTn, hSc, heta, hbp, hvd, hNc, -⟩ := hPg'
  obtain ⟨hw, hY1, hlY, hYb, hkS, hkX, hlk, hL1⟩ := hSz
  have hSz' : LeafSizes O := ⟨hw, hY1, hlY, hYb, hkS, hkX, hlk, hL1⟩
  obtain ⟨hth, hsth, hsad, hgood⟩ := hG
  have hδ := index_pos O.U
  have hcard := card_pos O.U
  have hDr : (0 : ℝ) < (S.D : ℝ) := by exact_mod_cast hDpos
  have hb0 : 0 < O.b := Real.exp_pos _
  have hLxe : O.L = O.xe := L_eq O
  have hSe : 0 ≤ O.Se := by unfold OnObj.Se; linarith

  have hloc1 : ∀ w ∈ S.Tw, ∀ j, (idx w (S.M j) (matLat (S.θ j (S.μ w)) (Df.Tl j (S.μ w))) : ℝ) ≤
      (ramw w : ℝ) * ((O.e0 w j + O.vU0 w) * (S.dW j : ℝ) +
        (O.r w j / (ramw w : ℝ) + (O.nZ j : ℝ) * O.vU0 w) / (O.U.index : ℝ) + O.ε0 w j) := fun w hw j =>
    local_bound O w j (S.μ w) hMk hSup hProj (hC.1 j) (hC.2 w hw j).1 ((hSp w hw).1 j) ((hS w hw).1 j)
      ((hT0.1 w hw).1 j) ((hD w hw).1 j) ((hJ w hw).1 j) ((hI w hw).1 j).1 ((hI w hw).1 j).2 ((h2 w hw).1 j)
      ((h1.1 w hw).1 j).2
  have hloc2 : ∀ w ∈ S.Tw, ∀ j,
      (idx (conjPl w) (S.M j) (matLat (S.θ j (S.μ w)) (Df.Tl j (S.μ w))) : ℝ) ≤
      (ramw (conjPl w) : ℝ) * ((O.e0 (conjPl w) j + O.vU0 (conjPl w)) * (S.dW j : ℝ) +
        (O.r (conjPl w) j / (ramw (conjPl w) : ℝ) + (O.nZ j : ℝ) * O.vU0 (conjPl w)) / (O.U.index : ℝ) +
          O.ε0 (conjPl w) j) := fun w hw j =>
    local_bound O (conjPl w) j (S.μ w) hMk hSup hProj (hC.1 j) (hC.2 w hw j).2 ((hSp w hw).2 j)
      ((hS w hw).2 j) ((hT0.1 w hw).2 j) ((hD w hw).2 j) ((hJ w hw).2 j) ((hI w hw).2 j).1 ((hI w hw).2 j).2
      ((h2 w hw).2 j) ((h1.1 w hw).2 j).2

  have hy := y_bounds O hPg
  have hsh : ∀ j, (O.nZ j : ℝ) / (O.U.index : ℝ) ≤ 3 * (S.D : ℝ) := by
    intro j
    obtain ⟨ep, hep, hs1⟩ := hSh j
    obtain ⟨del, hdel0, hdel1, hs3⟩ := hBS j
    have hnz : (0 : ℝ) ≤ (O.nZ j : ℝ) := Nat.cast_nonneg _
    have hs1' : (1 - O.y) * (O.nZ j : ℝ) ≤ (Nat.card O.U : ℝ) * O.d0 j :=
      le_trans (mul_le_mul_of_nonneg_right (by linarith) hnz) hs1
    have hd0 : 0 ≤ O.d0 j := by unfold OnObj.d0; exact Nat.cast_nonneg _
    have := share_numeric (O.nZ j : ℝ) (O.d0 j) (S.D : ℝ) (Nat.card O.U : ℝ) (O.U.index : ℝ) O.y O.y del
      hcard hδ hnz hd0 hy.1 le_rfl hy.2 hdel0 hdel1 hs1' hIU hs3
    linarith

  have hv : ∀ w ∈ S.Tw, 0 ≤ O.vU0 w ∧ O.vU0 (conjPl w) = O.vU0 w ∧ 4 * O.vU0 w ≤ O.gq w := by
    intro w hw
    have hρ := ramw_pos w
    refine ⟨?_, ?_, ?_⟩
    · unfold OnObj.vU0
      exact div_nonneg (by exact_mod_cast Formalism.DivisionValues.PlaceSumConjugation.vw_nat_nonneg _ w) hρ.le
    · unfold OnObj.vU0
      rw [Formalism.DivisionValues.PlaceSumConjugation.vw_conj_nat, (ramified_basic_bound K w).2.2.2.1]
    · have h := hUn.2 w hw
      have hv' : O.vU0 w = (if plc w = O.g1 ∨ plc w = O.g2 then O.f * O.rr * (O.rr - 1) / 2 else 0) := by
        unfold OnObj.vU0; rw [h]; field_simp
      rw [hv']
      unfold OnObj.gq
      have hr := hUn.1
      split_ifs
      · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ O.f) (by linarith : (0 : ℝ) ≤ O.rr)]
      · norm_num

  have hdep : ∀ w ∈ S.Tw, ∀ j, O.e0 w j + O.e0 (conjPl w) j - 2 * N.F0 w j + 2 * O.gq w ≤ O.errl w j := by
    intro w hw j
    have dc := depth_cases (O.e0 w j) (O.e0 (conjPl w) j) (N.F0 w j)
    unfold OnObj.errl OnObj.errP
    by_cases hl : plc w = O.g1 ∨ plc w = O.g2
    · rw [if_pos hl]
      have hg : O.gq w = 2 * O.f * O.rr ^ 2 := if_pos hl
      obtain ⟨a, b, c⟩ := hL w hw hl j
      have := dc.2.2.2.2 O.T (O.nn w j) (O.nn (conjPl w) j) (O.gq w) a b c
      rw [hg] at this ⊢
      linarith
    · rw [if_neg hl]
      have hg : O.gq w = 0 := if_neg hl
      rw [hg]
      by_cases h2' : plc w ∈ O.sm
      · rw [if_pos h2']
        obtain ⟨a, b, c⟩ := h2p w hw h2' j
        have := dc.2.2.2.1 (O.sC j) O.T a b c
        linarith
      · rw [if_neg h2']
        by_cases hr : plc w = O.q1 ∨ plc w = O.dd
        · rw [if_pos hr]
          obtain ⟨a, b, cq, cd⟩ := hR w hw hr j
          have hβ : -(2 * O.β (plc w)) ≤ N.F0 w j ∧ N.F0 w j ≤ 0 := by
            unfold OnObj.β
            split_ifs with hd
            · exact cd hd
            · rw [cq (hr.resolve_right hd)]; norm_num
          have := dc.2.2.1 (O.sB j) O.T (O.β (plc w)) a b hβ.1 hβ.2
          linarith
        · rw [if_neg hr]
          have hng : ¬ (plc w ∈ O.sm ∨ plc w = O.q1 ∨ plc w = O.dd ∨ plc w = O.g1 ∨ plc w = O.g2) := by
            rintro (h | h | h | h | h)
            exacts [h2' h, hr (Or.inl h), hr (Or.inr h), hl (Or.inl h), hl (Or.inr h)]
          have hgg := hgood w hw hng j
          unfold errGood
          by_cases hy' : (plc w : ℝ) ≤ O.Y
          · rw [if_pos hy']
            obtain ⟨a, b⟩ := hgg.1 hy'
            have := dc.1 (O.aE j (plc w)) a b
            show _ ≤ 2 * O.aE j (plc w) + 2
            linarith
          · rw [if_neg hy']
            obtain ⟨a, b, c⟩ := hgg.2 (lt_of_not_ge hy')
            have := dc.2.1 a b c
            linarith

  have hDS : DepthSums O.T (O.C / O.k) (O.C * (O.m * O.b)) O.th O.ad := ⟨hsth, hsad⟩
  let EA : Bs.J → ℝ := fun j =>
    2 * (O.C * (Real.log O.k * O.m * O.wt j + O.f * O.k * O.Se) * Real.log O.Y + O.C * O.k * O.wt j * (O.C / O.k) +
      O.C * (O.m * O.b) + 2.04 * (O.C * O.k * O.wt j) / O.X2 + Real.log 4 * O.Y) +
      ∑ p ∈ O.Bad, Real.log (p : ℝ) * O.errP j p
  have hEA : ∀ j, ∑ w ∈ S.Tw, lw w * ((ramw w : ℝ) * O.errl w j) ≤ EA j := by
    intro j
    have hlk0 : 0 ≤ Real.log O.k := Real.log_nonneg hk1
    have hw0 := (hw j).1
    have hA1 : 0 ≤ O.C * (Real.log O.k * O.m * O.wt j + O.f * O.k * O.Se) := by
      have : 0 ≤ Real.log O.k * O.m * O.wt j := by positivity
      have : 0 ≤ O.f * O.k * O.Se := by positivity
      positivity
    have hA2 : 0 ≤ O.C * O.k * O.wt j := by positivity
    refine local_sum_exact K S.Tw O.Bad (O.errP j)
      (errorTerm_nonneg O hPg hSz' hth j) O.Y O.X2 _ _ _ O.T (O.C / O.k) (O.C * (O.m * O.b)) O.th O.ad hY1
      (by linarith) hA1 hA2 hA2 hTn (fun p => (hth p).1) (fun p => (hth p).2) hDS (fun w => O.errl w j) ?_
    intro w _
    unfold OnObj.errl
    split_ifs with hB
    · exact le_rfl
    · have hB' : ¬ (plc w = O.g1 ∨ plc w = O.g2) ∧ plc w ∉ O.sm ∧ ¬ (plc w = O.q1 ∨ plc w = O.dd) := by
        have e : O.Bad = insert O.g1 (insert O.g2 (insert O.q1 (insert O.dd O.sm))) := rfl
        rw [e] at hB
        simp only [Finset.mem_insert, not_or] at hB
        obtain ⟨a, b, c, d, f⟩ := hB
        exact ⟨by rintro (h | h); exacts [a h, b h], f, by rintro (h | h); exacts [c h, d h]⟩
      unfold OnObj.errP
      rw [if_neg hB'.1, if_neg hB'.2.1, if_neg hB'.2.2]
      exact le_rfl

  have hRb : ∀ j, ∀ S' : Finset (HeightOneSpectrum (𝓞 K)),
      ∑ w ∈ S', lw w * ((ramw w : ℝ) * (O.r w j / (ramw w : ℝ))) ≤ O.Rb j := by
    intro j S'
    obtain ⟨-, hde0, hde1, hr0, hbud⟩ := hT0
    have e : ∑ w ∈ S', lw w * ((ramw w : ℝ) * (O.r w j / (ramw w : ℝ))) = ∑ w ∈ S', lw w * O.r w j :=
      Finset.sum_congr rfl fun w _ => by rw [mul_div_cancel₀ _ (ramw_pos w).ne']
    rw [e]
    have s1 : ∑ w ∈ S', lw w * O.r w j ≤ ∑ w ∈ S', lw w * O.r1 w j + ∑ w ∈ S', lw w * O.r2 w j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun w _ => ?_
      have hl := lw_nonneg' w
      obtain ⟨a, b⟩ := hr0 w j
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ hl
      unfold OnObj.r
      split_ifs <;> linarith
    obtain ⟨b1, b2⟩ := hbud j S'
    have hB : 0 ≤ (O.nZ j : ℝ) * (O.f * O.m * O.b) := by
      have : 0 ≤ O.f * O.m * O.b := by positivity
      positivity
    have hde : (O.nZ j : ℝ) * (O.f * O.m * O.b * O.de2) ≤ (O.nZ j : ℝ) * (O.f * O.m * O.b) := by
      have e2 : (O.nZ j : ℝ) * (O.f * O.m * O.b * O.de2) = ((O.nZ j : ℝ) * (O.f * O.m * O.b)) * O.de2 := by ring
      rw [e2]; exact mul_le_of_le_one_right hB hde1
    unfold OnObj.Rb
    linarith

  have hEJ : ∀ j, ∑ w ∈ S.Tw, lw w * ((ramw w : ℝ) * N.J0 (S.μ w) w j) ≤ O.EJ := by
    intro j
    have e : ∑ w ∈ S.Tw, lw w * ((ramw w : ℝ) * N.J0 (S.μ w) w j) ≤
        ∑ w ∈ S.Tw, lw w * ((ramw w : ℝ) * O.Jp j (plc w)) :=
      Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hJE w hw j) (ramw_pos w).le) (lw_nonneg' w)
    refine le_trans e (le_trans (place_sum K S.Tw (O.Jp j) (hJS j).1)
      (le_trans (le_of_eq ?_) ((hJS j).2 (S.Tw.image plc) ?_)))
    · exact Finset.sum_congr rfl fun p _ => mul_comm _ _
    · intro p hp
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hp
      exact (ramified_basic_bound K w).1

  have X := local_conditions_global_form K S.D hDpos Bs.Tup S.μ Bs.J S.dW hdW S.M
    (fun j t => matLat (S.θ j t) (Df.Tl j t)) (fun j _ => (1 : Matrix (Fin (S.dW j)) (Fin (S.dW j)) K)) S.Tw
    O.e0 (fun v j => O.r v j / (ramw v : ℝ)) O.ε0 N.F0 O.errl (fun w j => (ramw w : ℝ) * N.J0 (S.μ w) w j)
    O.vU0 O.gq (fun j => (O.nZ j : ℝ)) EA O.Rb (fun _ => O.EJ) (O.U.index : ℝ)
    (∑ w ∈ S.Tw, lw w * ((ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2))) hδ
    (by intro w hw j; simp only [matLat_one']; exact hloc1 w hw j)
    (by intro w hw j; simp only [matLat_one']; exact hloc2 w hw j)
    hsh hv hdep h1.2 hEA hRb hEJ le_rfl
  obtain ⟨c1, c2, -⟩ := X
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    have h := c1 w hw
    simp only [matLat_one'] at h
    rw [(ramified_basic_bound K w).2.2.2.2] at h
    simp only [IndefData.Iw]
    exact h
  · intro w hw j
    unfold OnObj.errOn
    have := errorTerm_nonneg O hPg hSz' hth j (plc w)
    have h0 := r_nonneg O hT0 w j
    have h0' := r_nonneg O hT0 (conjPl w) j
    have := ramw_pos w
    have := ramw_pos (conjPl w)
    have : 0 ≤ (O.r w j / (ramw w : ℝ) + O.r (conjPl w) j / (ramw (conjPl w) : ℝ)) /
        ((O.U.index : ℝ) * (S.D : ℝ)) := by positivity
    unfold OnObj.errl
    linarith
  · intro j
    have h := c2 j
    simp only [EA] at h
    have hCE : 4 * O.C ^ 2 + 25 * O.C + O.Cb + 44 ≤ CE := hCE
    have hE1 := tE1

    have b1 := budget_numeric (O.nZ j : ℝ) (O.U.index : ℝ) (S.D : ℝ) (O.f * O.m * O.b) hδ hDr
      (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hb0.le) (hsh j)
    have hCb0' : 0 ≤ O.Cb := by unfold OnObj.Cb; linarith [hBad.1, hBad.2.1]

    have hbad := bad_sum O hPg hSz' hX hBad j
    have b2 := absorb_local_conditions_exact O.C O.Cb O.L O.xe O.f O.m O.b O.k (O.wt j) O.Se O.Y O.X2
      (∑ p ∈ O.Bad, Real.log (p : ℝ) * O.errP j p) hC1 hCb0'
      hL1 (le_of_eq hLxe) (by linarith) hm1 hb0 hk1 hlk (hw j).1 (hw j).2 hSe hkS hY1 hlY hYb hkX hbad

    have hxe1 : 1 ≤ O.xe := by rw [← hLxe]; exact hL1
    have hEJb : O.EJ ≤ 32 * O.xe * (O.f * O.m * O.b * O.L) := by
      unfold OnObj.EJ
      rw [hLxe]
      have hmb : 0 ≤ O.m * O.b := mul_nonneg (by linarith) hb0.le
      have hx2 : 1 ≤ O.xe ^ 2 := one_le_pow₀ hxe1
      have hmbx : 0 ≤ O.m * O.b * O.xe ^ 2 := mul_nonneg hmb (sq_nonneg _)
      have t1 : (O.T2 : ℝ) * (O.m * O.b * O.xe ^ 2) ≤ O.f * (O.m * O.b * O.xe ^ 2) :=
        mul_le_mul_of_nonneg_right hX.2 hmbx
      have t2a : O.m * O.b ≤ O.m * O.b * O.xe ^ 2 := le_mul_of_one_le_right hmb hx2
      have t2b : O.m * O.b * O.xe ^ 2 ≤ O.f * (O.m * O.b * O.xe ^ 2) := le_mul_of_one_le_left hmbx (by linarith)
      have e : 32 * O.xe * (O.f * O.m * O.b * O.xe) = 32 * (O.f * (O.m * O.b * O.xe ^ 2)) := by ring
      have e2 : 30 * (O.T2 : ℝ) * O.m * O.b * O.xe ^ 2 = 30 * ((O.T2 : ℝ) * (O.m * O.b * O.xe ^ 2)) := by ring
      have e3 : 2 * O.m * O.b = 2 * (O.m * O.b) := by ring
      rw [e, e2, e3]
      linarith
    have eR : 2 * O.Rb j / ((O.U.index : ℝ) * (S.D : ℝ)) =
        2 * (2 * ((O.nZ j : ℝ) * (O.f * O.m * O.b))) / ((O.U.index : ℝ) * (S.D : ℝ)) := rfl
    have hB0 : 0 ≤ O.f * O.m * O.b * O.L :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hb0.le) (by linarith)
    have hxe0 : 0 ≤ O.xe := by linarith
    have hCb0 : 0 ≤ O.Cb := by unfold OnObj.Cb; linarith [hBad.1, hBad.2.1]
    have hfin : (4 * O.C ^ 2 + 25 * O.C + O.Cb + 12) * O.xe * (O.f * O.m * O.b * O.L) +
        32 * O.xe * (O.f * O.m * O.b * O.L) ≤ CE * O.E1u := by
      unfold OnObj.E1u OnObj.B0
      have h1' : 0 ≤ (CE - (4 * O.C ^ 2 + 25 * O.C + O.Cb + 44)) * (O.xe * (O.f * O.m * O.b * O.L)) :=
        mul_nonneg (by linarith) (mul_nonneg hxe0 hB0)
      have hCE0 : 0 ≤ CE := by linarith [sq_nonneg O.C]
      have h2' : 0 ≤ CE * (O.xe * O.Nc) := mul_nonneg hCE0 (mul_nonneg hxe0 hNc)
      have e : CE * (O.xe * (O.f * O.m * O.b * O.L + O.Nc)) -
          ((4 * O.C ^ 2 + 25 * O.C + O.Cb + 12) * O.xe * (O.f * O.m * O.b * O.L) +
            32 * O.xe * (O.f * O.m * O.b * O.L)) =
          (CE - (4 * O.C ^ 2 + 25 * O.C + O.Cb + 44)) * (O.xe * (O.f * O.m * O.b * O.L)) +
            CE * (O.xe * O.Nc) := by ring
      linarith
    rw [hE1 j]
    have e3 : ∑ w ∈ S.Tw, lw w * ((ramw w : ℝ) * O.errOn w j + (ramw w : ℝ) * N.J0 (S.μ w) w j) =
        ∑ w ∈ S.Tw, lw w * ((ramw w : ℝ) * (O.errl w j + (O.r w j / (ramw w : ℝ) +
          O.r (conjPl w) j / (ramw (conjPl w) : ℝ)) / ((O.U.index : ℝ) * (S.D : ℝ))) +
            (ramw w : ℝ) * N.J0 (S.μ w) w j) := rfl
    rw [e3]
    unfold OnObj.Rb at h
    linarith
theorem on_of_leaves (N : IndefNum Bs) (O : OnObj S P c) (CE : ℝ) (hRk : RankRows S)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O) (hC : TieCoord O)
    (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : LatticeIndexBoundAtPairs O) (hD : LeafData O) (hJ : LeafRankJ O)
    (hI : LeafIdentity O) (h2 : LeafTW2 O) (h1 : LeafTW1 O)
    (hSh : LeafShareI O) (hIU : LeafIndexU O) (hBS : LeafBadShare O) (hUn : LeafUnip O)
    (hG : LeafDepthGood N O) (hR : LeafDepthRam N O) (h2p : LeafDepth2 N O) (hL : LeafDepthLevel N O)
    (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hJS : LeafJSum O) (hJE : LeafJExp N O) (hCE : c.CE ≤ CE) (tE1 : ErrorConstantMatchesDefinition N O CE) (tErr : TieErr O) : S.ON N := by
  obtain ⟨c1, c2, c3⟩ := on_core N O CE hRk hMk hSup hProj hC hSp hS hT0 hD hJ hI h2 h1 hSh hIU hBS hUn hG hR h2p hL
    hPg hSz hX hBad hJS hJE hCE tE1
  rw [on_iff_with]
  refine ⟨fun w hw => ?_, fun w hw j => ?_, fun j => ?_⟩
  · simp only [tErr w hw]
    exact c1 w hw
  · rw [tErr w hw j]
    exact c2 w hw j
  · calc ∑ w ∈ S.Tw, lw w * ((ramw w : ℝ) * S.err0 w j + (ramw w : ℝ) * N.J0 (S.μ w) w j)
          = ∑ w ∈ S.Tw, lw w * ((ramw w : ℝ) * O.errOn w j + (ramw w : ℝ) * N.J0 (S.μ w) w j) :=
            Finset.sum_congr rfl (fun w hw => by rw [tErr w hw j])
        _ ≤ N.E1 j := c3 j
theorem on_of_rows (N : IndefNum Bs) (R : IndefRows Df) (wf : Df.WF) (O : OnObj R.toIndefData P c) (CE : ℝ)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O) (hC : TieCoord O)
    (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : LatticeIndexBoundAtPairs O) (hD : LeafData O) (hJ : LeafRankJ O)
    (hI : LeafIdentity O) (h2 : LeafTW2 O) (h1 : LeafTW1 O)
    (hSh : LeafShareI O) (hIU : LeafIndexU O) (hBS : LeafBadShare O) (hUn : LeafUnip O)
    (hG : LeafDepthGood N O) (hR : LeafDepthRam N O) (h2p : LeafDepth2 N O) (hL : LeafDepthLevel N O)
    (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hJS : LeafJSum O) (hJE : LeafJExp N O) (hCE : c.CE ≤ CE) (tE1 : ErrorConstantMatchesDefinition N O CE) (tErr : TieErr O) : R.toIndefData.ON N := by
  exact on_of_leaves N O CE (rankRows_of R wf) hMk hSup hProj hC hSp hS hT0 hD hJ hI h2 h1 hSh hIU hBS hUn
    hG hR h2p hL hPg hSz hX hBad hJS hJE hCE tE1 tErr
theorem on_of_scale (Z : IndefScale Bs) (Cp CH : ℝ) (R : IndefRows Df) (wf : Df.WF) (O : OnObj R.toIndefData P c)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O) (hC : TieCoord O)
    (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : LatticeIndexBoundAtPairs O) (hD : LeafData O) (hJ : LeafRankJ O)
    (hI : LeafIdentity O) (h2 : LeafTW2 O) (h1 : LeafTW1 O)
    (hSh : LeafShareI O) (hIU : LeafIndexU O) (hBS : LeafBadShare O) (hUn : LeafUnip O)
    (hG : LeafDepthGood (Z.num Cp CH) O) (hR : LeafDepthRam (Z.num Cp CH) O) (h2p : LeafDepth2 (Z.num Cp CH) O)
    (hL : LeafDepthLevel (Z.num Cp CH) O)
    (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hJS : LeafJSum O) (hJE : LeafJExp (Z.num Cp CH) O) (hCE : c.CE ≤ Cp) (hE : Z.E1u = O.E1u) (tErr : TieErr O) :
    R.toIndefData.ON (Z.num Cp CH) := by
  have tE1 : ErrorConstantMatchesDefinition (Z.num Cp CH) O Cp := by
    intro j
    show Cp * Z.E1u = Cp * O.E1u
    rw [hE]
  exact on_of_rows (Z.num Cp CH) R wf O Cp hMk hSup hProj hC hSp hS hT0 hD hJ hI h2 h1 hSh hIU hBS hUn
    hG hR h2p hL hPg hSz hX hBad hJS hJE hCE tE1 tErr
def side_of_leaves (Z : IndefScale Bs) (Cp CH : ℝ) (R : IndefRows Df) (wf : Df.WF) (h3 : R.toIndefData.L3 (Z.num Cp CH))
    (O : OnObj R.toIndefData P c)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O) (hC : TieCoord O)
    (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : LatticeIndexBoundAtPairs O) (hD : LeafData O) (hJ : LeafRankJ O)
    (hI : LeafIdentity O) (h2 : LeafTW2 O) (h1 : LeafTW1 O)
    (hSh : LeafShareI O) (hIU : LeafIndexU O) (hBS : LeafBadShare O) (hUn : LeafUnip O)
    (hG : LeafDepthGood (Z.num Cp CH) O) (hR : LeafDepthRam (Z.num Cp CH) O) (h2p : LeafDepth2 (Z.num Cp CH) O)
    (hL : LeafDepthLevel (Z.num Cp CH) O)
    (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hJS : LeafJSum O) (hJE : LeafJExp (Z.num Cp CH) O) (hCE : c.CE ≤ Cp) (hE : Z.E1u = O.E1u) (tErr : TieErr O) :
    IndefSide Df (Z.num Cp CH) :=
  { R with
    l3 := h3
    on := on_of_scale Z Cp CH R wf O hMk hSup hProj hC hSp hS hT0 hD hJ hI h2 h1 hSh hIU hBS hUn hG hR h2p hL
      hPg hSz hX hBad hJS hJE hCE hE tErr }
end Proof
section Examples₂
variable (K)
def stdLat (n : ℕ) : Submodule (𝓞 K) (Fin n → K) :=
  Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n)))
abbrev exampleBs (v0 : InfinitePlace K) : DefBase K where
  K0 := ⊥
  v0 := v0
  Tup := Bool
  μ0 := false
  Ix := Unit
  fIx := inferInstance
  J := Unit
  fJ := inferInstance
abbrev exampleDf (v0 : InfinitePlace K) : DefSide (exampleBs K v0) where
  nV := fun _ => 1
  HV := fun _ => 1
  Mt := fun _ => stdLat K 1
  dQ := fun _ => 1
  Pq := fun _ => 1
  XQ := fun _ _ => 1
  Qp := fun _ _ => ⊤
  dZ := fun _ _ => 1
  HT := fun _ _ => 1
  XT := fun _ _ _ => 1
  Tl := fun _ _ => stdLat K 1
  Zp := fun _ _ _ => ⊤
open Classical in

abbrev exampleIndefiniteData (v0 : InfinitePlace K) (Tw0 : Finset (HeightOneSpectrum (𝓞 K))) (er : ℝ) : IndefData (exampleDf K v0) where
  μ := fun w => decide (w ∈ Tw0)
  Tw := Tw0
  D := 1
  XE := fun _ => 1
  Ep := fun _ => ⊤
  ι := fun _ => 1
  dW := fun _ => 1
  XW := fun _ _ => 1
  Wp := fun _ _ => ⊤
  M := fun _ => stdLat K 1
  θ := fun _ _ => 1
  κ := fun _ => 1
  lam := fun _ _ _ _ => 1
  err0 := fun _ _ => er
abbrev exampleConstants (v0 : InfinitePlace K) (F E : ℝ) : IndefNum (exampleBs K v0) where
  F0 := fun w _ => if plc w = 3 then F else 0
  J0 := fun _ _ _ => 0
  E1 := fun _ => E
  l3 := fun _ => 0
  l6 := fun _ => 0
  hh := 0
  la := 0
  de := 0
abbrev exampleC : OnConst := ⟨1, 2 * Real.log 143, 1⟩
abbrev exampleObject (v0 : InfinitePlace K) (Tw0 : Finset (HeightOneSpectrum (𝓞 K))) : OnObj (exampleIndefiniteData K v0 Tw0 0) Unit exampleC where
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
  k := 1
  m := 1
  f := 8
  bp := 0
  Sc := 0
  eta := 0
  T := 0
  DF := 3
  X2 := 1
  x := 300
  eps := 1
  vd := 0
  rr := 1
  de2 := 1
  Nc := 0
  wt := fun _ => 0
  th := fun _ => 0
  ad := fun _ => 0
  T2 := 0
  g1 := 5
  g2 := 7
  q1 := 11
  dd := 13
  sm := {2}
variable {K} (v0 : InfinitePlace K) (Tw0 : Finset (HeightOneSpectrum (𝓞 K)))
variable (h3 : ∀ w ∈ Tw0, plc w = 3)
include h3
omit h3
section Level
variable (h5 : ∀ w ∈ Tw0, plc w = 5)
include h5
end Level
end Examples₂
end Formalism.L2.Indef.Tree


