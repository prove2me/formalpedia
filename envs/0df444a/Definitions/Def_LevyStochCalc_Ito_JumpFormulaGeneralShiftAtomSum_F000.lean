-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaGeneralShiftAtomSum_F000
-- name    : LevyStochCalc_Ito_JumpFormulaGeneralShiftAtomSum_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:03:16.333349+00:00
-- url     : https://prove2.me/theorems/d3b1d962-c76a-49ab-b5ea-ac7822e56216
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaGeneralShiftAtomSum
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaGeneralShiftAtomSum. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaGeneralShiftCappedChain_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaGeneralShiftCappedChain_F003
import Definitions.Def_SourceProof_0d088112759d60f13f10d2df
import Definitions.Def_SourceProof_3b4c8aaeb3983333d32ff10f
import Definitions.Def_SourceProof_5ffe5f6881eccb3f8509bfdc
import Definitions.Def_SourceProof_b233f14b4b88a4af49762008

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The telescope's jump sum over a prescribed evaluation path

Over an enumeration of the atoms of a window, the telescope of a state function along the chain
of capped jump sums collapses to the sum, over those atoms, of the increments of the state
function taken at the left limits of the jump path and displaced by the jump coefficient read at
the prescribed states: an index whose arrival time has passed the horizon contributes nothing and
each in-window index contributes one increment. Almost surely every window carries such an
enumeration, which gives that identification for the path itself and for a path translated by the
jump sum, together with the piecewise translation and the atom sum for the jump sums evaluated at
the point values and at the left limits of the path.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

section JumpSideAssembly

variable (X : Setting.JumpDiffusion W N coeffs x₀) (Y : ℝ → Ω → Fin n → ℝ) {A : Set E} {K : ℕ}
  {θ : Fin K → ℝ} {ε : Fin K → E} {T : ℝ} {ω : Ω}

/-- **The telescope's jump sum is the atom sum of the increments of the state function across
the jumps.** Each in-window index contributes the increment of the state function at the left
limit of the translated path `Z`, displaced by the jump coefficient read along the prescribed
path of states, and the indices past the horizon contribute nothing. -/
theorem sum_range_jumpTermAt_eq_sum_atomEnum_of_path (f : (Fin n → ℝ) → ℝ)
    (Z : ℝ → Ω → Fin n → ℝ)
    {V : ℝ → Ω → Fin n → ℝ} {m : ℕ} (hA : MeasurableSet A) (hmonoθ : StrictMono θ)
    (hmem : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j))
    (hrange : Set.range θ
      = {v : ℝ | ∃ i : ℕ, LevyStochCalc.Poisson.jumpTime N A i ω = (v : WithTop ℝ)
          ∧ 0 < v ∧ v ≤ T})
    (hV : Continuous fun t => V t ω)
    (hstrict : ∀ i : ℕ, LevyStochCalc.Poisson.jumpTime N A (i + 1) ω ≤ ((T : ℝ) : WithTop ℝ) →
      LevyStochCalc.Poisson.jumpTime N A i ω < LevyStochCalc.Poisson.jumpTime N A (i + 1) ω)
    (hshift : ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSumAt X Y A T k ω = Z s ω)
    (hm : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω) :
    (∑ k ∈ Finset.range m,
        (f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + cappedJumpSumAt X Y A T (k + 1) ω)
          - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + cappedJumpSumAt X Y A T k ω)))
      = ∑ j : Fin K, (f (Function.leftLim (fun s => Z s ω) (θ j)
            + coeffs.γ (θ j) (Y (θ j) ω) (ε j))
          - f (Function.leftLim (fun s => Z s ω) (θ j))) :=
  _root_.Prove2MeSourceProof.h_0d088112759d60f13f10d2df (Y := Z)
    (c := cappedJumpSumAt X Y A T) (jump := fun j => coeffs.γ (θ j) (Y (θ j) ω) (ε j)) f
    hmonoθ (fun j => (hmem j).1) hrange hV hstrict hshift
    (fun _k hk => _root_.Prove2MeSourceProof.h_b233f14b4b88a4af49762008 X Y hA hmem hsum hrange hk)
    (fun k hk => _root_.Prove2MeSourceProof.h_5ffe5f6881eccb3f8509bfdc X Y hA hmem hsum hmonoθ.injective hrange
      (hstrict k hk) hk)
    hm
/-- **The telescope's jump sum of a jump diffusion is the atom sum of the increments of the state
function across the jumps.** Each in-window index contributes the increment of the state function
at the left limit of the path, displaced by the jump coefficient read along the prescribed path
of states, and the indices past the horizon contribute nothing. -/
theorem sum_range_jumpTermAt_eq_sum_atomEnum (f : (Fin n → ℝ) → ℝ)
    {V : ℝ → Ω → Fin n → ℝ} {m : ℕ} (hA : MeasurableSet A) (hmonoθ : StrictMono θ)
    (hmem : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j))
    (hrange : Set.range θ
      = {v : ℝ | ∃ i : ℕ, LevyStochCalc.Poisson.jumpTime N A i ω = (v : WithTop ℝ)
          ∧ 0 < v ∧ v ≤ T})
    (hV : Continuous fun t => V t ω)
    (hstrict : ∀ i : ℕ, LevyStochCalc.Poisson.jumpTime N A (i + 1) ω ≤ ((T : ℝ) : WithTop ℝ) →
      LevyStochCalc.Poisson.jumpTime N A i ω < LevyStochCalc.Poisson.jumpTime N A (i + 1) ω)
    (hshift : ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSumAt X Y A T k ω = X.X s ω)
    (hm : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω) :
    (∑ k ∈ Finset.range m,
        (f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + cappedJumpSumAt X Y A T (k + 1) ω)
          - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + cappedJumpSumAt X Y A T k ω)))
      = ∑ j : Fin K, (f (Function.leftLim (fun s => X.X s ω) (θ j)
            + coeffs.γ (θ j) (Y (θ j) ω) (ε j))
          - f (Function.leftLim (fun s => X.X s ω) (θ j))) :=
  sum_range_jumpTermAt_eq_sum_atomEnum_of_path X Y f X.X hA hmonoθ hmem hsum hrange hV hstrict
    hshift hm
end JumpSideAssembly

section MarkIdentificationAe

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

/-- **The telescope's jump sum against the atom enumeration, almost surely.** Almost surely the
window carries a strictly increasing enumeration of its atoms computing every integral over the
window, along which the telescope's jump sum over any range past the horizon is the sum of the
increments of the state function across the jumps, read at the left limits of the translated path
`Z` and displaced by the jump coefficient taken along the prescribed path of states. -/
theorem ae_exists_atomEnum_sum_range_jumpTermAt_of_path (f : (Fin n → ℝ) → ℝ)
    (X : Setting.JumpDiffusion W N coeffs x₀) (Y Z : ℝ → Ω → Fin n → ℝ) {A : Set E}
    {V : ℝ → Ω → Fin n → ℝ} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ)
    (hV : ∀ᵐ ω ∂P, Continuous fun t => V t ω)
    (hshift : ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ),
      cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSumAt X Y A T k ω = Z s ω) :
    ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E),
      (∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A) ∧
      (∀ g : ℝ × E → ℝ,
        ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j)) ∧
      ∀ m : ℕ, ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω →
        (∑ k ∈ Finset.range m,
            (f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                  + cappedJumpSumAt X Y A T (k + 1) ω)
              - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                  + cappedJumpSumAt X Y A T k ω)))
          = ∑ j : Fin K, (f (Function.leftLim (fun s => Z s ω) (θ j)
                + coeffs.γ (θ j) (Y (θ j) ω) (ε j))
              - f (Function.leftLim (fun s => Z s ω) (θ j))) := by
  filter_upwards [_root_.Prove2MeSourceProof.h_2d73a2b6df3c10b500c2eec5 N A hA hAν T,
    _root_.Prove2MeSourceProof.h_3b4c8aaeb3983333d32ff10f N A hA hAν T, hV, hshift]
    with ω hω hstrict hVω hshiftω
  obtain ⟨K, θ, ε, hmonoθ, hrange, hmem, hsum⟩ := hω
  exact ⟨K, θ, ε, hmem, hsum, fun m hm =>
    sum_range_jumpTermAt_eq_sum_atomEnum_of_path X Y f Z hA hmonoθ hmem hsum hrange hVω hstrict
      hshiftω hm⟩
/-- **The telescope's jump sum of a jump diffusion against the atom enumeration, almost surely.**
Almost surely the window carries a strictly increasing enumeration of its atoms computing every
integral over the window, along which the telescope's jump sum over any range past the horizon is
the sum of the increments of the state function across the jumps, read at the left limits of the
path and displaced by the jump coefficient taken along the prescribed path of states. -/
theorem ae_exists_atomEnum_sum_range_jumpTermAt (f : (Fin n → ℝ) → ℝ)
    (X : Setting.JumpDiffusion W N coeffs x₀) (Y : ℝ → Ω → Fin n → ℝ) {A : Set E}
    {V : ℝ → Ω → Fin n → ℝ} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ)
    (hV : ∀ᵐ ω ∂P, Continuous fun t => V t ω)
    (hshift : ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ),
      cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSumAt X Y A T k ω = X.X s ω) :
    ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E),
      (∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A) ∧
      (∀ g : ℝ × E → ℝ,
        ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j)) ∧
      ∀ m : ℕ, ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω →
        (∑ k ∈ Finset.range m,
            (f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                  + cappedJumpSumAt X Y A T (k + 1) ω)
              - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                  + cappedJumpSumAt X Y A T k ω)))
          = ∑ j : Fin K, (f (Function.leftLim (fun s => X.X s ω) (θ j)
                + coeffs.γ (θ j) (Y (θ j) ω) (ε j))
              - f (Function.leftLim (fun s => X.X s ω) (θ j))) :=
  ae_exists_atomEnum_sum_range_jumpTermAt_of_path f X Y X.X hA hAν T hV hshift
end MarkIdentificationAe

section Instances

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

/-- **The piecewise translation between consecutive capped arrival times, along the left
limits.** Strictly between consecutive capped arrival times a path splitting into a continuous
part and the left-limit jump sum is that continuous part translated by the capped left-limit
jump sum. -/
theorem ae_forall_add_cappedJumpSumLeft_eq
    {X : Setting.JumpDiffusion W N coeffs x₀} {A : Set E} {V : ℝ → Ω → Fin n → ℝ}
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      X.X t ω i = V t ω i + JumpSplitting.jumpSumLeft X A t ω i)
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T k ω = X.X s ω :=
  ae_forall_add_cappedJumpSumAt_eq (Y := JumpSplitting.leftLimPath X) hsplit hA hAν hT
/-- **The piecewise translation between consecutive capped arrival times of a translated path
carrying the left-limit jump sum.** Strictly between consecutive capped arrival times a path
splitting into a continuous part and the left-limit jump sum is that continuous part translated
by the capped left-limit jump sum. -/
theorem ae_forall_add_cappedJumpSumLeft_eq_of_path
    {X : Setting.JumpDiffusion W N coeffs x₀} {A : Set E} {Z V : ℝ → Ω → Fin n → ℝ}
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Z t ω i = V t ω i + JumpSplitting.jumpSumLeft X A t ω i)
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T k ω = Z s ω :=
  ae_forall_add_cappedJumpSumAt_eq_of_path (Y := JumpSplitting.leftLimPath X) hsplit hA hAν hT
/-- **The piecewise translation between consecutive capped arrival times, at the point values.**
Strictly between consecutive capped arrival times a path splitting into a continuous part and the
point-evaluated jump sum is that continuous part translated by the capped jump sum. -/
theorem ae_forall_add_cappedJumpSumPoint_eq
    {X : Setting.JumpDiffusion W N coeffs x₀} {A : Set E} {V : ℝ → Ω → Fin n → ℝ}
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      X.X t ω i = V t ω i + JumpSplitting.jumpSum X A t ω i)
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSum X A T k ω = X.X s ω :=
  ae_forall_add_cappedJumpSumAt_eq (Y := X.X) hsplit hA hAν hT
/-- **The telescope's jump sum against the atom enumeration, along the left limits.** The jump
coefficient of each increment is read at the same left limit of the path as the base point of
that increment. -/
theorem ae_exists_atomEnum_sum_range_jumpTermLeft (f : (Fin n → ℝ) → ℝ)
    (X : Setting.JumpDiffusion W N coeffs x₀) {A : Set E}
    {V : ℝ → Ω → Fin n → ℝ} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ)
    (hV : ∀ᵐ ω ∂P, Continuous fun t => V t ω)
    (hshift : ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ),
      cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T k ω = X.X s ω) :
    ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E),
      (∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A) ∧
      (∀ g : ℝ × E → ℝ,
        ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j)) ∧
      ∀ m : ℕ, ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω →
        (∑ k ∈ Finset.range m,
            (f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                  + cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T (k + 1) ω)
              - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                  + cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T k ω)))
          = ∑ j : Fin K, (f (Function.leftLim (fun s => X.X s ω) (θ j)
                + coeffs.γ (θ j) (JumpSplitting.leftLimPath X (θ j) ω) (ε j))
              - f (Function.leftLim (fun s => X.X s ω) (θ j))) :=
  ae_exists_atomEnum_sum_range_jumpTermAt f X (JumpSplitting.leftLimPath X) hA hAν T hV hshift
/-- **The telescope's jump sum against the atom enumeration for a translated path carrying the
left-limit jump sum.** The base point of each increment is the left limit of the translated path
`Z`, while the jump coefficient is read at the left limits of the jump diffusion `X`. -/
theorem ae_exists_atomEnum_sum_range_jumpTermLeft_of_path (f : (Fin n → ℝ) → ℝ)
    (X : Setting.JumpDiffusion W N coeffs x₀) (Z : ℝ → Ω → Fin n → ℝ) {A : Set E}
    {V : ℝ → Ω → Fin n → ℝ} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ)
    (hV : ∀ᵐ ω ∂P, Continuous fun t => V t ω)
    (hshift : ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ),
      cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T k ω = Z s ω) :
    ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E),
      (∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A) ∧
      (∀ g : ℝ × E → ℝ,
        ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j)) ∧
      ∀ m : ℕ, ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω →
        (∑ k ∈ Finset.range m,
            (f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                  + cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T (k + 1) ω)
              - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                  + cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T k ω)))
          = ∑ j : Fin K, (f (Function.leftLim (fun s => Z s ω) (θ j)
                + coeffs.γ (θ j) (JumpSplitting.leftLimPath X (θ j) ω) (ε j))
              - f (Function.leftLim (fun s => Z s ω) (θ j))) :=
  ae_exists_atomEnum_sum_range_jumpTermAt_of_path f X (JumpSplitting.leftLimPath X) Z
    hA hAν T hV hshift
/-- **The telescope's jump sum against the atom enumeration, at the point values.** The jump
coefficient of each increment is read at the point value of the path at the arrival time, while
the base point of that increment is the left limit there. -/
theorem ae_exists_atomEnum_sum_range_jumpTermPoint (f : (Fin n → ℝ) → ℝ)
    (X : Setting.JumpDiffusion W N coeffs x₀) {A : Set E}
    {V : ℝ → Ω → Fin n → ℝ} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ)
    (hV : ∀ᵐ ω ∂P, Continuous fun t => V t ω)
    (hshift : ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ),
      cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSum X A T k ω = X.X s ω) :
    ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E),
      (∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A) ∧
      (∀ g : ℝ × E → ℝ,
        ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j)) ∧
      ∀ m : ℕ, ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω →
        (∑ k ∈ Finset.range m,
            (f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                  + cappedJumpSum X A T (k + 1) ω)
              - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                  + cappedJumpSum X A T k ω)))
          = ∑ j : Fin K, (f (Function.leftLim (fun s => X.X s ω) (θ j)
                + coeffs.γ (θ j) (X.X (θ j) ω) (ε j))
              - f (Function.leftLim (fun s => X.X s ω) (θ j))) :=
  ae_exists_atomEnum_sum_range_jumpTermAt f X X.X hA hAν T hV hshift
end Instances

end LevyStochCalc.Ito.JumpFormula


