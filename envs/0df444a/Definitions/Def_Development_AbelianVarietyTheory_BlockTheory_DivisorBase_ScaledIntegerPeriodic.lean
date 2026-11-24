-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ScaledIntegerPeriodic
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ScaledIntegerPeriodic
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T21:31:15.162483+00:00
-- url     : https://prove2.me/theorems/cc15183e-1600-4006-8214-f1693ab6b889
-- title:
--   Scaled Integer Periodic
-- statement:
--   Definitions and structural lemmas for Scaled Integer Periodic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/ScaledIntegerPeriodic.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_exists_isUnif
import Theorems.Thm_GlobalTheory_SplitFlip_exists_ramified
import Theorems.Thm_GlobalTheory_SplitFlip_hasDepth_indicator
import Theorems.Thm_GlobalTheory_SplitFlip_mem_diagLat
import Theorems.Thm_GlobalTheory_SplitFlip_mem_matLat
import Theorems.Thm_GlobalTheory_SplitFlip_smul_diagLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip
section Defs
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def scaledInt (ϖ : kˣ) (a : ℕ) (m : ℤ) : Set (Matrix (Fin a) (Fin a) k) :=
  {Z | ∀ i j, valuation k (Z i j) ≤ valuation k ((ϖ ^ m : kˣ) : k)}
theorem mem_scaledInt_iff (ϖ : kˣ) (a : ℕ) (m : ℤ) (Z : Matrix (Fin a) (Fin a) k) :
    Z ∈ scaledInt ϖ a m ↔ Z ∈ matLat (Fin a) (ϖ ^ m • stdLat k (Fin a)) := by
  rw [stdLat, smul_diagLat, mem_matLat]
  simp only [mem_diagLat, Pi.one_apply, mul_one]
  rfl
def IsPeriodic (ϖ : kˣ) {a : ℕ} (M : ℤ) (φ : Matrix (Fin a) (Fin a) k → ℂ) : Prop :=
  ∀ X, ∀ Z ∈ scaledInt ϖ a M, φ (X + Z) = φ X
example (ϖ : kˣ) (hϖ : IsUnif ϖ) (a : ℕ) :
    IsPeriodic ϖ 0 ((matLat (Fin a) (stdLat k (Fin a)) : Set (Matrix (Fin a) (Fin a) k)).indicator 1) := by
  intro X Z hZ
  refine (hasDepth_indicator hϖ 0 (stdLat k (Fin a))).2 X Z ?_
  simpa using (mem_scaledInt_iff ϖ a 0 Z).1 hZ
end Defs
def ShellLemma : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ), IsUnif ϖ →
    ∀ (ν : kˣ →* ℂˣ) (e : ℕ), ¬ IsUnram ν → CondLE ϖ e ν →
    ∀ (a : ℕ) (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] (φ : Matrix (Fin a) (Fin a) k → ℂ),
      φ ∈ SB (Matrix (Fin a) (Fin a) k) →
      (∀ (n : Fin a → ℤ) (z : ℂ),
        IntegrableOn (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) (shellSet ϖ n) μ) ∧
      (∀ M : ℤ, IsPeriodic ϖ M φ → ∀ n : Fin a → ℤ, (∃ i, M ≤ n i) → ∀ z : ℂ, shell μ ϖ ν z φ n = 0) ∧
      (∀ M' : ℕ, Function.support φ ⊆ scaledInt ϖ a (-(M' : ℤ)) →
        ∀ n : Fin a → ℤ, ¬ (∀ i, -(M' : ℤ) ≤ n i) → ∀ z : ℂ, shell μ ϖ ν z φ n = 0) ∧
      {n : {n : Fin a → ℤ // Antitone n} | ∃ z : ℂ, shell μ ϖ ν z φ n.1 ≠ 0}.Finite
example (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ∃ (ϖ : kˣ) (ν : kˣ →* ℂˣ) (e : ℕ), IsUnif ϖ ∧ ¬ IsUnram ν ∧ CondLE ϖ e ν := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (k := k)
  obtain ⟨ν, h1, h2, -⟩ := exists_ramified hϖ
  exact ⟨ϖ, ν, 2, hϖ, h1, h2⟩
end GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic


