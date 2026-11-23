-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeafCoefficientValuation_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeafCoefficientValuation_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:30.391938+00:00
-- url     : https://prove2.me/theorems/85fb8946-8016-4032-bcd3-071a962a1d7c
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LeafCoefficientValuation/Development.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LeafCoeffVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LCV
open PowerSeries Finset
def W (p d : ℕ) (j : ℤ) (f : PowerSeries ℚ) : Prop :=
  ∀ m : ℕ, padicNorm p (coeff m f) ^ d ≤ (p : ℚ) ^ ((m : ℤ) - j)
def gser (p : ℕ) (T : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => ∑ k ∈ range (n + 1), coeff n (T ^ (p * (p ^ 2) ^ k)) / (p : ℚ) ^ k
def SMul : Prop := ∀ (p d : ℕ), p.Prime → 1 ≤ d → ∀ (j k : ℤ) (f g : PowerSeries ℚ),
  W p d j f → W p d k g → W p d (j + k) (f * g)
def SAdd : Prop := ∀ (p d : ℕ), p.Prime → 1 ≤ d → ∀ (j : ℤ) (f g : PowerSeries ℚ),
  W p d j f → W p d j g → W p d j (f + g)
def SSub : Prop := ∀ (p d : ℕ), p.Prime → 1 ≤ d → ∀ (j : ℤ) (f g : PowerSeries ℚ),
  W p d j f → W p d j g → W p d j (f - g)
def SMono : Prop := ∀ (p d : ℕ), p.Prime → 1 ≤ d → ∀ (j j' : ℤ) (f : PowerSeries ℚ),
  j' ≤ j → W p d j f → W p d j' f
def SSum : Prop := ∀ (p d : ℕ), p.Prime → 1 ≤ d → ∀ (j : ℤ) (ι : Type) (s : Finset ι)
  (x : ι → PowerSeries ℚ), (∀ i ∈ s, W p d j (x i)) → W p d j (∑ i ∈ s, x i)
def SPow : Prop := ∀ (p d : ℕ), p.Prime → 1 ≤ d → ∀ (j : ℤ) (f : PowerSeries ℚ),
  W p d j f → ∀ n : ℕ, W p d (n * j) (f ^ n)
def SSmul : Prop := ∀ (p d : ℕ), p.Prime → 1 ≤ d → ∀ (j s : ℤ) (c : ℚ) (f : PowerSeries ℚ),
  W p d j f → padicNorm p c ^ d ≤ (p : ℚ) ^ (-s) → W p d (j + s) (c • f)
def SPowDiff : Prop := ∀ (p d : ℕ), p.Prime → 1 ≤ d → ∀ (j s : ℤ) (a b : PowerSeries ℚ),
  0 ≤ s → W p d j a → W p d j b → W p d (j + s) (a - b) → ∀ n : ℕ, 1 ≤ n →
  W p d (n * j + s) (a ^ n - b ^ n)
def SFrobIter : Prop := ∀ (p d : ℕ), p.Prime → 1 ≤ d → ∀ (j : ℤ) (f : PowerSeries ℚ),
  W p d j f → ∀ (i m : ℕ),
  padicNorm p (coeff (p ^ i * m) (f ^ (p ^ i)) - (coeff m f) ^ (p ^ i)) ^ d ≤
    (p : ℚ) ^ (((p ^ i * m : ℕ) : ℤ) - (p ^ i : ℕ) * j - d)
def SLeafW : Prop := ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ t : Fin 1 → PowerSeries ℚ, IsLeaf p t →
  W p (p ^ 2 - 1) 1 (t 0)
def SLeafLow : Prop := ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ t : Fin 1 → PowerSeries ℚ, IsLeaf p t →
  coeff 1 (t 0) = 1 ∧ coeff (p ^ 2) (t 0) = -1 / (p : ℚ)
def SZe3 : Prop := ∀ p : ℕ, p.Prime → ∀ t : Fin 1 → PowerSeries ℚ, IsLeaf p t → ∀ i1 : Fin 1,
  ze3 p t i1 = (1 / (p : ℚ)) • gser p (t 0)
def SGW : Prop := ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ t : Fin 1 → PowerSeries ℚ, IsLeaf p t →
  W p (p ^ 2 - 1) ((p : ℤ) + (p ^ 2 - 1 : ℕ)) (gser p (t 0) - (t 0) ^ p)
def SKey : Prop := ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ t : Fin 1 → PowerSeries ℚ, IsLeaf p t → ∀ e : ℕ,
  padicNorm p (coeff (p ^ 3 * p ^ e) ((gser p (t 0)) ^ (p ^ e))) = (p : ℚ) ^ (p ^ (e + 1))
def SConv : Prop := ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (Z g : PowerSeries ℚ) (e : ℕ),
  Z = (1 / (p : ℚ)) • g →
  padicNorm p (coeff (p ^ 3 * p ^ e) (g ^ (p ^ e))) = (p : ℚ) ^ (p ^ (e + 1)) →
  padicValRat p (coeff (p ^ 3 * p ^ e) ((-Z) ^ (p ^ e)) / ((p ^ e).factorial : ℚ)) =
    -(((p : ℤ) + 1) * (p : ℤ) ^ e + padicValNat p (p ^ e).factorial)
end PI.LCV
end


