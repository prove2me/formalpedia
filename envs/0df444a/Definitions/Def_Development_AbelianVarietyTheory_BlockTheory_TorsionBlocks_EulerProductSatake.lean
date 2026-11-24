-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_EulerProductSatake
-- name    : Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_EulerProductSatake
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T23:44:14.601153+00:00
-- url     : https://prove2.me/theorems/d151ac58-8c5a-40c9-9bba-f15b5ef1f141
-- title:
--   Euler Product Satake
-- statement:
--   Definitions and structural lemmas for Euler Product Satake, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/EulerProductSatake.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
namespace GlobalTheory.IndefiniteRowSideFullHecke.EulerProductLocalFactors
noncomputable section
abbrev Place (K : Type) [Field K] [NumberField K] := HeightOneSpectrum (𝓞 K)
def normAt {K : Type} [Field K] [NumberField K] (w : Place K) : ℝ :=
  (Ideal.absNorm w.asIdeal : ℝ)
def zetaR (σ : ℝ) : ℝ := (riemannZeta (σ : ℂ)).re
section Euler
variable {K : Type} [Field K] [NumberField K] {ι : Type}
def localFactor (I : Finset ι) (x : Place K → ι → ℂ) (w : Place K) : ℂ :=
  ∏ i ∈ I, (1 - x w i)⁻¹
def eulerProd (T : Set (Place K)) (I : Finset ι) (x : Place K → ι → ℂ) : ℂ :=
  ∏' w : {w : Place K // w ∉ T}, localFactor I x w.1
def localLog (I : Finset ι) (x : Place K → ι → ℂ) (w : Place K) : ℂ :=
  ∑ i ∈ I, -Complex.log (1 - x w i)
def eulerLog (T : Set (Place K)) (I : Finset ι) (x : Place K → ι → ℂ) : ℂ :=
  ∑' w : {w : Place K // w ∉ T}, localLog I x w.1
def ConvergesAbsolutely (T : Set (Place K)) (I : Finset ι) (x : Place K → ι → ℂ) : Prop :=
  (∀ w, w ∉ T → ∀ i ∈ I, ‖x w i‖ < 1) ∧
  Summable (fun w : {w : Place K // w ∉ T} => ‖localFactor I x w.1 - 1‖) ∧
  Summable (fun w : {w : Place K // w ∉ T} => ‖localLog I x w.1‖) ∧
  Multipliable (fun w : {w : Place K // w ∉ T} => localFactor I x w.1) ∧
  eulerProd T I x ≠ 0 ∧
  Complex.exp (eulerLog T I x) = eulerProd T I x
end Euler
def SatakeBound {E : Type} [Field E] [NumberField E] (T : Set (Place E)) (r : ℕ) (s : ℝ)
    (x : Place E → Fin r → ℂ) : Prop :=
  ∀ w, w ∉ T → ∀ i, ‖x w i‖ ≤ normAt w ^ (((r : ℝ) - 1) / 2 - s)
def twistTerm {F : Type} [Field F] [NumberField F] (ω : Place F → ℂ) (v : Place F) (i : ℕ) : ℂ :=
  ω v ^ i * ((normAt v : ℂ) ^ i)⁻¹
def dPart {F : Type} [Field F] [NumberField F] (S : Set (Place F)) (ω : Place F → ℂ)
    (r t : ℕ) : ℂ :=
  eulerProd S (Finset.Icc (t + 1) (r + t)) (twistTerm ω)
def dLog {F : Type} [Field F] [NumberField F] (S : Set (Place F)) (ω : Place F → ℂ)
    (r t : ℕ) : ℂ :=
  eulerLog S (Finset.Icc (t + 1) (r + t)) (twistTerm ω)
def placesOver {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E]
    [Algebra F E] (S : Set (Place F)) : Set (Place E) :=
  {w | ∃ v ∈ S, w.asIdeal.LiesOver v.asIdeal}
def StandardBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (f r : ℕ), Module.finrank ℚ E = 2 * f →
    ∀ (s : ℝ), 7 / 2 ≤ s - ((r : ℝ) - 1) / 2 →
    ∀ (T : Set (Place E)) (x : Place E → Fin r → ℂ), SatakeBound T r s x →
      ConvergesAbsolutely T Finset.univ x ∧
      ‖eulerLog T Finset.univ x‖ ≤ 2 * f * r * Real.log (zetaR (7 / 2)) ∧
      |Real.log ‖eulerProd T Finset.univ x‖| ≤ 2 * f * r * Real.log (zetaR (7 / 2)) ∧
      2 * f * r * Real.log (zetaR (7 / 2)) ≤ 0.24 * f * r
def NormalisingBound : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (f r t : ℕ), Module.finrank ℚ F = f →
    Odd t → r + 5 ≤ t →
    ∀ (S : Set (Place F)) (ω : Place F → ℂ), (∀ v, v ∉ S → ‖ω v‖ ≤ 1) →
      ConvergesAbsolutely S (Finset.Icc (t + 1) (r + t)) (twistTerm ω) ∧
      (∀ i ∈ Finset.Icc (t + 1) (r + t), ConvergesAbsolutely S {i} (twistTerm ω)) ∧
      dPart S ω r t = ∏ i ∈ Finset.Icc (t + 1) (r + t), eulerProd S {i} (twistTerm ω) ∧
      ((∀ v, v ∉ S → (ω v).im = 0) → (dPart S ω r t).im = 0 ∧ 0 < (dPart S ω r t).re) ∧
      ‖dLog S ω r t‖ ≤ f * r * Real.log (zetaR ((t : ℝ) + 1)) ∧
      |Real.log ‖dPart S ω r t‖| ≤ f * r * Real.log (zetaR ((t : ℝ) + 1)) ∧
      f * r * Real.log (zetaR ((t : ℝ) + 1)) ≤ 0.005 * f * r
def QuotientBound : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (f r t : ℕ), Module.finrank ℚ F = f → Module.finrank F E = 2 → Odd t → r + 5 ≤ t →
    ∀ (S : Set (Place F)) (ω : Place F → ℂ), (∀ v, v ∉ S → ‖ω v‖ ≤ 1) →
    ∀ (x : Place E → Fin r → ℂ), SatakeBound (placesOver E S) r ((1 + (t : ℝ)) / 2) x →
      eulerProd (placesOver E S) Finset.univ x ≠ 0 ∧ dPart S ω r t ≠ 0 ∧
      Complex.exp (eulerLog (placesOver E S) Finset.univ x - dLog S ω r t)
        = eulerProd (placesOver E S) Finset.univ x / dPart S ω r t ∧
      ‖eulerLog (placesOver E S) Finset.univ x - dLog S ω r t‖ ≤ (f : ℝ) * r / 4 ∧
      |Real.log ‖eulerProd (placesOver E S) Finset.univ x / dPart S ω r t‖| ≤ (f : ℝ) * r / 4
def EulerLogBounds : Prop :=
  StandardBound ∧ NormalisingBound ∧ QuotientBound
def SharpConstant : Prop :=
  2 * Real.log (zetaR (7 / 2)) ≤ 0.2387
open Classical in

def quadSign {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E]
    [Algebra F E] (v : Place F) : ℂ :=
  if (placesOver E ({v} : Set (Place F))).ncard = 2 then 1
  else if (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime then -1 else 0
end
end GlobalTheory.IndefiniteRowSideFullHecke.EulerProductLocalFactors


