-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:11.795657+00:00
-- url     : https://prove2.me/theorems/18fb39da-b9f1-47da-aa0f-7793f0a339e8
-- title:
--   PSpec Chart Iso
-- statement:
--   Definitions and structural lemmas for PSpec Chart Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
set_option linter.unusedSectionVars false
namespace SpecChart
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
  (j : Fin n)
abbrev FreePar : Type := (Fin e × {m : Fin n // m ≠ j}) ⊕ {m : Fin n // m ≠ j}
def FreePar.val : FreePar e j → Par e n
  | .inl (i, m) => .inl (i, m.1)
  | .inr m => .inr m.1
abbrev Base : Type := ChartDomain.Base (integralModel I) j
abbrev Poly : Type := MvPolynomial (FreePar e j) (Base I j)
def toBase : MvPolynomial (Fin n) (𝓞 K) →+* Base I j :=
  (algebraMap _ (Base I j)).comp (Ideal.Quotient.mk (integralModel I))
def cx (l : Fin n) : Poly e I j := C (toBase I j (X l))
def cinv : Poly e I j := C (IsLocalization.Away.invSelf (Ideal.Quotient.mk (integralModel I) (X j)))
def val : Par e n → Poly e I j
  | .inl (i, l) => if h : l = j then -(cinv e I j * ∑ m : {m : Fin n // m ≠ j}, X (.inl (i, m)) * cx e I j m)
      else X (.inl (i, ⟨l, h⟩))
  | .inr l => if h : l = j then cinv e I j * (1 - ∑ m : {m : Fin n // m ≠ j}, X (.inr m) * cx e I j m)
      else X (.inr ⟨l, h⟩)
def σ : MvPolynomial (Par e n) (𝓞 K) →+* Poly e I j :=
  eval₂Hom (C.comp ((toBase I j).comp C)) (val e I j)
variable (W : Ideal (MvPolynomial (Fin n) (𝓞 K)))
def Wb : Ideal (Base I j) :=
  (W.map (Ideal.Quotient.mk (integralModel I))).map (algebraMap _ (Base I j))
def Q : Ideal (Poly e I j) :=
  RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk (Wb I j W)) :
    Poly e I j →+* MvPolynomial (FreePar e j) (Base I j ⧸ Wb I j W))
variable {I W}
variable {v : HeightOneSpectrum (𝓞 K)}
theorem toSecB_le : integralModel I ≤ RingHom.ker (toSecB e I v) := fun g hg => by
  rw [RingHom.mem_ker, toSecB, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg))
variable (𝔫 : Ideal (SecB e I v)) [𝔫.IsPrime]
def quotToBn : MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I →+* Localization.AtPrime 𝔫 :=
  Ideal.Quotient.lift _ ((algebraMap (SecB e I v) (Localization.AtPrime 𝔫)).comp (toSecB e I v))
    (fun g hg => by rw [RingHom.comp_apply, RingHom.mem_ker.mp (toSecB_le e hg), map_zero])
theorem quotToBn_mk (g : MvPolynomial (Fin n) (𝓞 K)) :
    quotToBn e 𝔫 (Ideal.Quotient.mk _ g) = algebraMap _ (Localization.AtPrime 𝔫) (toSecB e I v g) :=
  Ideal.Quotient.lift_mk _ _ _
def parB (p : Par e n) : Localization.AtPrime 𝔫 :=
  algebraMap (SecB e I v) _ (algebraMap (ParDVR e n v) (SecB e I v) (parY e n v p))
variable {e j 𝔫}
def baseToBn (hj : toSecB e I v (X j) ∉ 𝔫) : Base I j →+* Localization.AtPrime 𝔫 :=
  IsLocalization.Away.lift (Ideal.Quotient.mk (integralModel I) (X j)) (g := quotToBn e 𝔫)
    (by
      rw [quotToBn_mk]
      exact IsLocalization.map_units (Localization.AtPrime 𝔫) (⟨toSecB e I v (X j), hj⟩ : 𝔫.primeCompl))
def Φ (hj : toSecB e I v (X j) ∉ 𝔫) : Poly e I j →+* Localization.AtPrime 𝔫 :=
  eval₂Hom (baseToBn hj) fun y => parB e 𝔫 (FreePar.val e j y)
end SpecChart
end
end GroundTheory.Heights₂.Heights.Vertical


