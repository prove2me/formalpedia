-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0046
-- name    : PNT_ZeroFree_433_0046
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T14:58:58.457416+00:00
-- url     : https://prove2.me/theorems/98bb7ff7-0e41-47d5-ade6-3b524704c07e
-- title:
--   Zero-free region foundations: GaussSum.SquarePhaseFactorization [0046]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.SquarePhaseFactorization
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/SquarePhaseFactorization.lean#L453-L583

import Definitions.Def_PNT_ZeroFree_433_0046_2

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/SquarePhaseFactorization.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators

namespace ActualEisensteinCubic


end ActualEisensteinCubic

open scoped BigOperators Classical

namespace IdealGaussCRT


end IdealGaussCRT

namespace QuadraticGaussRay


open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates


theorem I_zpow_eq_of_mod_four {a b : ℤ} (h : (a : ZMod 4) = b) :
    Complex.I ^ a = Complex.I ^ b := by
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub b a 4).mp h.symm
  have ha : a = b + 4 * k := by omega
  rw [ha, zpow_add₀ Complex.I_ne_zero, zpow_mul]
  norm_num

theorem fourTerms_eq_of_mod_four {a b c d : ℤ}
    (ha : (a : ZMod 4) = c) (hb : (b : ZMod 4) = d) :
    breveGaussianFourTerms a b = breveGaussianFourTerms c d := by
  have hn : ((-b : ℤ) : ZMod 4) = (-d : ℤ) := by simpa using congrArg Neg.neg hb
  have hs : ((b-a : ℤ) : ZMod 4) = (d-c : ℤ) := by
    push_cast
    rw [ha, hb]
  rw [breveGaussianFourTerms_formula, breveGaussianFourTerms_formula,
    I_zpow_eq_of_mod_four ha, I_zpow_eq_of_mod_four hn, I_zpow_eq_of_mod_four hs]

def quadraticRayValue (r : EisensteinEPrimaryPhase.Coord) : ℂ :=
  breveGaussianFourTerms (r.1.val : ℤ) (r.2.val : ℤ)

theorem quadraticGammaO_eq_rayValue (c : O) (hc : c ≠ 0) :
    quadraticGammaO c hc = quadraticRayValue (residue c) := by
  have h := quadraticGammaO_eq_fourTerms (coords c).1 (coords c).2 (by rwa [eval_coords])
  have h' : quadraticGammaO c hc = breveGaussianFourTerms (coords c).1 (coords c).2 := by
    simpa only [eval_coords] using h
  rw [h']
  unfold quadraticRayValue residue
  exact fourTerms_eq_of_mod_four (by simp) (by simp)

theorem quadraticGammaO_eq_of_residue_eq (c d : O) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : residue c = residue d) : quadraticGammaO c hc = quadraticGammaO d hd := by
  rw [quadraticGammaO_eq_rayValue, quadraticGammaO_eq_rayValue, h]

theorem canonicalProductGauss_three_eq_rayValue
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) :
    canonicalProductGauss p hp hcop hgood (fun _ => 3) =
      quadraticRayValue (residue (∏ i, p i)) := by
  rw [canonicalProductGauss_three_eq_quadraticGamma p hp hcop hgood hchar,
    quadraticGammaO_eq_rayValue]

open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates

theorem fixed_two_mk_eq_residue_lift (c : O) :
    Ideal.Quotient.mk cubicTwoIdeal c =
      Ideal.Quotient.mk cubicTwoIdeal (lift (residue c)) := by
  obtain ⟨z, hz⟩ := congr_mod_four_of_residue_eq (residue_lift (residue c)).symm
  apply Ideal.Quotient.eq.mpr
  rw [cubicTwoIdeal, Ideal.mem_span_singleton]
  refine ⟨(-2 : O) * z, ?_⟩
  calc
    c - lift (residue c) = 4 * z := hz
    _ = (-2 : O) * (-2 * z) := by ring

def fixedGValue (r : EisensteinEPrimaryPhase.Coord) : ℂ :=
  (eisEmbedding (cubicChar cubicTwoIdeal cubicTwoIdeal_good
    (Ideal.Quotient.mk cubicTwoIdeal (lift r))))⁻¹ * quadraticRayValue r

theorem residue_eq_of_four_dvd_sub (c d : O) (h : (4 : O) ∣ c - d) :
    residue c = residue d := by
  obtain ⟨z, hz⟩ := h
  have he : c = eval ((coords d).1 + 4 * (coords z).1)
      ((coords d).2 + 4 * (coords z).2) := by
    calc
      c = d + 4 * z := by linear_combination hz
      _ = eval (coords d).1 (coords d).2 + 4 * eval (coords z).1 (coords z).2 := by
        rw [eval_coords, eval_coords]
      _ = _ := by simp only [eval]; push_cast; ring
  rw [he, residue_eval]
  simp only [residue, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
    show (4 : ZMod 4) = 0 by decide, zero_mul, add_zero]

theorem residue_eq_of_quotient_four_eq (c d : O)
    (h : Ideal.Quotient.mk (Ideal.span {(4 : O)}) c =
      Ideal.Quotient.mk (Ideal.span {(4 : O)}) d) : residue c = residue d :=
  residue_eq_of_four_dvd_sub c d (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h))

def residueQuotientFour : (O ⧸ Ideal.span {(4 : O)}) → EisensteinEPrimaryPhase.Coord :=
  Quotient.lift residue (fun c d h => residue_eq_of_quotient_four_eq c d (Quotient.sound h))

@[simp] theorem residueQuotientFour_mk (c : O) :
    residueQuotientFour (Ideal.Quotient.mk (Ideal.span {(4 : O)}) c) = residue c := rfl

def fixedGQuotientValue (r : O ⧸ Ideal.span {(4 : O)}) : ℂ :=
  fixedGValue (residueQuotientFour r)

theorem canonicalProductG_eq_fixedGValue
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductG p hp hcop hgood = fixedGValue (residue (∏ i, p i)) := by
  rw [canonicalProductG,
    canonicalSextic_four_prod_eq_fixed_two Finset.univ (fun i => Ideal.span {p i}) hgood p
      (fun i _ => rfl) (fun i _ => hprimary i),
    canonicalProductGauss_three_eq_rayValue p hp hcop hgood hchar,
    fixed_two_mk_eq_residue_lift]
  rfl

theorem canonicalProductG_eq_of_residue_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (q : κ → O) (hq : ∀ i, q i ≠ 0) [∀ i, (Ideal.span {q i}).IsMaximal]
    (kcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {q i})))
    (kgood : ∀ i, lambda ∉ Ideal.span {q i})
    (kchar : ∀ i, ringChar (O ⧸ Ideal.span {q i}) ≠ 2)
    (kprimary : ∀ i, lambda ^ 2 ∣ q i - 1)
    (hres : residue (∏ i, p i) = residue (∏ i, q i)) :
    canonicalProductG p hp hcop hgood = canonicalProductG q hq kcop kgood := by
  rw [canonicalProductG_eq_fixedGValue p hp hcop hgood hchar hprimary,
    canonicalProductG_eq_fixedGValue q hq kcop kgood kchar kprimary, hres]

theorem canonicalProductG_eq_fixed_quotient
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductG p hp hcop hgood =
      fixedGQuotientValue (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i, p i)) :=
  canonicalProductG_eq_fixedGValue p hp hcop hgood hchar hprimary

end QuadraticGaussRay

end

end OAI

end


