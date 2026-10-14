-- Prove2me | Definitions.Def_PNT_Kadiri_HeckeBridge_433_0005
-- name    : PNT_Kadiri_HeckeBridge_433_0005
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-12T12:32:25.751992+00:00
-- url     : https://prove2.me/theorems/dce3a21c-f880-42a7-b7db-29d1cc35b887
-- title:
--   Complete Hecke-to-zeta bridge, part 0005
-- statement:
--   Complete proved arithmetic and analytic lemmas connecting the Eisenstein Hecke L-function to ordinary Dirichlet L-functions and the Riemann zeta function. The final bridge transfers Hecke nonvanishing in Re(s) > 7/8 to zeta nonvanishing. Original hypotheses and proof bodies are retained; no unproved theorem is imported. Source modules: OAI.NumberTheory.DirichletL.Eisenstein.CoordinateLaplacian, OAI.NumberTheory.DirichletL.GaussSum.GaussianDualLimit, OAI.NumberTheory.DirichletL.Hecke.Family
-- source:
--   OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Apache-2.0; ported to Lean 4.33.1 and pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_HeckeSevenEighths
import Definitions.Def_PNT_Kadiri_HeckeBridge_433_0004

/- Complete Hecke-to-Dirichlet and zeta bridge lemmas.
Source: OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Eisenstein.CoordinateLaplacian
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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical


open scoped BigOperators Classical


open scoped BigOperators Classical
namespace CanonicalCoefficientClass

section
open ActualEisensteinCubic



def FactorsModulo (Q : Ideal ActualEisensteinCubic.O) (Ψ : ActualEisensteinCubic.O→*ℂ) : Prop :=
  ∀x y : ActualEisensteinCubic.O,x-y∈Q → Ψ x=Ψ y


end

open ActualEisensteinCubic
open ActualEisensteinCoordinates (eval coords eval_coords)
open ShortDraftLatticeCount (qNat qO_nonneg coords_eval)

lemma norm_eval_mod (m : ℕ) (a b : ℤ) :
    (Ideal.absNorm (Ideal.span {eval a b}) : ZMod m)=
      (a : ZMod m)^2-(a : ZMod m)*(b : ZMod m)+(b : ZMod m)^2 := by
  have hi : (Ideal.absNorm (Ideal.span {eval a b}) : ℤ)=a^2-a*b+b^2 := by
    rw [←qNat_eq_absNorm_span]
    change ((ShortDraftLatticeCount.q (coords (eval a b))).toNat : ℤ)=_
    rw [Int.toNat_of_nonneg (qO_nonneg _),coords_eval]
    rfl
  have hz := congrArg (fun k : ℤ => (k : ZMod m)) hi
  push_cast at hz
  exact hz

theorem normCharacter_factorsModulo {m : ℕ} (χ : DirichletCharacter ℂ m) :
    FactorsModulo (Ideal.span {(m : ActualEisensteinCubic.O)}) (InitialMeanSquare.normCharacter χ) := by
  intro x y hxy
  obtain ⟨z,hz⟩ := Ideal.mem_span_singleton.mp hxy
  let c := (coords y).1
  let d := (coords y).2
  let e := (coords z).1
  let f := (coords z).2
  have hy : y=eval c d := (eval_coords y).symm
  have hx : x=eval (c+(m : ℤ)*e) (d+(m : ℤ)*f) := by
    calc
      x=y+(m : ActualEisensteinCubic.O)*z := by linear_combination hz
      _=eval (c+(m : ℤ)*e) (d+(m : ℤ)*f) := by
        rw [hy,←eval_coords z]
        dsimp [eval,c,d,e,f]
        push_cast
        ring
  change χ (Ideal.absNorm (Ideal.span {x}))=χ (Ideal.absNorm (Ideal.span {y}))
  congr 1
  rw [hx,hy,norm_eval_mod,norm_eval_mod]
  simp


end CanonicalCoefficientClass

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.GaussSum.GaussianDualLimit
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


namespace ShortDraftLatticeCount

open ActualEisensteinCoordinates

noncomputable def rowNormBall (H : ℕ) : Finset O := by
  classical
  let I : Finset ℤ := Finset.Icc (-((H : ℤ) + 1)) ((H : ℤ) + 1)
  exact (I.product I).image (fun v => eval v.1 v.2)

theorem mem_rowNormBall_of_qNat_le (H : ℕ) (u : O)
    (h : qNat u ≤ H) : u ∈ rowNormBall H := by
  classical
  have hq : q (coords u) ≤ (H : ℤ) := by
    change (q (coords u)).toNat ≤ H at h
    have hnonneg := qO_nonneg u
    omega
  let a := (coords u).1
  let b := (coords u).2
  have hab : a ^ 2 - a * b + b ^ 2 ≤ (H : ℤ) := hq
  obtain ⟨ha2, hb2⟩ := coordinate_squares a b (H : ℤ)
    (by positivity) hab
  have hH : (0 : ℤ) ≤ H := by positivity
  have haL : -((H : ℤ) + 1) ≤ a := by nlinarith [sq_nonneg (H : ℤ)]
  have haU : a ≤ (H : ℤ) + 1 := by nlinarith [sq_nonneg (H : ℤ)]
  have hbL : -((H : ℤ) + 1) ≤ b := by nlinarith [sq_nonneg (H : ℤ)]
  have hbU : b ≤ (H : ℤ) + 1 := by nlinarith [sq_nonneg (H : ℤ)]
  unfold rowNormBall
  apply Finset.mem_image.mpr
  refine ⟨coords u, ?_, eval_coords u⟩
  exact Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨haL, haU⟩,
     Finset.mem_Icc.mpr ⟨hbL, hbU⟩⟩

theorem mem_rowNormBall_of_absNorm_le (H : ℕ) (u : O)
    (h : Ideal.absNorm (Ideal.span {u}) ≤ H) :
    u ∈ rowNormBall H := by
  apply mem_rowNormBall_of_qNat_le
  simpa only [ActualEisensteinCubic.qNat_eq_absNorm_span] using h

end ShortDraftLatticeCount


end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Hecke.Family
section
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeFamily


def Character.ofResidue (M : Ideal O) (hM : M ≠ ⊥)
    (χ : MulChar (O ⧸ M) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk M (u : O)) = 1) : Character := by
  letI : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient hM
  letI : Fintype (O ⧸ M) := Fintype.ofFinite _
  exact {
    modulus := M
    modulus_ne_bot := hM
    residue := χ
    unit_trivial := hu
    period := Fintype.card (O ⧸ M)
    period_pos := Fintype.card_pos
    period_mem := Ideal.Quotient.eq_zero_iff_mem.mp (by
      simpa only [map_natCast] using Nat.cast_card_eq_zero (O ⧸ M)) }


theorem elementCoeff_mul (χ : Character) (z w : O) :
    elementCoeff χ (z * w) = elementCoeff χ z * elementCoeff χ w := by
  simp [elementCoeff, map_mul]

theorem elementCoeff_unit_mul (χ : Character) (u : Oˣ) (z : O) :
    elementCoeff χ ((u : O) * z) = elementCoeff χ z := by
  rw [elementCoeff_mul]
  have hu : elementCoeff χ (u : O) = 1 := χ.unit_trivial u
  rw [hu, one_mul]

theorem quotient_period (χ : Character) :
    Ideal.Quotient.mk χ.modulus (χ.period : O) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr χ.period_mem

theorem elementCoeff_add_period_mul (χ : Character) (z w : O) :
    elementCoeff χ (z + (χ.period : O) * w) = elementCoeff χ z := by
  simp [elementCoeff, map_add, map_mul, quotient_period χ]

theorem periodicCoeff_eq_elementCoeff (χ : Character) (n : ℤ × ℤ) :
    HeckeTheta.periodicCoeff (coefficients χ) n =
      elementCoeff χ (coordinateElement n.1 n.2) := by
  obtain ⟨p, rfl⟩ := (HeckeTheta.residueEquiv χ.period).symm.surjective n
  simp only [HeckeTheta.periodicCoeff, Equiv.apply_symm_apply, coefficients]
  change elementCoeff χ (coordinateElement p.1.1 p.1.2) =
    elementCoeff χ (coordinateElement (p.2.1 * (χ.period : ℤ) + p.1.1)
      (p.2.2 * (χ.period : ℤ) + p.1.2))
  have heq : coordinateElement (p.2.1 * (χ.period : ℤ) + p.1.1)
      (p.2.2 * (χ.period : ℤ) + p.1.2) =
      coordinateElement p.1.1 p.1.2 + (χ.period : O) *
        ((p.2.1 : O) + (p.2.2 : O) * omega) := by
    unfold coordinateElement
    push_cast
    ring
  rw [heq, elementCoeff_add_period_mul]


theorem continuedLattice_differentiableAt (χ : Character) {s : ℂ}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ ∑ a, (coefficients χ) a = 0) :
    DifferentiableAt ℂ (continuedLattice χ) s :=
  HeckeTheta.latticeL_differentiableAt (coefficients χ) hs₀ hs₁

end SevenEighths.HeckeFamily

end

end OAI

end


