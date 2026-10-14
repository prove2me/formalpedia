-- Prove2me | Definitions.Def_PNT_Kadiri_HeckeBridge_433_0007
-- name    : PNT_Kadiri_HeckeBridge_433_0007
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-12T12:39:10.852989+00:00
-- url     : https://prove2.me/theorems/843bdd92-6166-477b-81a2-e44d4c0cb70d
-- title:
--   Complete Hecke-to-zeta bridge, part 0007
-- statement:
--   Complete proved arithmetic and analytic lemmas connecting the Eisenstein Hecke L-function to ordinary Dirichlet L-functions and the Riemann zeta function. The final bridge transfers Hecke nonvanishing in Re(s) > 7/8 to zeta nonvanishing. Original hypotheses and proof bodies are retained; no unproved theorem is imported. Source modules: OAI.NumberTheory.DirichletL.Eisenstein.FourierCoefficients, OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson, OAI.NumberTheory.DirichletL.Hecke.Coordinates, OAI.NumberTheory.DirichletL.Hecke.FamilySeries
-- source:
--   OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Apache-2.0; ported to Lean 4.33.1 and pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_HeckeSevenEighths
import Definitions.Def_PNT_Kadiri_HeckeBridge_433_0006

/- Complete Hecke-to-Dirichlet and zeta bridge lemmas.
Source: OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Eisenstein.FourierCoefficients
section
namespace OAI

noncomputable section

namespace CubicEisenstein

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


section
open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal Matrix

open ActualEisensteinCubic ConcreteTraceCRT

instance p2mAnonymous_PNT_Kadiri_HeckeBridge_433_0007_1 : DiscreteTopology periodLattice := by unfold periodLattice; infer_instance
instance p2mAnonymous_PNT_Kadiri_HeckeBridge_433_0007_2 : IsZLattice ℝ periodLattice := by unfold periodLattice; infer_instance

lemma summable_embedding_rpow (k : ℝ) (hk : k < -2) :
    Summable (fun n : O => ‖eisEmbedding n‖^k) := by
  have hrank : Module.finrank ℤ periodLattice=2 := by
    rw [ZLattice.rank ℝ periodLattice,Complex.finrank_real_complex]
  have hs := ZLattice.summable_norm_rpow periodLattice k (by rw [hrank]; norm_num; exact hk)
  have hcomp := periodEquiv.summable_iff.mpr hs
  have hscale := hcomp.mul_left (((3:ℝ)^k)⁻¹)
  apply hscale.congr
  intro n
  change ((3:ℝ)^k)⁻¹*‖(3:ℂ)*eisEmbedding n‖^k=‖eisEmbedding n‖^k
  rw [norm_mul,show ‖(3:ℂ)‖=(3:ℝ) by norm_num,
    Real.mul_rpow (by norm_num) (norm_nonneg _)]
  rw [← mul_assoc,inv_mul_cancel₀ (Real.rpow_pos_of_pos (by norm_num) k).ne',one_mul]


end


end CubicEisenstein

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson
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


open scoped BigOperators Classical SchwartzMap ContDiff

namespace ActualEisensteinCubic
open ConcreteTraceCRT EisensteinSchwartzPoisson


theorem eisEmbedding_norm_sq_eq_absNorm_span (a : O) :
    ‖eisEmbedding a‖ ^ 2 = (Ideal.absNorm (Ideal.span {a}) : ℝ) := by
  open ActualEisensteinCoordinates ShortDraftLatticeCount in
    have hnorm : ‖eisEmbedding a‖ ^ 2 = (q (coords a) : ℝ) := by
      simpa only [eval_coords, q, pow_two] using
        eisEmbedding_eval_norm_sq (coords a).1 (coords a).2
    have hNat : (qNat a : ℤ) = q (coords a) := Int.toNat_of_nonneg (qO_nonneg a)
    have hNatR := congrArg (fun n : ℤ => (n : ℝ)) hNat
    simp only [Int.cast_natCast] at hNatR
    rw [← qNat_eq_absNorm_span, hNatR]
    exact hnorm


end ActualEisensteinCubic

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Hecke.Coordinates
section
namespace OAI

noncomputable section
namespace SevenEighths.HeckeCoordinates
open HeckeFamily

private instance p2mAnonymous_PNT_Kadiri_HeckeBridge_433_0007_3 : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
private theorem hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta 3 ℚ K) 3 := IsCyclotomicExtension.zeta_spec 3 ℚ K
private def pb : PowerBasis ℤ O := hζ.integralPowerBasis

private theorem pb_dim : pb.dim = 2 := by
  simp [pb, Nat.totient_prime Nat.prime_three]

private theorem pb_gen : pb.gen = HeckeFamily.omega := hζ.integralPowerBasis_gen

theorem coordinateElement_surjective :
    Function.Surjective (fun n : ℤ × ℤ => coordinateElement n.1 n.2) := by
  intro x
  let i0 : Fin pb.dim := ⟨0, by rw [pb_dim]; decide⟩
  let i1 : Fin pb.dim := ⟨1, by rw [pb_dim]; decide⟩
  let a : ℤ := (pb.basis.repr x) i0
  let b : ℤ := (pb.basis.repr x) i1
  refine ⟨(a,b), ?_⟩
  have hsum := pb.basis.sum_repr x
  have huniv : (Finset.univ : Finset (Fin pb.dim)) = {i0, i1} := by
    ext i
    have hi : i.val < 2 := by simpa only [pb_dim] using i.isLt
    have hv : i.val = 0 ∨ i.val = 1 := by omega
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases hv with h | h
    · left; exact Fin.ext h
    · right; exact Fin.ext h
  rw [huniv] at hsum
  have hne : i0 ≠ i1 := by decide
  have hnot : i0 ∉ ({i1} : Finset (Fin pb.dim)) := by
    simpa only [Finset.mem_singleton] using hne
  rw [Finset.sum_insert hnot, Finset.sum_singleton] at hsum
  simp only [pb.basis_eq_pow] at hsum
  simpa [a, b, i0, i1, pb_gen, coordinateElement, smul_eq_mul, mul_comm] using hsum

def intQuotientHom (χ : Character) : ℤ →+ (O ⧸ χ.modulus) :=
  (Ideal.Quotient.mk χ.modulus).toAddMonoidHom.comp (Int.castAddHom O)

def zmodQuotientHom (χ : Character) : ZMod χ.period →+ (O ⧸ χ.modulus) :=
  ZMod.lift χ.period ⟨intQuotientHom χ, by
    change Ideal.Quotient.mk χ.modulus ((χ.period : ℤ) : O) = 0
    simpa only [Int.cast_natCast] using quotient_period χ⟩

@[simp] theorem zmodQuotientHom_intCast (χ : Character) (a : ℤ) :
    zmodQuotientHom χ (a : ZMod χ.period) = Ideal.Quotient.mk χ.modulus (a : O) :=
  ZMod.lift_coe _ _ _

@[simp] theorem zmodQuotientHom_natCast (χ : Character) (a : ℕ) :
    zmodQuotientHom χ (a : ZMod χ.period) = Ideal.Quotient.mk χ.modulus (a : O) := by
  simpa only [Int.cast_natCast] using zmodQuotientHom_intCast χ (a : ℤ)

def coordinateQuotientHom (χ : Character) :
    (ZMod χ.period × ZMod χ.period) →+ (O ⧸ χ.modulus) where
  toFun p := zmodQuotientHom χ p.1 +
    zmodQuotientHom χ p.2 * Ideal.Quotient.mk χ.modulus HeckeFamily.omega
  map_zero' := by simp
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring

@[simp] theorem coordinateQuotientHom_intCast (χ : Character) (a b : ℤ) :
    coordinateQuotientHom χ (a, b) =
      Ideal.Quotient.mk χ.modulus (coordinateElement a b) := by
  simp only [coordinateQuotientHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    zmodQuotientHom_intCast, coordinateElement, map_add, map_mul]

theorem coordinateQuotientHom_surjective (χ : Character) :
    Function.Surjective (coordinateQuotientHom χ) := by
  intro x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨⟨a,b⟩, hab⟩ := coordinateElement_surjective z
  change coordinateElement a b = z at hab
  exact ⟨(a,b), by rw [coordinateQuotientHom_intCast, hab]⟩

theorem coefficients_eq_quotient_character (χ : Character)
    (a : Fin χ.period × Fin χ.period) :
    coefficients χ a = χ.residue (coordinateQuotientHom χ (a.1, a.2)) := by
  simp [HeckeFamily.coefficients, HeckeFamily.elementCoeff, coordinateQuotientHom,
    coordinateElement]

end SevenEighths.HeckeCoordinates

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Hecke.FamilySeries
section
namespace OAI

noncomputable section


namespace SevenEighths.HeckeFamily
open EisensteinTheta

theorem continuedLattice_hasSum (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℤ × ℤ => elementCoeff χ (coordinateElement n.1 n.2) /
      (normForm n.1 n.2 : ℂ) ^ s) (continuedLattice χ s) := by
  simpa only [periodicCoeff_eq_elementCoeff, continuedLattice] using HeckeTheta.latticeL_hasSum (coefficients χ) hs


end SevenEighths.HeckeFamily

end

end OAI

end


