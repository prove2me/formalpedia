-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0265_parallel1
-- name    : PNT_ZeroFree_433_0265_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:29:12.657477+00:00
-- url     : https://prove2.me/theorems/3df841e5-1446-4eae-a7c6-2c316866d142
-- title:
--   Zero-free region foundations: GaussSum.MellinSupport [0265_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.MellinSupport
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/MellinSupport.lean#L345-L568

import Definitions.Def_PNT_ZeroFree_433_0265_parallel1_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/MellinSupport.lean
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
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical


open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance signedOmegaUnitsFintype : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units


lemma cubicSymbol_norm_one (c n:Eis) (hn:lambda^2∣n-1) (hc:IsCoprime c n) :
    ‖eisEmbedding (symbol c n)‖=1 := by
  have hcube:(eisEmbedding (symbol c n))^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime c n hn hc,map_one]
  apply (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3:ℕ)≠0)).mp
  simpa only [norm_pow,norm_one,one_pow] using congrArg norm hcube

lemma arithmeticResidueSum_norm_mul_primary (h n:Eis) (hn:lambda^2∣n-1)
    (u:Eisˣ) (r:ℕ) (hr:2≤r) :
    ‖arithmeticResidueSum (h*n) (u.val*lambda^r)‖=
      ‖arithmeticResidueSum h (u.val*lambda^r)‖ := by
  have hc: IsCoprime (u.val*lambda^r) n :=
    (ramified_primary_coprime u r n hn).of_mul_left_right
  have he:=congrArg norm (arithmeticResidueSum_frequency_twist h (u.val*lambda^r) n
    (ramifiedElement_ne_zero u r) (ramifiedElement_level u r hr)
    ⟨hc,three_dvd_lambda_sq.trans hn⟩)
  simpa only [norm_mul,cubicSymbol_norm_one _ n hn hc,one_mul] using he

def lowRamifiedFrequency (a r:Fin 3) : Eis := omega^a.val*lambda^(r.val+2)


end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance ramifiedCoordinateUnitsFintype : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def ramifiedCoordMul (x y:ℤ×ℤ) :ℤ×ℤ := (x.1*y.1-x.2*y.2,x.1*y.2+x.2*y.1-x.2*y.2)
def ramifiedCoordPow (x:ℤ×ℤ) :ℕ→ℤ×ℤ
  | 0=>(1,0)
  | n+1=>ramifiedCoordMul (ramifiedCoordPow x n) x

def lowRamifiedQuotientCoord (a r:Fin 3) (s:Bool) (j:Fin 3) (n:Fin 5) :ℤ×ℤ :=
  let z:=ramifiedCoordMul (ramifiedCoordPow (0,1) (a.val+5-j.val))
    (ramifiedCoordPow (-1,1) (r.val+2-n.val))
  if s then z else (-z.1,-z.2)

def lowRamifiedSupport (a r:Fin 3) (p:Bool×Fin 3×Fin 5) :Prop :=
  p.2.2.val≤r.val+2 ∧
  let z:=lowRamifiedQuotientCoord a r p.1 p.2.1 p.2.2
  (3:ℤ)∣2*(p.2.1.val:ℤ)+(p.2.2.val+2:ℕ)+z.2 ∧
  (3:ℤ)∣2*(p.2.1.val:ℤ)+z.1-z.2

instance lowRamifiedSupport_decidable (a r:Fin 3) (p:Bool×Fin 3×Fin 5) :
    Decidable (lowRamifiedSupport a r p) :=
  inferInstanceAs (Decidable (p.2.2.val≤r.val+2 ∧
    (3:ℤ)∣2*(p.2.1.val:ℤ)+(p.2.2.val+2:ℕ)+(lowRamifiedQuotientCoord a r p.1 p.2.1 p.2.2).2 ∧
    (3:ℤ)∣2*(p.2.1.val:ℤ)+(lowRamifiedQuotientCoord a r p.1 p.2.1 p.2.2).1-
      (lowRamifiedQuotientCoord a r p.1 p.2.1 p.2.2).2))

def lowRamifiedSupportSet (a r:Fin 3) :Finset (Bool×Fin 3×Fin 5) :=
  Finset.univ.filter (lowRamifiedSupport a r)

lemma lowRamifiedSupport_card (a r:Fin 3) : (lowRamifiedSupportSet a r).card≤5 := by
  decide +revert

lemma lowRamifiedSupport_exponent (a r:Fin 3) (p:Bool×Fin 3×Fin 5)
    (hp:lowRamifiedSupport a r p) : 1≤p.2.2.val := by
  decide +revert

lemma ramifiedCoordMul_eval (x y:ℤ×ℤ) :
    ActualEisensteinCoordinates.eval (ramifiedCoordMul x y).1 (ramifiedCoordMul x y).2=
      ActualEisensteinCoordinates.eval x.1 x.2*ActualEisensteinCoordinates.eval y.1 y.2 :=
  (ActualEisensteinCoordinates.eval_mul _ _ _ _).symm

lemma ramifiedCoordPow_eval (x:ℤ×ℤ) (n:ℕ) :
    ActualEisensteinCoordinates.eval (ramifiedCoordPow x n).1 (ramifiedCoordPow x n).2=
      (ActualEisensteinCoordinates.eval x.1 x.2)^n := by
  induction n with
  | zero => simp [ramifiedCoordPow,ActualEisensteinCoordinates.eval]
  | succ n ih => rw [ramifiedCoordPow,ramifiedCoordMul_eval,ih,pow_succ]

lemma lowRamifiedQuotientCoord_eval (a r:Fin 3) (s:Bool) (j:Fin 3) (n:Fin 5) :
    ActualEisensteinCoordinates.eval (lowRamifiedQuotientCoord a r s j n).1
      (lowRamifiedQuotientCoord a r s j n).2=
      if s then omega^(a.val+5-j.val)*lambda^(r.val+2-n.val)
      else -(omega^(a.val+5-j.val)*lambda^(r.val+2-n.val)) := by
  have ho:ActualEisensteinCoordinates.eval 0 1=omega:=by
    simp [ActualEisensteinCoordinates.eval]; rfl
  have hl:ActualEisensteinCoordinates.eval (-1) 1=lambda:=by
    change ActualEisensteinCoordinates.eval (-1) 1=omega-1
    have he:ActualEisensteinCoordinates.eval (-1) 1=(-1:Eis)+ActualEisensteinCoordinates.eval 0 1:=by
      simp [ActualEisensteinCoordinates.eval]
    rw [he,ho]
    ring
  have he:∀x:ℤ×ℤ,ActualEisensteinCoordinates.eval (-x.1) (-x.2)=
      -ActualEisensteinCoordinates.eval x.1 x.2:=by
    intro x
    simp only [ActualEisensteinCoordinates.eval,Int.cast_neg]
    ring
  cases s <;> simp only [lowRamifiedQuotientCoord,Bool.false_eq_true,ite_false,ite_true,
    he,ramifiedCoordMul_eval,ramifiedCoordPow_eval,ho,hl]


end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance ramifiedRawWeightUnitsFintype : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def ramifiedRawWeight (h:Eis) (u:Eisˣ) (k:ℕ) :ℂ :=
  ((3^(k+2):ℕ):ℂ)^(-(4/3:ℂ))*arithmeticResidueSum h (u.val*lambda^(k+2))


lemma ramifiedRawWeight_norm_mul_primary (h n:Eis) (hn:lambda^2∣n-1) (u:Eisˣ) (k:ℕ) :
    ‖ramifiedRawWeight (h*n) u k‖=‖ramifiedRawWeight h u k‖ := by
  simp only [ramifiedRawWeight,norm_mul,
    arithmeticResidueSum_norm_mul_primary h n hn u (k+2) (by omega)]


end CubicEisenstein

end

end OAI

end


