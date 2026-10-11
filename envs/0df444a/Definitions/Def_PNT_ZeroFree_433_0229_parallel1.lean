-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0229_parallel1
-- name    : PNT_ZeroFree_433_0229_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:24:10.968147+00:00
-- url     : https://prove2.me/theorems/3cb43595-af3d-4947-b7c5-3a947265e771
-- title:
--   Zero-free region foundations: Eisenstein.BesselMellinTransform [0229_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.BesselMellinTransform
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/BesselMellinTransform.lean#L194-L379

import Definitions.Def_PNT_ZeroFree_433_0229_parallel1_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/BesselMellinTransform.lean
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

namespace ShortDraftCRT


open scoped BigOperators Classical Matrix

variable {R : Type*} [CommRing R] [IsDomain R]


theorem fixed_completion_matrix_congr (M c r r0 a a0 b b0 d d0 : R)
    (hc : c≠0) (hr : IsCoprime M r)
    (hdet : a*d-b*(c*r)=1) (hdet0 : a0*d0-b0*(c*r0)=1)
    (ha : M*c∣a-a0) (hd : M*c∣d-d0) (hrr : M∣r-r0) :
    (!![a,b;c*r,d] : Matrix (Fin 2) (Fin 2) R).map
        (Ideal.Quotient.mk (Ideal.span {M})) =
      (!![a0,b0;c*r0,d0] : Matrix (Fin 2) (Fin 2) R).map
        (Ideal.Quotient.mk (Ideal.span {M})) := by
  have hqa := quotient_eq_of_dvd_sub M a a0 ((dvd_mul_right M c).trans ha)
  have hqd := quotient_eq_of_dvd_sub M d d0 ((dvd_mul_right M c).trans hd)
  have hqb := quotient_eq_of_dvd_sub M b b0
    (fixed_completion_congr M c r r0 a a0 b b0 d d0 hc hr hdet hdet0 ha hd hrr)
  have hqc : Ideal.Quotient.mk (Ideal.span {M}) (c*r) =
      Ideal.Quotient.mk (Ideal.span {M}) (c*r0) := by
    apply quotient_eq_of_dvd_sub
    simpa only [mul_sub] using dvd_mul_of_dvd_right hrr c
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.map_apply,] <;>
    assumption

theorem exists_fixed_matrix_completion (M c a0 r0 d0 b0 : R)
    (hc : c≠0) (hdet0 : a0*d0-b0*(c*r0)=1) :
    ∀a r : R, M*c∣a-a0 → M∣r-r0 → IsCoprime r (M*c) → IsCoprime a r →
      ∃b d : R, a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧
        (!![a,b;c*r,d] : Matrix (Fin 2) (Fin 2) R).map
            (Ideal.Quotient.mk (Ideal.span {M})) =
          (!![a0,b0;c*r0,d0] : Matrix (Fin 2) (Fin 2) R).map
            (Ideal.Quotient.mk (Ideal.span {M})) := by
  intro a r ha hrr hr har
  have hbase : c ∣ a0*d0-1 := by
    refine ⟨b0*r0,?_⟩
    linear_combination hdet0
  have hfixed : c ∣ a*d0-1 := by
    have hdiff := dvd_mul_of_dvd_left ((dvd_mul_left c M).trans ha) d0
    convert! dvd_add hdiff hbase using 1 ; ring
  obtain ⟨b,d,hdet,hd⟩ := exists_fixed_completion M c r a d0 hfixed hr har
  exact ⟨b,d,hdet,hd,fixed_completion_matrix_congr M c r r0 a a0 b b0 d d0 hc
    hr.of_mul_right_left.symm hdet hdet0 ha hd hrr⟩

end ShortDraftCRT

open scoped BigOperators Classical
namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def conductorReduction (a b:Eis):
    (Eis⧸Ideal.span {a*b})→+*(Eis⧸Ideal.span {a}):=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right a b))

lemma conductorReduction_surjective (a b:Eis):Function.Surjective (conductorReduction a b):=
  Ideal.Quotient.factor_surjective _

def quotientTrace (c:Eis) (hc:c≠0):AddChar (Eis⧸Ideal.span {c}) ℂ:=
  eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc


def conductorFourier (a b:Eis) (ha:a≠0) (hb:b≠0)
    (F:(Eis⧸Ideal.span {a})→ℂ) (h:Eis):ℂ:=
  ∑'x:Eis⧸Ideal.span {a*b},F (conductorReduction a b x)*
    quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ h*x)

lemma conductorFourier_shift (a b:Eis) (ha:a≠0) (hb:b≠0)
    (F:(Eis⧸Ideal.span {a})→ℂ) (h t:Eis):
    conductorFourier a b ha hb F h=
      quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ (h*a*t))*
        conductorFourier a b ha hb F h:=by
  let q:Eis⧸Ideal.span {a*b}:=Ideal.Quotient.mk _ (a*t)
  have hq:conductorReduction a b q=0:=by
    change Ideal.Quotient.mk (Ideal.span {a}) (a*t)=0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨t,rfl⟩)
  unfold conductorFourier
  conv_lhs => rw [←(Equiv.addRight q).tsum_eq]
  rw [←tsum_mul_left]
  apply tsum_congr
  intro x
  change F (conductorReduction a b (x+q))*
    quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ h*(x+q))=_
  simp only [map_add,hq,add_zero,mul_add,AddChar.map_add_eq_mul]
  have he:Ideal.Quotient.mk (Ideal.span {a*b}) h*q=Ideal.Quotient.mk _ (h*a*t):=by
    dsimp [q]
    rw [←map_mul]
    congr 1
    ring
  rw [he]
  ring

theorem conductorFourier_support (a b:Eis) (ha:a≠0) (hb:b≠0)
    (F:(Eis⧸Ideal.span {a})→ℂ) (h:Eis)
    (hF:conductorFourier a b ha hb F h≠0):b∣h:=by
  have hphase (t:Eis):
      quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ (h*a*t))=1:=by
    apply mul_right_cancel₀ hF
    rw [one_mul,←conductorFourier_shift]
  have hz:Ideal.Quotient.mk (Ideal.span {a*b}) (h*a)=0:=by
    by_contra hn
    apply GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (a*b) (mul_ne_zero ha hb) hn
    ext x
    obtain ⟨t,rfl⟩:=Ideal.Quotient.mk_surjective x
    simpa only [AddChar.mulShift_apply,←map_mul,AddChar.one_apply,quotientTrace] using hphase t
  have hd:a*b∣h*a:=Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hd':a*b∣a*h:=by simpa only [mul_comm h a] using hd
  exact (mul_dvd_mul_iff_left ha).mp hd'


end
section

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma cubicSymbol_pow_denominator (x p:Eis) (n:ℕ):
    symbol x (p^n)=(symbol x p)^n:=by
  induction n with
  | zero=>simp
  | succ n ih=>rw [pow_succ,symbol_mul_denominator,ih,pow_succ]


end


end CubicEisenstein

end

end OAI

end


