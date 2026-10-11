-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0229_parallel1_1
-- name    : PNT_ZeroFree_433_0229_parallel1_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:20:23.999556+00:00
-- url     : https://prove2.me/theorems/763ce4f5-4e99-44a6-949a-57078ebcb56a
-- title:
--   Zero-free region foundations: Eisenstein.BesselMellinTransform [0229_parallel1_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.BesselMellinTransform
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/BesselMellinTransform.lean#L81-L192

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0083
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0087
import Definitions.Def_PNT_ZeroFree_433_0130_parallel1
import Definitions.Def_PNT_ZeroFree_433_0158_parallel1
import Definitions.Def_PNT_ZeroFree_433_0188_parallel1
import Definitions.Def_PNT_ZeroFree_433_0218_parallel1
import Definitions.Def_PNT_ZeroFree_433_0228_parallel1
import Definitions.Def_PNT_ZeroFree_433_0260_parallel1
import Definitions.Def_PNT_ZeroFree_433_0262_parallel1
import Definitions.Def_PNT_ZeroFree_433_0303_parallel1
import Definitions.Def_PNT_ZeroFree_433_0329_parallel1
import Definitions.Def_PNT_ZeroFree_433_0330_parallel1
import Definitions.Def_PNT_ZeroFree_433_0506_parallel1_1

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

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

lemma schlafliBesselK_cubic_scaled_mellin_integrable (s : ℂ) (c : ℝ)
    (hs : 1/3<s.re) (hc : 0<c) :
    IntegrableOn (fun v : ℝ => (v:ℂ)^(s-1)*schlafliBesselK (1/3) (c*v))
      (Set.Ioi 0) volume := by
  have hb : MellinConvergent (fun v => schlafliBesselK (1/3) v) s := by
    simpa only [MellinConvergent,smul_eq_mul] using schlafliBesselK_cubic_mellin_integrable s hs
  have hh := (MellinConvergent.comp_mul_left
    (f := fun v => schlafliBesselK (1/3) v) (s := s) hc).mpr hb
  simpa only [MellinConvergent,smul_eq_mul] using hh

lemma schlafliBesselK_cubic_scaled_mellin (s : ℂ) (c : ℝ)
    (hs : 1/3<s.re) (hc : 0<c) :
    (∫v : ℝ in Set.Ioi 0,(v:ℂ)^(s-1)*schlafliBesselK (1/3) (c*v)) =
      (c:ℂ)^(-s)*((2:ℂ)^(s-2)*Complex.Gamma ((s-1/3)/2)*Complex.Gamma ((s+1/3)/2)) := by
  have hh := mellin_comp_mul_left (fun v => schlafliBesselK (1/3) v) s hc
  simp only [mellin,smul_eq_mul] at hh
  rw [schlafliBesselK_cubic_mellin s hs] at hh
  exact hh

lemma source_cubic_bessel_mellin_integrable (s freq : ℂ)
    (hs : -(1/3)<s.re) (hfreq : freq≠0) :
    IntegrableOn (fun v : ℝ => (v:ℂ)^(2*s)*
      schlafliBesselK (1/3) (4*Real.pi*‖freq‖*v)) (Set.Ioi 0) volume := by
  have hc : 0<4*Real.pi*‖freq‖ := by positivity
  have ht : 1/3<(2*s+1).re := by norm_num; linarith
  simpa only [show (2*s+1:ℂ)-1=2*s by ring] using
    schlafliBesselK_cubic_scaled_mellin_integrable (2*s+1) (4*Real.pi*‖freq‖) ht hc

theorem source_cubic_bessel_mellin (s freq : ℂ)
    (hs : -(1/3)<s.re) (hfreq : freq≠0) :
    (∫v : ℝ in Set.Ioi 0,(v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*‖freq‖*v)) =
      ((2:ℂ)^(2*s-1)*Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))/
        ((4*Real.pi*‖freq‖:ℝ):ℂ)^(2*s+1) := by
  have hc : 0<4*Real.pi*‖freq‖ := by positivity
  have ht : 1/3<(2*s+1).re := by norm_num; linarith
  have hh := schlafliBesselK_cubic_scaled_mellin (2*s+1) (4*Real.pi*‖freq‖) ht hc
  rw [show (2*s+1:ℂ)-1=2*s by ring,
    show (2*s+1:ℂ)-2=2*s-1 by ring,
    show ((2*s+1:ℂ)-1/3)/2=s+1/3 by ring,
    show ((2*s+1:ℂ)+1/3)/2=s+2/3 by ring,Complex.cpow_neg] at hh
  rw [hh]
  ring

end CubicEisenstein

open scoped BigOperators Classical

namespace ShortDraftCRT

section
variable {R : Type*} [CommRing R]

theorem exists_fixed_completion (M c r a d0 : R)
    (hfixed : c∣a*d0-1) (hr : IsCoprime r (M*c)) (ha : IsCoprime a r) :
    ∃b d : R,a*d-b*(c*r)=1 ∧ M*c∣d-d0 := by
  have hcr : IsCoprime c r := hr.of_mul_right_right.symm
  obtain ⟨u,v,huv⟩ := hr
  obtain ⟨x,y,hxy⟩ := ha
  let d : R := d0*u*r+x*v*(M*c)
  have hd : M*c∣d-d0 := by
    refine ⟨v*(x-d0),?_⟩
    dsimp [d]
    linear_combination d0*huv
  have hdr : r∣d-x := by
    refine ⟨u*(d0-x),?_⟩
    dsimp [d]
    linear_combination x*huv
  have hcd : c∣a*d-1 := by
    have hdiff : c∣a*(d-d0) := dvd_mul_of_dvd_right
      ((dvd_mul_left c M).trans hd) a
    convert! dvd_add hdiff hfixed using 1 ; ring
  have hrd : r∣a*d-1 := by
    have hx : r∣a*x-1 := by
      refine ⟨-y,?_⟩
      linear_combination hxy
    have hdiff : r∣a*(d-x) := dvd_mul_of_dvd_right hdr a
    convert! dvd_add hdiff hx using 1 ; ring
  obtain ⟨b,hb⟩ := hcr.mul_dvd hcd hrd
  refine ⟨b,d,?_,hd⟩
  linear_combination hb

variable [IsDomain R]

theorem fixed_completion_congr (M c r r0 a a0 b b0 d d0 : R)
    (hc : c≠0) (hr : IsCoprime M r)
    (hdet : a*d-b*(c*r)=1) (hdet0 : a0*d0-b0*(c*r0)=1)
    (ha : M*c∣a-a0) (hd : M*c∣d-d0) (hrr : M∣r-r0) : M∣b-b0 := by
  have hprod : M*c∣a*d-a0*d0 := by
    have h1 := dvd_mul_of_dvd_left ha d
    have h2 := dvd_mul_of_dvd_right hd a0
    convert! dvd_add h1 h2 using 1 ; ring
  have hcancel : M*c∣c*(b*r-b0*r0) := by
    convert! hprod using 1
    linear_combination -hdet+hdet0
  have hbr : M∣b*r-b0*r0 := by
    rw [mul_comm M c] at hcancel
    exact (mul_dvd_mul_iff_left hc).mp hcancel
  have hsub : M∣(b-b0)*r := by
    have hsmall := dvd_mul_of_dvd_right hrr b0
    convert! dvd_sub hbr hsmall using 1 ; ring
  exact hr.dvd_of_dvd_mul_right hsub

end

open scoped BigOperators Classical Matrix

variable {R : Type*} [CommRing R] [IsDomain R]

omit [IsDomain R] in
lemma quotient_eq_of_dvd_sub (M x y : R) (h : M ∣ x-y) :
    Ideal.Quotient.mk (Ideal.span {M}) x = Ideal.Quotient.mk (Ideal.span {M}) y := by
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr h)


end ShortDraftCRT


end

end OAI

end


