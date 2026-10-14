-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0245
-- name    : PNT_ZeroFree_433_0245
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:37:44.5718+00:00
-- url     : https://prove2.me/theorems/3a9717c3-77e5-4bbd-a1f2-d2051916899b
-- title:
--   Zero-free region foundations: Eisenstein.AffineCuspFourier [0245]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.AffineCuspFourier
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/AffineCuspFourier.lean#L86-L652

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0044
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0133
import Definitions.Def_PNT_ZeroFree_433_0179_parallel1
import Definitions.Def_PNT_ZeroFree_433_0180_parallel1
import Definitions.Def_PNT_ZeroFree_433_0186_parallel1
import Definitions.Def_PNT_ZeroFree_433_0190_parallel2
import Definitions.Def_PNT_ZeroFree_433_0200_parallel1
import Definitions.Def_PNT_ZeroFree_433_0202_parallel1
import Definitions.Def_PNT_ZeroFree_433_0212_parallel1
import Definitions.Def_PNT_ZeroFree_433_0220_parallel1
import Definitions.Def_PNT_ZeroFree_433_0225_parallel1
import Definitions.Def_PNT_ZeroFree_433_0232_parallel1
import Definitions.Def_PNT_ZeroFree_433_0235_parallel2
import Definitions.Def_PNT_ZeroFree_433_0236_parallel2
import Definitions.Def_PNT_ZeroFree_433_0237_parallel1
import Definitions.Def_PNT_ZeroFree_433_0239_parallel1
import Definitions.Def_PNT_ZeroFree_433_0240_parallel1
import Definitions.Def_PNT_ZeroFree_433_0242_parallel2
import Definitions.Def_PNT_ZeroFree_433_0243_parallel1
import Definitions.Def_PNT_ZeroFree_433_0244_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0244_parallel2
import Definitions.Def_PNT_ZeroFree_433_0244_parallel3
import Definitions.Def_PNT_ZeroFree_433_0245_parallel1
import Definitions.Def_PNT_ZeroFree_433_0249_parallel2
import Definitions.Def_PNT_ZeroFree_433_0251_parallel1
import Definitions.Def_PNT_ZeroFree_433_0257_parallel1
import Definitions.Def_PNT_ZeroFree_433_0264_parallel2
import Definitions.Def_PNT_ZeroFree_433_0268_parallel1
import Definitions.Def_PNT_ZeroFree_433_0284_parallel1
import Definitions.Def_PNT_ZeroFree_433_0291_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/AffineCuspFourier.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

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


section
open MeasureTheory Filter
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma hasSum_diagonal_unit_integrals (u t:Eisˣ) (v:ℝ) (hv:0<v) (s freq:ℂ) (hs:2<s.re) :
    HasSum (fun p:UnitLowerData=>∫z in periodDomain,
      affineLowerTerm (t:Eis) ((↑u⁻¹:Eis)^2*(t:Eis)) z v s p.1.val p.2.val.val*
        ShortDraftTrace.breveE (-freq*z))
      (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
        integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s*
          ShortDraftTrace.breveE (-freq*z)) := by
  have hh:=(diagonalUnitCuspIndex u t).hasSum_iff.mpr
    (hasSum_integral_fixed_left_Eisenstein
      (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (t:Eis)))
      v hv s freq hs)
  apply hh.congr_fun
  intro p
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z=>by dsimp only; rw [diagonal_unit_summand])

theorem diagonal_unit_eisenstein_fourier (u t:Eisˣ) (j:ℕ) (h h1:Eis)
    (hr:(↑u⁻¹:Eis)^2*(t:Eis)=omega^j ∨ (↑u⁻¹:Eis)^2*(t:Eis)=-(omega^j))
    (hh:h=(t:Eis)*h1) (hfreq:(3:Eis)∣h1+ramifiedAffineParameter j 0)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) :
    (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (t:Eis))*
          unramifiedCubicGaussSeries s (3*((↑u⁻¹:Eis)^2*(t:Eis))^2*h1) := by
  have hsum:=hasSum_diagonal_unit_integrals u t v hv s (ninthCuspFrequency h) hs
  rw [←hsum.tsum_eq]
  have h:=affineCusp_branch_fourier h h1 (t:Eis) ((↑u⁻¹:Eis)^2*(t:Eis)) j 0 t.ne_zero
    (by simpa using hr) hh hfreq v hv s (by linarith) hsum.summable
  simpa only [GaussGeneratorTransport.norm_eisEmbedding_unit,one_pow,Complex.ofReal_one,
    Complex.one_cpow,Ideal.span_singleton_eq_top.mpr t.isUnit,Ideal.absNorm_top,map_one,Nat.cast_one,one_mul] using h

lemma onceCusp_q_norm (t:Eisˣ) (j:Fin 3) :
    ‖eisEmbedding (onceCuspScale t*omega^j.val)‖^2=3 := by
  have hw:‖eisEmbedding omega‖=1:=by
    let w:Eisˣ:=(omega_primitive.isUnit (by decide)).unit
    have hw:(w:Eis)=omega:=(omega_primitive.isUnit (by decide)).unit_spec
    rw [←hw]
    exact GaussGeneratorTransport.norm_eisEmbedding_unit w
  simp only [onceCuspScale,map_mul,norm_mul,GaussGeneratorTransport.norm_eisEmbedding_unit,
    one_mul,map_pow,norm_pow,hw,one_pow,mul_one,ramifiedEmbedding_traceLambda]
  rw [←ramifiedEmbedding_traceLambda,←norm_pow,←map_pow,ramifiedTraceLambda_square]
  norm_num [map_ofNat]

lemma onceCusp_q_absNorm (t:Eisˣ) (j:Fin 3) :
    Ideal.absNorm (Ideal.span {onceCuspScale t*omega^j.val})=3 := by
  have h:=onceCusp_q_norm t j
  rw [eisEmbedding_norm_sq_eq_absNorm_span] at h
  exact_mod_cast h

theorem diagonal_once_branch_fourier (u t:Eisˣ) (l:Fin 3) (j:ℕ) (h h1:Eis)
    (hr:(↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)=omega^j*ramifiedTraceLambda ∨
      (↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)=-(omega^j*ramifiedTraceLambda))
    (hh:h=(onceCuspScale t*omega^l.val)*h1) (hfreq:(3:Eis)∣h1+ramifiedAffineParameter j 1)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) :
    (∑'p:UnitLowerData,∫z in periodDomain,
      affineLowerTerm (onceCuspScale t*omega^l.val)
        ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)) z v s p.1.val p.2.val.val*
          ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      (3:ℂ)*(3:ℂ)^(-s)*((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (onceCuspScale t*omega^l.val))*
          unramifiedCubicGaussSeries s
            (3*((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val))^2*h1) := by
  have hsum:=(hasSum_diagonal_once_integrals u t v hv s (ninthCuspFrequency h) hs).summable.prod_factor l
  have hq:onceCuspScale t*omega^l.val≠0:=mul_ne_zero (onceCusp_scale_ne_zero t)
    (pow_ne_zero _ (omega_primitive.isUnit (by decide)).ne_zero)
  have h:=affineCusp_branch_fourier h h1 (onceCuspScale t*omega^l.val)
    ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)) j 1 hq (by simpa only [pow_one] using hr)
      hh hfreq v hv s (by linarith) hsum
  simpa only [onceCusp_q_norm,onceCusp_q_absNorm,Nat.cast_ofNat,Complex.ofReal_ofNat] using h

end


open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O


theorem diagonal_once_eisenstein_fourier (u t:Eisˣ) (j:Fin 3→ℕ) (h:Eis) (h1:Fin 3→Eis)
    (hr:∀l,(↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)=omega^(j l)*ramifiedTraceLambda ∨
      (↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)=-(omega^(j l)*ramifiedTraceLambda))
    (hh:∀l,h=(onceCuspScale t*omega^l.val)*h1 l)
    (hbase:∀l,(3:Eis)∣h+ramifiedAffineParameter (j l) 1*(onceCuspScale t*omega^l.val))
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) :
    (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv) s*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ∑l:Fin 3,if (3:Eis)∣h1 l+ramifiedAffineParameter (j l) 1 then
        (3:ℂ)*(3:ℂ)^(-s)*((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
          ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (onceCuspScale t*omega^l.val))*
            unramifiedCubicGaussSeries s
              (3*((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val))^2*h1 l) else 0 := by
  have hsum:=hasSum_diagonal_once_integrals u t v hv s (ninthCuspFrequency h) hs
  rw [←hsum.tsum_eq,hsum.summable.tsum_prod,tsum_fintype]
  apply Finset.sum_congr rfl
  intro l hl
  have hq:onceCuspScale t*omega^l.val≠0:=mul_ne_zero (onceCusp_scale_ne_zero t)
    (pow_ne_zero _ (omega_primitive.isUnit (by decide)).ne_zero)
  have h:=affineCusp_branch_fourier_masked h (h1 l) (onceCuspScale t*omega^l.val)
    ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)) (j l) 1 hq
      (by simpa only [pow_one] using hr l) (hh l) (hbase l) v hv s (by linarith)
        (hsum.summable.prod_factor l)
  simpa only [onceCusp_q_norm,onceCusp_q_absNorm,Nat.cast_ofNat,Complex.ofReal_ofNat] using h

end CubicEisenstein

end

end OAI

end


