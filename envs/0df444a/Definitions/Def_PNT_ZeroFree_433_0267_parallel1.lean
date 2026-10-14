-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0267_parallel1
-- name    : PNT_ZeroFree_433_0267_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:36:42.2703+00:00
-- url     : https://prove2.me/theorems/647138ef-1bd5-4c86-a026-dd87581a1968
-- title:
--   Zero-free region foundations: Eisenstein.EntireMellinProfile [0267_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.EntireMellinProfile
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/EntireMellinProfile.lean#L216-L467

import Definitions.Def_PNT_ZeroFree_433_0267_parallel1_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/EntireMellinProfile.lean
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


namespace CompletedGauss
open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff


theorem besselSmoothingIntegrand_finite_integrable {ι : Type*} [Fintype ι]
    (F : ℝ→ℂ) (G : ι→ℝ→ℂ) (w : ι→ℂ)
    (hFG : ∀v : ℝ,0<v→F v=∑i,w i*G i v)
    (q : ℝ) (V : ℝ→ℂ) (X σ : ℝ)
    (hG : ∀i,∀t : ℝ,MellinConvergent (G i) (2*((σ:ℂ)+t*Complex.I)))
    (hi : ∀i,Integrable (fun t : ℝ=>besselSmoothingIntegrand (G i) q V X ((σ:ℂ)+t*Complex.I))) :
    Integrable (fun t : ℝ=>besselSmoothingIntegrand F q V X ((σ:ℂ)+t*Complex.I)) := by
  have hsum := integrable_finsetSum Finset.univ (fun i _=>(hi i).const_mul (w i))
  apply hsum.congr
  filter_upwards with t
  exact (besselSmoothingIntegrand_finite_sum F G w hFG q V X _ (fun i=>hG i t)).symm

end CompletedGauss

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O


lemma primeCubicGauss_two_norm (p:Eis) (hp:Prime p) (hpp:lambda^2∣p-1)
    (h:Eis) (hph:¬p∣h) : ‖primeCubicGauss p hp hpp 2 h‖=‖eisEmbedding p‖ := by
  have he:=congrArg norm (primeCubicGauss_one_mul_two p hp hpp h hph)
  rw [norm_mul,primeCubicGauss_two_eq_star,norm_star,Complex.norm_natCast] at he
  have hn:=eisEmbedding_norm_sq_eq_absNorm_span p
  have hg:0≤‖primeCubicGauss p hp hpp 1 h‖:=norm_nonneg _
  have hr:0≤‖eisEmbedding p‖:=norm_nonneg _
  rw [primeCubicGauss_two_eq_star,norm_star]
  nlinarith


end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def threeRamifiedUnit :Eisˣ:=-(ramifiedOmegaUnit^2)
def traceRamifiedUnit :Eisˣ:=-ramifiedOmegaUnit

lemma three_eq_ramifiedUnit : (3:Eis)=(threeRamifiedUnit:Eis)*lambda^2 := by
  have hw:omega^2=-omega-1:=by linear_combination ramified_omega_relation
  have hl:lambda^2=-3*omega:=by
    change (omega-1)^2=-3*omega
    linear_combination hw
  simp only [threeRamifiedUnit,Units.val_neg,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,hl]
  calc
    (3:Eis)=3*omega^3:=by rw [omega_primitive.pow_eq_one]; ring
    _=_:=by ring

lemma trace_eq_ramifiedUnit : ramifiedTraceLambda=(traceRamifiedUnit:Eis)*lambda := by
  have hw:=ramified_omega_relation
  simp only [traceRamifiedUnit,Units.val_neg,ramifiedOmegaUnit_val]
  change 1+2*omega=-omega*(omega-1)
  linear_combination hw


end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma ramified_norm_third (u:Eisˣ) (m:ℕ) :
    ‖eisEmbedding (u.val*lambda^m)‖^(1/3:ℝ)=(3:ℝ)^((m:ℝ)/6) := by
  have hs:‖eisEmbedding (u.val*lambda^m)‖^2=(3:ℝ)^m:=by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,ramifiedElement_absNorm,Nat.cast_pow,Nat.cast_ofNat]
  calc
    _=(‖eisEmbedding (u.val*lambda^m)‖^2)^(1/6:ℝ):=by
      rw [←Real.rpow_natCast_mul (norm_nonneg _)]
      congr 1
      norm_num
    _=((3:ℝ)^m)^(1/6:ℝ):=by rw [hs]
    _=(3:ℝ)^((m:ℝ)/6):=by
      rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤3)]
      congr 1
      ring


end CubicEisenstein


end

end OAI

end


