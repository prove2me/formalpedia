-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0274_parallel3
-- name    : PNT_ZeroFree_433_0274_parallel3
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:34:42.296384+00:00
-- url     : https://prove2.me/theorems/e891c62d-72a5-48e3-ba1e-41e9a8530aa3
-- title:
--   Zero-free region foundations: Cusp.ResiduePhases [0274_parallel3]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Cusp.ResiduePhases
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Cusp/ResiduePhases.lean#L109-L627

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0008
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0038
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0133
import Definitions.Def_PNT_ZeroFree_433_0179_parallel1
import Definitions.Def_PNT_ZeroFree_433_0180_parallel1
import Definitions.Def_PNT_ZeroFree_433_0186_parallel1
import Definitions.Def_PNT_ZeroFree_433_0190_parallel2
import Definitions.Def_PNT_ZeroFree_433_0202_parallel1
import Definitions.Def_PNT_ZeroFree_433_0212_parallel1
import Definitions.Def_PNT_ZeroFree_433_0229_parallel1
import Definitions.Def_PNT_ZeroFree_433_0232_parallel1
import Definitions.Def_PNT_ZeroFree_433_0235_parallel2
import Definitions.Def_PNT_ZeroFree_433_0240_parallel1
import Definitions.Def_PNT_ZeroFree_433_0249_parallel2
import Definitions.Def_PNT_ZeroFree_433_0260_parallel2_1
import Definitions.Def_PNT_ZeroFree_433_0262_parallel1
import Definitions.Def_PNT_ZeroFree_433_0263_parallel2
import Definitions.Def_PNT_ZeroFree_433_0268_parallel1
import Definitions.Def_PNT_ZeroFree_433_0273_parallel1
import Definitions.Def_PNT_ZeroFree_433_0274_parallel1
import Definitions.Def_PNT_ZeroFree_433_0284_parallel1
import Definitions.Def_PNT_ZeroFree_433_0291_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Cusp/ResiduePhases.lean
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

namespace ShortDraftCusp
open scoped BigOperators Classical MatrixGroups Matrix

section
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase IdealGaussCRT
local notation "Eis" => ActualEisensteinCubic.O


theorem A4_phase_product {ι : Type*} [Fintype ι] (p : ι→Eis)
    [∀i,(Ideal.span {p i}).IsMaximal] (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (a b c0 d U w x:Eis) (hc0:c0≠0)
    (hdet:a*d-b*(c0*∏i,p i)=1)
    (hbez:U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1)
    (σ ε : ∀i,(Eis⧸Ideal.span {p i})ˣ) (h : ∀i,Eis⧸Ideal.span {p i})
    (ha : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) a=(σ i:Eis⧸Ideal.span {p i})*h i)
    (hε : ∀i,Ideal.Quotient.mk (Ideal.span {p i})
      (ramifiedTraceLambda^3*c0*cofactor p i)*(σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1) :
    ShortDraftTrace.breveE (-(eisEmbedding d*(eisEmbedding x/eisLam^4))/
      (eisEmbedding c0*eisEmbedding (∏i,p i))) =
    A4BadPhase c0 hc0 d U x *
      ∏i,quotientTrace (p i) (hp i)
        (((ε i:Eis⧸Ideal.span {p i})*Ideal.Quotient.mk _ x)*(h i)⁻¹) := by
  let hr : (∏i,p i)≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hs:=ShortDraftCRT.normalized_crt_pair eisEmbedding ShortDraftTrace.breveE
    ramifiedTraceLambda c0 (∏i,p i) d x U w
    (by simpa only [ramifiedEmbedding_traceLambda] using eisLam_ne_zero)
    (eisEmbedding_ne_zero hc0) (eisEmbedding_ne_zero hr) hbez
  simp only [ramifiedEmbedding_traceLambda] at hs
  rw [hs,←A4BadPhase_eq c0 hc0 d U x]
  congr 1
  have he : ShortDraftTrace.breveE (eisEmbedding (-d*w*x)/(eisLam*eisEmbedding (∏i,p i)))=
      quotientTrace (∏i,p i) hr (Ideal.Quotient.mk _ (-d*w*x)) := by
    simp only [quotientTrace,eisTraceModChar,traceModChar_mk]
    congr 1
    rw [mul_comm eisLam]
  rw [he,addChar_finite_crt_factor (fun i=>Eis⧸Ideal.span {p i})
    (productElementCRT p hcop)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [productElementCRT_mk]
  obtain ⟨t,v,hlocal⟩:=bezout_of_principal_coprime (cofactor_coprime p hcop i)
  have hc:=coordinate_trace_character p hp hcop i t v hlocal
  change coordinateAddChar (fun i=>Eis⧸Ideal.span {p i}) (productElementCRT p hcop)
    (quotientTrace (∏i,p i) hr) i (Ideal.Quotient.mk _ (-d*w*x))=_
  change coordinateAddChar (fun i=>Eis⧸Ideal.span {p i}) (productElementCRT p hcop)
    (eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates (∏i,p i) hr) i
    (Ideal.Quotient.mk _ (-d*w*x))=_
  rw [hc]
  change quotientTrace (p i) (hp i)
    (Ideal.Quotient.mk _ v*Ideal.Quotient.mk _ (-d*w*x))=_
  apply congrArg (quotientTrace (p i) (hp i))
  have hinv:=A4_complement_inverse p c0 U w hbez i v t hlocal
  have hphase:=(A4_active_local p a b c0 d hdet σ ε h ha hε x i).2
  rw [hinv] at hphase
  convert! hphase using 1 ; simp only [map_mul,map_neg] ; ring

end

open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
open CompletedGauss LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O


end ShortDraftCusp

open scoped BigOperators Classical


open scoped Classical BigOperators

namespace ShortDraftCusp
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem A4BadPhase_strong_sector (M c0 r r0 d d0 U U0 x:Eis) (hc0:c0≠0)
    (hM:ramifiedTraceLambda^3∣M) (hc:c0∣M)
    (hr:M^2∣r-r0) (hd:M*c0∣d-d0)
    (hcop:IsCoprime (ramifiedTraceLambda^3*c0) r)
    (hU:ramifiedTraceLambda^3*c0∣U*r-1)
    (hU0:ramifiedTraceLambda^3*c0∣U0*r0-1) :
    A4BadPhase c0 hc0 d U x=A4BadPhase c0 hc0 d0 U0 x := by
  obtain ⟨hrr,hdd⟩:=ShortDraftCRT.strong_sector_additive_congruences
    M ramifiedTraceLambda c0 r r0 d d0 hM hc hr hd
  apply A4BadPhase_eq_of_residue
  have he:=ShortDraftCRT.inverse_weight_residue_congr
    (ramifiedTraceLambda^3*c0) r r0 U U0 d d0 hcop hrr hU hU0 hdd
  have hn:=dvd_neg.mpr he
  convert! hn using 1 ; ring


end ShortDraftCusp

namespace CompletedGauss
open ActualEisensteinCubic CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

variable (Ψ Φ:Eis→*ℂ) (h:∀n:Eis,lambda^2∣n-1→Ψ n=Φ n)
include h


theorem completedBesselProfile_congr_primary (q:ℝ) :
    completedBesselProfile Ψ q=completedBesselProfile Φ q := by
  have he:completedMellinCoefficient Ψ=completedMellinCoefficient Φ:=
    funext (completedMellinCoefficient_congr_primary Ψ Φ h)
  simp only [completedBesselProfile,he]

end CompletedGauss


open scoped Classical BigOperators

namespace ShortDraftCRT
open ActualEisensteinCubic FiniteGaussPhase ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]


lemma finiteCrossNumerator_coprime (a c l:Eis) (p h:ι→Eis)
    (hbase:IsCoprime a c) (hpair:Pairwise (Function.onFun IsCoprime p))
    (hc:∀i,IsCoprime c (p i)) (hl:∀i,IsCoprime l (p i))
    (hh:∀i,IsCoprime (h i) (p i)) :
    IsCoprime (finiteCrossNumerator a c l p h) (c*∏i,p i) := by
  have hmodc:c∣finiteCrossNumerator a c l p h-a*(∏i,p i):=by
    refine ⟨l^2*(∑i,h i*cofactor p i),?_⟩
    unfold finiteCrossNumerator
    ring
  have hcR:IsCoprime c (∏i,p i):=IsCoprime.prod_right (fun i _=>hc i)
  have hca:IsCoprime c (finiteCrossNumerator a c l p h):=
    (CanonicalRowCompletion.isCoprime_congr_mod c _ _ hmodc).mpr (hbase.symm.mul_right hcR)
  apply hca.symm.mul_right
  apply IsCoprime.prod_right
  intro i hi
  have hcof:IsCoprime (p i) (cofactor p i):=
    IsCoprime.prod_right (fun k hk=>hpair (Ne.symm (Finset.mem_erase.mp hk).1))
  have hterm:IsCoprime (p i) (l^2*c*cofactor p i*h i):=
    (((hl i).symm.pow_right : IsCoprime (p i) (l^2)).mul_right (hc i).symm).mul_right hcof |>.mul_right (hh i).symm
  have he:=finiteCrossNumerator_local a c l p h i
  rw [←map_mul] at he
  have hd:p i∣finiteCrossNumerator a c l p h-l^2*c*cofactor p i*h i:=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  exact ((CanonicalRowCompletion.isCoprime_congr_mod (p i) _ _ hd).mpr hterm).symm

end ShortDraftCRT

end

end OAI

end


