-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0274_parallel1
-- name    : PNT_ZeroFree_433_0274_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:20:46.08878+00:00
-- url     : https://prove2.me/theorems/6e66bf4f-1c34-4255-bf09-8e2f99d0ca9f
-- title:
--   Zero-free region foundations: Cusp.ResiduePhases [0274_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Cusp.ResiduePhases
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Cusp/ResiduePhases.lean#L83-L602

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0008
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0038
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0096
import Definitions.Def_PNT_ZeroFree_433_0109
import Definitions.Def_PNT_ZeroFree_433_0138_parallel1
import Definitions.Def_PNT_ZeroFree_433_0185_parallel2
import Definitions.Def_PNT_ZeroFree_433_0229_parallel1
import Definitions.Def_PNT_ZeroFree_433_0240_parallel1
import Definitions.Def_PNT_ZeroFree_433_0260_parallel2_1

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

lemma A4_bad_modulus_ne_zero (c0:Eis) (hc0:c0≠0) : ramifiedTraceLambda^3*c0≠0 := by
  apply mul_ne_zero _ hc0
  apply pow_ne_zero
  intro hz
  have he:=ramifiedEmbedding_traceLambda
  rw [hz,map_zero] at he
  exact eisLam_ne_zero he.symm

def A4BadPhase (c0:Eis) (hc0:c0≠0) (d U x:Eis) : ℂ :=
  quotientTrace (ramifiedTraceLambda^3*c0) (A4_bad_modulus_ne_zero c0 hc0)
    (Ideal.Quotient.mk _ (-d*U*x))

lemma A4BadPhase_eq (c0:Eis) (hc0:c0≠0) (d U x:Eis) :
    A4BadPhase c0 hc0 d U x =
      ShortDraftTrace.breveE (-(eisEmbedding d*eisEmbedding U*(eisEmbedding x/eisLam^4))/eisEmbedding c0) := by
  change ShortDraftTrace.breveE
    (eisEmbedding (-d*U*x)/(eisEmbedding (ramifiedTraceLambda^3*c0)*eisLam))=_
  simp only [map_mul,map_pow,map_neg,ramifiedEmbedding_traceLambda]
  congr 1
  field_simp [eisLam_ne_zero,eisEmbedding_ne_zero hc0]

noncomputable local instance A4phaseField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance A4phaseFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _


end

open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
open CompletedGauss LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance A4frequencyField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance A4frequencyFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _


lemma A4BadPhase_eq_of_residue (c0:Eis) (hc0:c0≠0) (d U d' U' x:Eis)
    (hres:ramifiedTraceLambda^3*c0∣d*U-d'*U') :
    A4BadPhase c0 hc0 d U x=A4BadPhase c0 hc0 d' U' x := by
  unfold A4BadPhase
  congr 1
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_singleton.mpr
  have hd:=dvd_mul_of_dvd_left hres (-x)
  convert! hd using 1 ; ring

lemma A4BadPhase_norm (c0:Eis) (hc0:c0≠0) (d U x:Eis) :
    ‖A4BadPhase c0 hc0 d U x‖=1 := by
  rw [A4BadPhase_eq]
  exact breveE_norm _

end ShortDraftCusp

open scoped BigOperators Classical


namespace LocalReflectionBrackets
open ActualEisensteinCubic CubicEisenstein IdealGaussCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance canonicalShiftField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance canonicalShiftFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _


end LocalReflectionBrackets

namespace FiniteGaussPhase

section
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT IdealGaussCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem exists_product_trace_shifts {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i}))) :
    ∃k : ∀i,(Eis⧸Ideal.span {p i})ˣ,
      (∀i,Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)*(k i:Eis⧸Ideal.span {p i})=1) ∧
      ∀i,coordinateAddChar (fun i=>Eis⧸Ideal.span {p i}) (productElementCRT p hcop)
        (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))) i=
          (quotientTrace (p i) (hp i)).mulShift (k i:Eis⧸Ideal.span {p i}) := by
  have hone (i : ι) : ∃k : (Eis⧸Ideal.span {p i})ˣ,
      Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)*(k:Eis⧸Ideal.span {p i})=1 ∧
      coordinateAddChar (fun i=>Eis⧸Ideal.span {p i}) (productElementCRT p hcop)
        (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))) i=
          (quotientTrace (p i) (hp i)).mulShift (k:Eis⧸Ideal.span {p i}) := by
    obtain ⟨u,v,hbez⟩:=bezout_of_principal_coprime (cofactor_coprime p hcop i)
    have hv : Ideal.Quotient.mk (Ideal.span {p i}) v*
        Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)=1 := by
      simpa only [mul_comm] using bezout_inverse_left hbez
    refine ⟨Units.mkOfMulEqOne _ _ hv,?_,?_⟩
    · simpa only [Units.val_mkOfMulEqOne,mul_comm] using hv
    · exact coordinate_trace_character p hp hcop i u v hbez
  choose k hki hkψ using hone
  exact ⟨k,hki,hkψ⟩

noncomputable def productTraceShift {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i}))) :
    ∀i,(Eis⧸Ideal.span {p i})ˣ :=
  (exists_product_trace_shifts p hp hcop).choose

lemma productTraceShift_inverse {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i}))) (i:ι) :
    Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)*
      (productTraceShift p hp hcop i:Eis⧸Ideal.span {p i})=1 :=
  (exists_product_trace_shifts p hp hcop).choose_spec.1 i

lemma productTraceShift_character {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i}))) (i:ι) :
    coordinateAddChar (fun i=>Eis⧸Ideal.span {p i}) (productElementCRT p hcop)
      (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))) i=
        (quotientTrace (p i) (hp i)).mulShift
          (productTraceShift p hp hcop i:Eis⧸Ideal.span {p i}) :=
  (exists_product_trace_shifts p hp hcop).choose_spec.2 i

end

open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT IdealGaussCRT
local notation "Eis" => ActualEisensteinCubic.O


end FiniteGaussPhase

namespace LocalReflectionBrackets
open ActualEisensteinCubic CubicEisenstein IdealGaussCRT CompletedGauss FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance productReflectionField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance productReflectionFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _


end LocalReflectionBrackets

open scoped Classical BigOperators

namespace ShortDraftCusp
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O


def A4PhaseFromResidue (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {ramifiedTraceLambda^3*c0}) (x:Eis) : ℂ :=
  quotientTrace (ramifiedTraceLambda^3*c0) (A4_bad_modulus_ne_zero c0 hc0)
    (v*Ideal.Quotient.mk _ x)

lemma A4BadPhase_as_fixed_residue (c0:Eis) (hc0:c0≠0) (d U:Eis) :
    A4BadPhase c0 hc0 d U=
      A4PhaseFromResidue c0 hc0 (Ideal.Quotient.mk _ (-d*U)) := by
  funext x
  simp only [A4BadPhase,A4PhaseFromResidue,map_mul]

lemma A4PhaseFromResidue_range (c0:Eis) (hc0:c0≠0) :
    (Set.range (A4PhaseFromResidue c0 hc0)).Finite ∧
      (Set.range (A4PhaseFromResidue c0 hc0)).ncard≤
        Ideal.absNorm (Ideal.span {ramifiedTraceLambda^3*c0}) := by
  let:Finite (Eis⧸Ideal.span {ramifiedTraceLambda^3*c0}):=
    finite_quotient_span (A4_bad_modulus_ne_zero c0 hc0)
  refine ⟨Set.finite_range _,?_⟩
  have h:=Set.ncard_image_le (s:=Set.univ) (f:=A4PhaseFromResidue c0 hc0)
  simpa only [Set.image_univ,Set.ncard_univ,Ideal.absNorm_apply,Submodule.cardQuot_apply] using h

end ShortDraftCusp

namespace CompletedGauss
open ActualEisensteinCubic CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

variable (Ψ Φ:Eis→*ℂ) (h:∀n:Eis,lambda^2∣n-1→Ψ n=Φ n)
include h

lemma columnWeight_congr_primary (I:Ideal Eis) : columnWeight Ψ I=columnWeight Φ I := by
  by_cases hi:primaryGenerator I=0
  · simp only [columnWeight,squarefreeGaussCoefficient,hi,ne_eq,not_true_eq_false,and_false,
      dite_false,zero_mul]
  · rw [columnWeight,columnWeight,h _ (primaryGenerator_spec I hi).2]

lemma cubeWeight_congr_primary (I:Ideal Eis) : cubeWeight Ψ I=cubeWeight Φ I := by
  change star (FiniteGaussPhase.angularFactor (primaryGenerator I))^3*Ψ (primaryGenerator I)^3/
      (Ideal.absNorm I:ℂ)=star (FiniteGaussPhase.angularFactor (primaryGenerator I))^3*Φ (primaryGenerator I)^3/
      (Ideal.absNorm I:ℂ)
  by_cases hi:primaryGenerator I=0
  · simp only [hi,FiniteGaussPhase.angularFactor,map_zero,norm_zero,Complex.ofReal_zero,
      div_zero,star_zero,zero_pow (by decide : (3:ℕ)≠0),zero_mul,zero_div]
  · rw [h _ (primaryGenerator_spec I hi).2]

theorem completedT_congr_primary (W:ℝ→ℂ) (X:ℝ) : completedT Ψ W X=completedT Φ W X := by
  unfold completedT
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  rw [summand,summand,columnWeight_congr_primary Ψ Φ h,cubeWeight_congr_primary Ψ Φ h]

lemma completedMellinCoefficient_congr_primary (p:CompletedMellinIndex) :
    completedMellinCoefficient Ψ p=completedMellinCoefficient Φ p := by
  unfold completedMellinCoefficient
  rw [columnWeight_congr_primary Ψ Φ h,cubeWeight_congr_primary Ψ Φ h]


end CompletedGauss


open scoped Classical BigOperators

namespace ShortDraftCRT
open ActualEisensteinCubic FiniteGaussPhase ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]

def finiteCrossNumerator (a c l:Eis) (p h:ι→Eis) : Eis :=
  a*(∏i,p i)+l^2*c*∑i,h i*cofactor p i

lemma prime_dvd_other_cofactor (p:ι→Eis) {i k:ι} (hik:i≠k) : p i∣cofactor p k := by
  exact Finset.dvd_prod_of_mem p (Finset.mem_erase.mpr ⟨hik,Finset.mem_univ i⟩)

lemma finiteCrossNumerator_local (a c l:Eis) (p h:ι→Eis) (i:ι) :
    Ideal.Quotient.mk (Ideal.span {p i}) (finiteCrossNumerator a c l p h)=
      Ideal.Quotient.mk (Ideal.span {p i}) (l^2*c*cofactor p i)*
        Ideal.Quotient.mk (Ideal.span {p i}) (h i) := by
  let q:=Ideal.Quotient.mk (Ideal.span {p i})
  have hz:q (∏k,p k)=0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton.mpr ⟨cofactor p i, (prime_mul_cofactor p i).symm⟩
  have hs:(∑k,q (h k)*q (cofactor p k))=q (h i)*q (cofactor p i) := by
    apply Finset.sum_eq_single i
    · intro k hk hki
      have hk0:q (cofactor p k)=0:=Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton.mpr (prime_dvd_other_cofactor p hki.symm))
      rw [hk0,mul_zero]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  change q (finiteCrossNumerator a c l p h)=q (l^2*c*cofactor p i)*q (h i)
  simp only [finiteCrossNumerator,map_add,map_mul,map_sum,map_pow,hz,mul_zero,zero_add,hs]
  ring

lemma finiteCrossNumerator_fixed (N a c l:Eis) (p h:ι→Eis)
    (hh:∀i,N∣h i) : N∣finiteCrossNumerator a c l p h-a*(∏i,p i) := by
  have hs:N∣∑i,h i*cofactor p i:=Finset.dvd_sum (fun i _=>dvd_mul_of_dvd_left (hh i) _)
  convert! dvd_mul_of_dvd_right hs (l^2*c) using 1 ; simp [finiteCrossNumerator]

lemma finiteCrossNumerator_fixed_sector {κ:Type*} [Fintype κ]
    (M a c l:Eis) (p h:ι→Eis) (p0 h0:κ→Eis)
    (hc:c∣M) (hh:∀i,M^2∣h i) (hh0:∀i,M^2∣h0 i)
    (hr:M^2∣(∏i,p i)-(∏i,p0 i)) :
    M*c∣finiteCrossNumerator a c l p h-finiteCrossNumerator a c l p0 h0 := by
  have hmc:M*c∣M^2:=by simpa only [pow_two] using mul_dvd_mul_left M hc
  apply hmc.trans
  have h1:=finiteCrossNumerator_fixed (M^2) a c l p h hh
  have h0:=finiteCrossNumerator_fixed (M^2) a c l p0 h0 hh0
  have h2:=dvd_mul_of_dvd_right hr a
  convert! dvd_sub (dvd_add h1 h2) h0 using 1 ; ring


end ShortDraftCRT

end

end OAI

end


