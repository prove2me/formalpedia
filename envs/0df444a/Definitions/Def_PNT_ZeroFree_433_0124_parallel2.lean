-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0124_parallel2
-- name    : PNT_ZeroFree_433_0124_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:06:42.341692+00:00
-- url     : https://prove2.me/theorems/1ee4f1af-b196-41e5-9d74-dc540edfc159
-- title:
--   Zero-free region foundations: Eisenstein.QuotientTopology [0124_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.QuotientTopology
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/QuotientTopology.lean#L266-L732

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0054
import Definitions.Def_PNT_ZeroFree_433_0054_1
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0059
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0066
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0077
import Definitions.Def_PNT_ZeroFree_433_0078
import Definitions.Def_PNT_ZeroFree_433_0080
import Definitions.Def_PNT_ZeroFree_433_0081
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0101
import Definitions.Def_PNT_ZeroFree_433_0102
import Definitions.Def_PNT_ZeroFree_433_0110
import Definitions.Def_PNT_ZeroFree_433_0118_parallel1
import Definitions.Def_PNT_ZeroFree_433_0119_parallel1
import Definitions.Def_PNT_ZeroFree_433_0120_parallel1
import Definitions.Def_PNT_ZeroFree_433_0122
import Definitions.Def_PNT_ZeroFree_433_0124_parallel1
import Definitions.Def_PNT_ZeroFree_433_0128
import Definitions.Def_PNT_ZeroFree_433_0152_parallel1
import Definitions.Def_PNT_ZeroFree_433_0153_parallel2
import Definitions.Def_PNT_ZeroFree_433_0210
import Definitions.Def_PNT_ZeroFree_433_0235_parallel1
import Definitions.Def_PNT_ZeroFree_433_0271_parallel1_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/QuotientTopology.lean
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


namespace SecondPassArithmetic

section

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory

section
open ActualEisensteinCubic
open SecondPassFiber (newLabel newRow)
open SecondPassIntegration (tupleSourceSum densityChildEnergy)
open JointLogSeparation (outerWindow)


variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})


def globalSecondSource (s : Finset (GlobalSecondData ι)) (w : GlobalSecondData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (A₁ A₂ W : 𝓢(ℝ,ℂ))
    (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : GlobalSecondData ι → ℝ) (X₁ X₂ R : ℝ) : ℂ :=
  ∑ x∈s,w x * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m (globalSecondLabel p x)
    (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x)) A₁ A₂ W V
    (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂ R

theorem globalSecondSource_eq_tupleSource
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (s : Finset (GlobalSecondData ι)) (q : Ideal O × Ideal O × Ideal O)
    (hs : ∀ x∈s,GlobalSecondAdmissible x) (hq : ∀ x∈s,globalSecondFixedTriple p x=q)
    (w : GlobalSecondData ι → ℂ) (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ)
    (z ud ue uv kap : GlobalSecondData ι → ℝ) (X₁ X₂ R : ℝ) :
    globalSecondSource p hp hcop hg s w F Ψ₁ Ψ₂ m A₁ A₂ W V z ud ue uv kap X₁ X₂ R =
    tupleSourceSum p hp hcop hg (s.image (globalSecondTuple p))
      (w ∘ globalSecondRecover p s) (globalSecondLabel p ∘ globalSecondRecover p s)
      F Ψ₁ Ψ₂ m A₁ A₂ W V (z ∘ globalSecondRecover p s) (ud ∘ globalSecondRecover p s)
      (ue ∘ globalSecondRecover p s) (uv ∘ globalSecondRecover p s) (kap ∘ globalSecondRecover p s) X₁ X₂ R := by
  unfold globalSecondSource tupleSourceSum
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro x hx
    simp only [Function.comp_apply,globalSecondRecover_apply p hinj s q hs hq x hx]
  · intro x hx y hy he
    exact globalSecondEncoding_injective p hinj (hs x hx) (hs y hy) ((hq x hx).trans (hq y hy).symm) he

theorem globalSecondSource_uniform_transfer
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i,0 ≤ M i) (hV : ∀ i x,V i x ≠ 0 → |x| ≤ M i) (A J : ℕ) :
    ∃ Cₐ : ℝ,0 < Cₐ ∧ ∃ Cₛ : ℝ,0 ≤ Cₛ ∧
      ∀ (R : ℝ),0 < R → ∀ (s : Finset (GlobalSecondData ι)) (T : Finset (Ideal O × O))
        (q : Ideal O × Ideal O × Ideal O) (w : GlobalSecondData ι → ℂ) (B lengthScale : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
        (z ud ue uv kap : GlobalSecondData ι → ℝ) (X₁ X₂ : ℝ),
        q.1 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
        (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,globalSecondFixedTriple p x=q) →
        (∀ x∈s,(newLabel (globalSecondTuple p x),newRow (globalSecondTuple p x))∈T) →
        (∀ a∈T,a.1 ≠ ⊥) → (∀ a∈T,(Ideal.absNorm a.1 : ℝ) ≤ lengthScale) →
        (∀ x∈s,‖w x‖*‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ ≤ B) →
        ‖globalSecondSource p hp hcop hg s w F Ψ₁ Ψ₂ (fixedTripleMask m q)
          A₁ A₂ W V z ud ue uv kap X₁ X₂ R‖ ≤
        (B*Cₐ*(lengthScale*Ideal.absNorm q.1)^ε) * (Cₛ/(1+R)^A) *
          densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ (fixedTripleMask m q) T (V 5) (V 6) X₁ X₂ J := by
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htransfer⟩ := SecondPassIntegration.tupleSource_uniform_transfer p hp hcop hg
    ε hε A₁ A₂ W V M hM hV A J
  refine ⟨Cₐ,hCₐ,Cₛ,hCₛ,?_⟩
  intro R hR s T q w B lengthScale F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hq hB hL hs hfixed hmap ht hn hw
  obtain ⟨b,hb,htrans⟩ := htransfer R hR
  let r := globalSecondRecover p s
  have hr (x : GlobalSecondData ι) (hx : x∈s) : r (globalSecondTuple p x)=x :=
    globalSecondRecover_apply p hinj s q hs hfixed x hx
  have hvalid : ∀ y∈s.image (globalSecondTuple p),
      SecondPassFiber.Valid y (newLabel y) q.1 (newRow y) := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    have hv := globalSecondTuple_valid p x (hs x hx)
    simpa only [hfixed x hx] using hv
  have hmap' : ∀ y∈s.image (globalSecondTuple p),(newLabel y,newRow y)∈T := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact hmap x hx
  have hw' : ∀ y∈s.image (globalSecondTuple p),
      ‖(w ∘ r) y‖*‖outerWindow V ((z ∘ r) y) ((ud ∘ r) y) ((ue ∘ r) y) ((uv ∘ r) y) ((kap ∘ r) y)‖ ≤ B := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    simpa only [Function.comp_apply,hr x hx] using hw x hx
  have hlabel : ∀ y∈s.image (globalSecondTuple p),Ideal.span {(globalSecondLabel p ∘ r) y}=newLabel y := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    simpa only [Function.comp_apply,hr x hx] using globalSecondLabel_span p x
  have hh := htrans (s.image (globalSecondTuple p)) T q.1 (w ∘ r) B lengthScale (globalSecondLabel p ∘ r)
    F Ψ₁ Ψ₂ (fixedTripleMask m q) (z ∘ r) (ud ∘ r) (ue ∘ r) (uv ∘ r) (kap ∘ r) X₁ X₂
    hq hB hL hvalid hmap' ht hn hw' hlabel
  rw [← globalSecondSource_eq_tupleSource p hp hcop hg hinj s q hs hfixed] at hh
  apply hh.trans
  have hd := SecondPassIntegration.child_coefficient_density_bound p hp hcop hg F Ψ₁ Ψ₂
    (fixedTripleMask m q) T (V 5) (V 6) X₁ X₂ (𝓕 A₁) (𝓕 A₂) b J ((1+R)^A) Cₛ hb
  have hpow : 0 < (1+R)^A := pow_pos (by linarith) _
  have hi := (le_div_iff₀' hpow).mpr hd
  have hnn : 0 ≤ B*Cₐ*(lengthScale*Ideal.absNorm q.1)^ε := by positivity
  have hbnd := mul_le_mul_of_nonneg_left hi hnn
  convert! hbnd using 1 ; ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (b0Label)
open SecondPassFiber (newLabel newRow)
open SecondPassIntegration (densityChildEnergy)
open JointLogSeparation (outerWindow)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})


def globalSecondRawSource (s : Finset (GlobalSecondData ι)) (w : GlobalSecondData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (A₁ A₂ W : 𝓢(ℝ,ℂ))
    (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : GlobalSecondData ι → ℝ) (X₁ X₂ R : ℝ) : ℂ :=
  ∑ x∈s,w x * postCommonSmoothPair p hp hcop hg (globalSecondRawPool F x) Ψ₁ Ψ₂
    (globalSecondRawMask p m x) (globalSecondLabel p x)
    (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x)) A₁ A₂ W V
    (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂ R


end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct jLabel b0Label cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)


variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]


include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalCubeJNorm_pos (x : GlobalSecondData ι) : 0 < globalCubeJNorm p x :=
  zero_lt_one.trans_le (element_norm_ge_one _ (primeProduct_ne_zero p hp _ _))


include hp in

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecond_radial_ratio (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (x : GlobalSecondData ι) (side : Bool) (j : SecondLogIndex) :
    globalFirstRowScale p K ell B F x*secondLogK j*
      (primeProductNorm p (x.source.sourceCommon\x.source.divisor))^2/
      (primeProductNorm p x.firstDivisor*(globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon)^2) =
    secondLogK j/globalNominalChildRow p K B F x side := by
  have hC := (FirstPassCubeLabels.primeProductNorm_pos p hp x.common).ne'
  have hd := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstDivisor).ne'
  have ha := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.cube.sideDivisor side)).ne'
  have ht := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon).ne'
  have hr := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.source.sourceCommon\x.source.divisor)).ne'
  have hJ := (globalCubeJNorm_pos p hp x).ne'
  unfold globalFirstRowScale globalFirstColumnScale globalNominalChildRow globalSecondDelta
  field_simp


include hp in

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecond_complete_cost (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (x : GlobalSecondData ι) (side : Bool) :
    (K/(primeProductNorm p x.firstDivisor*ell*B^2*F*globalCubeActiveRoot p x)) *
      (globalFirstRowScale p K ell B F x *
        ‖eisEmbedding (secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent
          x.cube.leftBit x.cube.rightBit)‖^2*Real.exp 2/globalFirstColumnScale p ell x side) *
      ((B*globalCubeActiveRoot p x/globalCubeJNorm p x)*primeProductNorm p x.firstCommon*
        primeProductNorm p (x.source.sourceCommon\x.source.divisor)) =
    Real.exp 2*globalSecondDelta p B F x side*B^2/globalCubeJNorm p x := by
  rw [globalBaseLabel_norm]
  have hC := (FirstPassCubeLabels.primeProductNorm_pos p hp x.common).ne'
  have hd := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstDivisor).ne'
  have ha := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.cube.sideDivisor side)).ne'
  have hJ := (globalCubeJNorm_pos p hp x).ne'
  have hc := (globalCubeActiveRoot_pos p hp x).ne'
  unfold globalFirstRowScale globalFirstColumnScale globalSecondDelta
  field_simp

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalNominalChildRow_pos (K B F : ℝ) (hK : 0 < K) (hB : 0 < B) (hF : 0 < F)
    (x : GlobalSecondData ι) (side : Bool) : 0 < globalNominalChildRow p K B F x side := by
  unfold globalNominalChildRow
  exact div_pos (mul_pos hK (globalCubeJNorm_pos p hp x))
    (mul_pos (sq_pos_of_pos (globalSecondDelta_pos p hp B F hB hF x side)) (sq_pos_of_pos hB))

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalNominalChildRow_bound (K B F : ℝ) (hK : 0 < K) (hB : 0 < B) (hF : 0 < F)
    (x : GlobalSecondData ι) (side : Bool)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    globalNominalChildRow p K B F x side ≤ K/(globalSecondDelta p B F x side)^2 := by
  have hJ := (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos B hB.le hb₁ hb₂).1
  change globalCubeJNorm p x ≤ B^2 at hJ
  unfold globalNominalChildRow
  have hD := globalSecondDelta_pos p hp B F hB hF x side
  calc
    _ ≤ K*B^2/((globalSecondDelta p B F x side)^2*B^2) := by gcongr
    _ = _ := by field_simp

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]


include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalChildMass_bound (ell B F : ℝ) (hell : 0 < ell) (hB : 0 < B) (hF : 0 < F)
    (x : GlobalSecondData ι) (side : Bool) (j : SecondLogIndex)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    globalChildMass p ell x side j ≤ Real.exp 2*((ell*B^3)*F)/globalSecondDelta p B F x side := by
  have hJ := (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos B hB.le hb₁ hb₂).1
  change globalCubeJNorm p x ≤ B^2 at hJ
  have hD := globalSecondDelta_pos p hp B F hB hF x side
  rw [globalChildMass,globalSecond_child_mass p hp ell B F hell hB hF]
  calc
    _ ≤ Real.exp 2*((ell*B^3)*F*B^2/(globalSecondDelta p B F x side*B^2)) := by gcongr
    _ = _ := by field_simp

include hp in

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalChildRow_bound (K B F : ℝ) (hK : 0 < K) (hB : 0 < B) (hF : 0 < F)
    (x : GlobalSecondData ι) (side : Bool) (j : SecondLogIndex)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hretained : secondLogK j/globalNominalChildRow p K B F x side ≤ globalSecondDelta p B F x side) :
    secondLogK j*Real.exp 1 ≤ Real.exp 1*K/globalSecondDelta p B F x side := by
  have hD := globalSecondDelta_pos p hp B F hB hF x side
  have hK' := globalNominalChildRow_pos p hp K B F hK hB hF x side
  have hk := (div_le_iff₀ hK').mp hretained
  have hsmall := globalNominalChildRow_bound p hp K B F hK hB hF x side hb₁ hb₂
  calc
    _ ≤ (globalSecondDelta p B F x side*globalNominalChildRow p K B F x side)*Real.exp 1 := by gcongr
    _ ≤ (globalSecondDelta p B F x side*(K/(globalSecondDelta p B F x side)^2))*Real.exp 1 := by gcongr
    _ = _ := by field_simp

include hp in

theorem globalSecondMask_bound (B F : ℝ) (hB : 0 < B) (hF : 1 ≤ F)
    (x : GlobalSecondData ι) (side : Bool) (m : O)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    ‖eisEmbedding (fixedTripleMask m (globalSecondFixedTriple p x))‖^2 ≤
      ‖eisEmbedding m‖^2*globalSecondDelta p B F x side := by
  have hb0 := (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos B hB.le hb₁ hb₂).2.1
  have he : ‖eisEmbedding (fixedTripleMask m (globalSecondFixedTriple p x))‖^2 =
      ‖eisEmbedding (globalSecondMask p m x)‖^2 := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,eisEmbedding_norm_sq_eq_absNorm_span,globalSecondMask_span]
  rw [he]
  have ha := primeProductNorm_ge_one p hp (x.cube.sideDivisor side)
  have ht := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon).le
  have hr := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.source.sourceCommon\x.source.divisor)).le
  change ‖eisEmbedding ((m*_*_)*∏ i∈x.firstCommon,p i)‖^2 ≤ _
  rw [SecondPassIntegration.restored_child_mask_norm]
  unfold globalSecondDelta
  calc
    _ ≤ ‖eisEmbedding m‖^2*B*primeProductNorm p (x.source.sourceCommon\x.source.divisor)*primeProductNorm p x.firstCommon := by gcongr
    _ ≤ ‖eisEmbedding m‖^2*(B*F*primeProductNorm p (x.cube.sideDivisor side)*primeProductNorm p x.firstCommon*
      primeProductNorm p (x.source.sourceCommon\x.source.divisor)) := by
      have hf : B ≤ B*F*primeProductNorm p (x.cube.sideDivisor side) := by
        calc
          B = B*1*1 := by ring
          _ ≤ _ := by gcongr
      nlinarith [mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hf ht) hr) (sq_nonneg ‖eisEmbedding m‖)]

include hp in

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecond_halving (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (x : GlobalSecondData ι) (side : Bool) (j : SecondLogIndex)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hretained : secondLogK j/globalNominalChildRow p K B F x side ≤ globalSecondDelta p B F x side)
    (hlarge : 2*Real.exp 2 ≤ globalSecondDelta p B F x side) :
    secondLogK j*Real.exp 1 ≤ K/2 ∧ globalChildMass p ell x side j ≤ ((ell*B^3)*F)/2 := by
  have hD := globalSecondDelta_pos p hp B F hB hF x side
  have he : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
  have hrow := globalChildRow_bound p hp K B F hK hB hF x side j hb₁ hb₂ hretained
  have hmass := globalChildMass_bound p hp ell B F hell hB hF x side j hb₁ hb₂
  constructor
  · apply hrow.trans
    apply (div_le_iff₀ hD).mpr
    nlinarith
  · apply hmass.trans
    apply (div_le_iff₀ hD).mpr
    have hparent : 0 < (ell*B^3)*F := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hlarge hparent.le]

end


theorem globalSecond_rank_decreases {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell) (hB : 0 < B) (hF : 0 < F)
    (x : GlobalSecondData ι) (side : Bool) (j : SecondLogIndex)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hretained : secondLogK j/globalNominalChildRow p K B F x side ≤ globalSecondDelta p B F x side)
    (hlarge : 2*Real.exp 2 ≤ globalSecondDelta p B F x side) :
    ⌈max (secondLogK j*Real.exp 1) (globalChildMass p ell x side j)⌉₊ < ⌈max K ((ell*B^3)*F)⌉₊ := by
  obtain ⟨hrow,hmass⟩ := globalSecond_halving p hp K ell B F hK hell hB hF x side j hb₁ hb₂ hretained hlarge
  have hchild : 1 ≤ secondLogK j*Real.exp 1 :=
    one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (Real.one_le_exp (by norm_num))
  apply ceil_strict_of_half
  · have h2 : 2 ≤ K := by linarith
    exact h2.trans (le_max_left _ _)
  · apply max_le
    · exact hrow.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by norm_num))
    · exact hmass.trans (div_le_div_of_nonneg_right (le_max_right _ _) (by norm_num))

end SecondPassArithmetic

end

end OAI

end


