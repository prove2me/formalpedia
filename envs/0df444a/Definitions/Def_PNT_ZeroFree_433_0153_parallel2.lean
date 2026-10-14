-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0153_parallel2
-- name    : PNT_ZeroFree_433_0153_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:50:11.473126+00:00
-- url     : https://prove2.me/theorems/f7ce88bd-baa4-4e94-b839-93977fe9a118
-- title:
--   Zero-free region foundations: CubicSieve.NormalizedMass [0153_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.NormalizedMass
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/NormalizedMass.lean#L94-L526

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0056_1
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0096
import Definitions.Def_PNT_ZeroFree_433_0102
import Definitions.Def_PNT_ZeroFree_433_0107
import Definitions.Def_PNT_ZeroFree_433_0110
import Definitions.Def_PNT_ZeroFree_433_0119
import Definitions.Def_PNT_ZeroFree_433_0120_parallel1
import Definitions.Def_PNT_ZeroFree_433_0121_parallel1
import Definitions.Def_PNT_ZeroFree_433_0123
import Definitions.Def_PNT_ZeroFree_433_0123_parallel2
import Definitions.Def_PNT_ZeroFree_433_0128_parallel2
import Definitions.Def_PNT_ZeroFree_433_0131_parallel2
import Definitions.Def_PNT_ZeroFree_433_0136_parallel2
import Definitions.Def_PNT_ZeroFree_433_0144_parallel2
import Definitions.Def_PNT_ZeroFree_433_0146_parallel1
import Definitions.Def_PNT_ZeroFree_433_0149_parallel2
import Definitions.Def_PNT_ZeroFree_433_0151_parallel1
import Definitions.Def_PNT_ZeroFree_433_0153_parallel1
import Definitions.Def_PNT_ZeroFree_433_0158_parallel2
import Definitions.Def_PNT_ZeroFree_433_0226_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/NormalizedMass.lean
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

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})


omit [DecidableEq ι] in
theorem normalized_second_coefficient_sq_le
    (Ψ : O→*ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (m c d : O)
    (g : ℝ→ℂ) (G X : ℝ) (hG : ∀t,‖g t‖≤G) (S : Finset ι) :
    ‖secondInputCoefficient p hg Ψ m c d
      (normalizedColumn p (fun A => g (columnLog p X A))) S‖^2≤G^2/primeProductNorm p S := by
  have hG0 : 0≤G := (norm_nonneg (g 0)).trans (hG 0)
  have ht := secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d
    (normalizedColumn p (fun A => g (columnLog p X A))) S
  apply (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans
  simp only [normalizedColumn,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),div_pow]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hG _) 2) (sq_nonneg _)


include hp in

theorem normalized_second_mass_fixed_bound
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ : O→*ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (m c d : O)
    (g : ℝ→ℂ) (G M X : ℝ) (hX : 0<X)
    (hG : ∀t,‖g t‖≤G) (hM : ∀t,g t≠0 → |t|≤M) :
    (∑S∈F.powerset,‖secondInputCoefficient p hg Ψ m c d
      (normalizedColumn p (fun A => g (columnLog p X A))) S‖^2)≤
      128*Real.exp (2*M)*G^2 := by
  by_cases hsmall : X*Real.exp M<1
  · rw [normalized_second_mass_zero p hp hg F Ψ m c d g M X hX hM hsmall]
    positivity
  have hH : 1≤X*Real.exp M := le_of_not_gt hsmall
  let T := F.powerset.filter (fun S => g (columnLog p X S)≠0)
  have hsub : T⊆boundedPrimeSupports p F (X*Real.exp M) := by
    intro S hS
    obtain ⟨hSF,hSn⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr ⟨hSF,columnLog_norm_upper p hp X M hX S
      ((le_abs_self _).trans (hM _ hSn))⟩
  have hcard : (T.card:ℝ)≤128*(X*Real.exp M) := by
    apply (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    exact boundedPrimeSupports_card p hinj F (X*Real.exp M) hH
  have he : (∑S∈F.powerset,‖secondInputCoefficient p hg Ψ m c d
        (normalizedColumn p (fun A => g (columnLog p X A))) S‖^2)=
      ∑S∈T,‖secondInputCoefficient p hg Ψ m c d
        (normalizedColumn p (fun A => g (columnLog p X A))) S‖^2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S hS hn
    have hz : g (columnLog p X S)=0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hS,hh⟩)
    simp [secondInputCoefficient,normalizedColumn,hz]
  rw [he]
  calc
    _ ≤ ∑_S∈T,G^2/(X*Real.exp (-M)) := by
      apply Finset.sum_le_sum
      intro S hS
      apply (normalized_second_coefficient_sq_le p hg Ψ hΨ m c d g G X hG S).trans
      have hlo := columnLog_norm_lower p hp X M hX S (abs_le.mp (hM _ (Finset.mem_filter.mp hS).2)).1
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hlo
    _ = (T.card:ℝ)*(G^2/(X*Real.exp (-M))) := by simp
    _ ≤ (128*(X*Real.exp M))*(G^2/(X*Real.exp (-M))) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 128*Real.exp (2*M)*G^2 := by
      rw [show 2*M=M+M by ring,Real.exp_add,Real.exp_neg]
      field_simp [hX.ne',Real.exp_ne_zero]

end

theorem full_uniform_normalized_second_mass (g : 𝓢(ℝ,ℂ)) (M : ℝ)
    (hM : ∀t,g t≠0 → |t|≤M) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀z,‖Ψ z‖≤1) (m c d : O) (X : ℝ),0<X →
      (∑S∈F.powerset,‖secondInputCoefficient p hg Ψ m c d
        (normalizedColumn p (fun A => g (columnLog p X A))) S‖^2)≤C := by
  refine ⟨128*Real.exp (2*M)*(SchwartzMap.seminorm ℝ 0 0 g)^2+1,by positivity,?_⟩
  intro ι _ p hp _ hg hinj F Ψ hΨ m c d X hX
  exact (normalized_second_mass_fixed_bound p hp hg hinj F Ψ hΨ m c d g _ M X hX
    (fun t => g.norm_le_seminorm ℝ t) hM).trans (by linarith)

end


theorem globalDiagonalPowers (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ B U : ℝ,1≤B → 1≤U →
      B^(ε/3)*(U*B^2)^(ε/3)*(128*Real.exp 1*(normLogBin U+1 : ℝ))^2≤C*(B*U)^ε := by
  let k : ℝ := 128*Real.exp 1
  let C := k^2*(1+1/(ε/3))^2
  refine ⟨C,by dsimp [C,k]; positivity,?_⟩
  intro B U hB hU
  have hB0 : 0<B := by linarith
  have hU0 : 0<U := by linarith
  have hη : 0<ε/3 := by positivity
  have hlog := descent_normLogBin_small_power (ε/3) hη U hU
  have hBp : B^(ε/3)*(B^2)^(ε/3)=B^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hB0.le,←Real.rpow_add hB0]
    congr 1
    ring
  have hUp : U^(ε/3)*(U^(ε/3))^2=U^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hU0.le,←Real.rpow_add hU0]
    congr 1
    ring
  calc
    _ ≤ B^(ε/3)*(U*B^2)^(ε/3)*(k*((1+1/(ε/3))*U^(ε/3)))^2 := by
      dsimp [k]
      gcongr
    _ = k^2*(1+1/(ε/3))^2*(B^(ε/3)*(B^2)^(ε/3))*(U^(ε/3)*(U^(ε/3))^2) := by
      rw [Real.mul_rpow hU0.le (sq_nonneg B)]
      ring
    _ = C*(B*U)^ε := by rw [hBp,hUp,Real.mul_rpow hB0.le hU0.le]; dsimp [C]; ring

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)


end SecondPassArithmetic

open scoped BigOperators Classical
namespace CompletedGauss


section
open ActualEisensteinCubic CanonicalQuadraticSieve QuadraticSquarefreeKernel

theorem powerful_inverse_norm_sum (S : Finset (Ideal O))
    (hS : ∀I∈S,PowerfulIdeal I) :
    (∑I∈S,1/(Ideal.absNorm I:ℝ))≤1048576 := by
  let A := S.image powerfulBase
  let B := S.image squarefreePart
  let pair : Ideal O→Ideal O×Ideal O := fun I => (powerfulBase I,squarefreePart I)
  have ha (I : Ideal O) (hI : I∈A) : I≠0 := by
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    exact (powerfulBase_spec J (hS J hJ)).1
  have hb (I : Ideal O) (hI : I∈B) : I≠0 := by
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    exact (squarefree_squarefreePart J).ne_zero
  have hca : (∑I∈A,1/(Ideal.absNorm I:ℝ)^2)≤1024 :=
    finite_inverse_norm_square_sum A (∑I∈A,(Ideal.absNorm I:ℝ)) ha
      (fun I hI => Finset.single_le_sum (fun J _ => Nat.cast_nonneg _) hI)
  have hcb : (∑I∈B,1/(Ideal.absNorm I:ℝ)^2)≤1024 :=
    finite_inverse_norm_square_sum B (∑I∈B,(Ideal.absNorm I:ℝ)) hb
      (fun I hI => Finset.single_le_sum (fun J _ => Nat.cast_nonneg _) hI)
  have hinj : Set.InjOn pair S := by
    intro I hI J hJ he
    exact powerfulBase_injective_on_fiber I J (hS I hI) (hS J hJ)
      (congrArg Prod.snd he) (congrArg Prod.fst he)
  have hsub : S.image pair ⊆ A×ˢB := by
    intro p hp
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hI,Finset.mem_image_of_mem _ hI⟩
  calc
    _ ≤ ∑I∈S,1/(Ideal.absNorm (powerfulBase I):ℝ)^2 *
        (1/(Ideal.absNorm (squarefreePart I):ℝ)^2) := by
      apply Finset.sum_le_sum
      intro I hI
      have hni := (powerfulBase_spec I (hS I hI)).2
      have hb1 : 1≤(Ideal.absNorm (squarefreePart I):ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (fun hz => (squarefree_squarefreePart I).ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
      have ha0 : 0<(Ideal.absNorm (powerfulBase I):ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero
          (fun hz => (powerfulBase_spec I (hS I hI)).1 (Ideal.absNorm_eq_zero_iff.mp hz))
      have he : (Ideal.absNorm I:ℝ)=(Ideal.absNorm (powerfulBase I):ℝ)^2*
          (Ideal.absNorm (squarefreePart I):ℝ)^3 := by
        have h := congrArg (fun J : Ideal O => (Ideal.absNorm J:ℝ)) hni
        simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using h.symm
      rw [he,one_div,one_div,one_div,←mul_inv]
      exact inv_anti₀ (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb1 (by decide)) (sq_nonneg _))
    _ = ∑p∈S.image pair,1/(Ideal.absNorm p.1:ℝ)^2 * (1/(Ideal.absNorm p.2:ℝ)^2) := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑p∈A×ˢB,1/(Ideal.absNorm p.1:ℝ)^2 * (1/(Ideal.absNorm p.2:ℝ)^2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = (∑I∈A,1/(Ideal.absNorm I:ℝ)^2)*(∑I∈B,1/(Ideal.absNorm I:ℝ)^2) := by
      rw [Finset.sum_product,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro I _
      rw [Finset.mul_sum]
    _ ≤ 1024*1024 := mul_le_mul hca hcb (by positivity) (by norm_num)
    _ = _ := by norm_num

end


end CompletedGauss

end

end OAI

end


