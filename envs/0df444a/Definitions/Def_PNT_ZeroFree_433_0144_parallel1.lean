-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0144_parallel1
-- name    : PNT_ZeroFree_433_0144_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:56:54.242963+00:00
-- url     : https://prove2.me/theorems/1ce5eb93-1dc4-4a67-bdd6-def27bf49383
-- title:
--   Zero-free region foundations: QuadraticSieve.ProductColumns [0144_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.ProductColumns
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/ProductColumns.lean#L77-L606

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0051
import Definitions.Def_PNT_ZeroFree_433_0056_1
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0086
import Definitions.Def_PNT_ZeroFree_433_0130_parallel1
import Definitions.Def_PNT_ZeroFree_433_0158_parallel1
import Definitions.Def_PNT_ZeroFree_433_0188_parallel1
import Definitions.Def_PNT_ZeroFree_433_0218_parallel1
import Definitions.Def_PNT_ZeroFree_433_0228_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0260_parallel1
import Definitions.Def_PNT_ZeroFree_433_0262_parallel1
import Definitions.Def_PNT_ZeroFree_433_0303_parallel1
import Definitions.Def_PNT_ZeroFree_433_0329_parallel1
import Definitions.Def_PNT_ZeroFree_433_0330_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/ProductColumns.lean
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum

def productColumnCoefficient (S T : Finset (Ideal O)) (β : Ideal O → Ideal O → ℂ) (I : Ideal O) : ℂ :=
  ∑p∈(S×ˢT).filter (fun p => p.1*p.2=I),β p.1 p.2

theorem product_fiber_card (P : Finset (Ideal O×Ideal O)) (I : Ideal O) (hI : I≠0) :
    (P.filter (fun p => p.1*p.2=I)).card≤(idealDivisors I).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    apply (mem_idealDivisors hI).mpr
    rw [←(Finset.mem_filter.mp hp).2]
    exact dvd_mul_right _ _
  · intro p hp q hq he
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    have hz : p.1≠0 := by intro hz; simp only [hz,zero_mul] at hp'; exact hI hp'.symm
    apply Prod.ext he
    apply mul_left_cancel₀ hz
    rw [hp',he,hq']

theorem productColumnCoefficient_norm (S T : Finset (Ideal O)) (β : Ideal O → Ideal O → ℂ)
    (hβ : ∀n∈S,∀b∈T,‖β n b‖≤1) (I : Ideal O) (hI : I≠0) :
    ‖productColumnCoefficient S T β I‖≤(idealDivisors I).card := by
  unfold productColumnCoefficient
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑p∈(S×ˢT).filter (fun p => p.1*p.2=I),(1:ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hh := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      exact hβ p.1 hh.1 p.2 hh.2
    _ = ((S×ˢT).filter (fun p => p.1*p.2=I)).card := by simp
    _ ≤ _ := by exact_mod_cast product_fiber_card (S×ˢT) I hI

theorem productColumnCoefficient_row_sum (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (k : Ideal O) :
    (∑n∈S,∑b∈T,quadraticRow k (primaryGenerator (n*b))*β n b)=
    ∑I∈(S×ˢT).image (fun p => p.1*p.2),quadraticRow k (primaryGenerator I)*productColumnCoefficient S T β I := by
  rw [←Finset.sum_product (f := fun p : Ideal O×Ideal O => quadraticRow k (primaryGenerator (p.1*p.2))*β p.1 p.2)]
  rw [←Finset.sum_fiberwise_of_maps_to
    (fun p (hp : p∈S×ˢT) => Finset.mem_image_of_mem (fun p : Ideal O×Ideal O => p.1*p.2) hp)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [productColumnCoefficient,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]


end CanonicalQuadraticSieve

namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge

def shortCompletedSum (Ψ : O →* ℂ) (W : ℝ → ℂ) (X H₀ : ℝ) : ℂ :=
  ∑' H : Ideal O, if (Ideal.absNorm H:ℝ)<H₀ then
    (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψ H*
      completedT Ψ W (X/(Ideal.absNorm H:ℝ)^3) else 0

def shortCubeRange (H₀ : ℝ) : Finset (Ideal O) :=
  (idealsUpTo ⌈H₀⌉₊).filter (fun H => (Ideal.absNorm H:ℝ)<H₀)

theorem mem_shortCubeRange (H₀ : ℝ) (H : Ideal O) :
    H∈shortCubeRange H₀ ↔ H≠0 ∧ (Ideal.absNorm H:ℝ)<H₀ := by
  rw [shortCubeRange,Finset.mem_filter,mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hn,hup⟩,hH⟩
    refine ⟨?_,hH⟩
    intro hz
    have hh : Ideal.absNorm H=0 := Ideal.absNorm_eq_zero_iff.mpr hz
    omega
  · rintro ⟨hH,hn⟩
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (fun hz => hH (Ideal.absNorm_eq_zero_iff.mp hz)),
      Nat.cast_le.mp (hn.le.trans (Nat.le_ceil H₀))⟩,hn⟩

theorem shortCompletedSum_eq (Ψ : O →* ℂ) (W : ℝ → ℂ) (X H₀ : ℝ) :
    shortCompletedSum Ψ W X H₀ = ∑H∈shortCubeRange H₀,
      (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψ H*
        completedT Ψ W (X/(Ideal.absNorm H:ℝ)^3) := by
  unfold shortCompletedSum
  rw [tsum_eq_sum (s:=shortCubeRange H₀)]
  · exact Finset.sum_congr rfl (fun H hH => if_pos ((mem_shortCubeRange H₀ H).mp hH).2)
  · intro H hH
    by_cases hz : H=0
    · simp [hz]
    · have hn : ¬(Ideal.absNorm H:ℝ)<H₀ := fun hn => hH ((mem_shortCubeRange H₀ H).mpr ⟨hz,hn⟩)
      exact if_neg hn

theorem cube_inverse_weight_norm (Ψ : O →* ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (H : Ideal O) :
    ‖(UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψ H‖≤1/(Ideal.absNorm H:ℝ) := by
  have hang : ‖FiniteGaussPhase.angularFactor (primaryGenerator H)‖≤1 := by
    by_cases hz : primaryGenerator H=0
    · simp [hz,FiniteGaussPhase.angularFactor]
    · exact (FiniteGaussPhase.norm_angularFactor _ hz).le
  have hw : ‖cubeWeight Ψ H‖≤1/(Ideal.absNorm H:ℝ) := by
    change ‖star (FiniteGaussPhase.angularFactor (primaryGenerator H))^3*Ψ (primaryGenerator H)^3/(Ideal.absNorm H:ℂ)‖≤_
    rw [norm_div,norm_mul,norm_pow,norm_pow,norm_star,Complex.norm_natCast]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have h1 : ‖FiniteGaussPhase.angularFactor (primaryGenerator H)‖^3≤1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) hang 3
    have h2 : ‖Ψ (primaryGenerator H)‖^3≤1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (hΨ _) 3
    nlinarith [pow_nonneg (norm_nonneg (Ψ (primaryGenerator H))) 3]
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (QuadraticInitialBound.norm_ideal_moebius_le_one H)).trans hw


end

open ActualEisensteinCubic CanonicalQuadraticSieve

theorem short_cube_scale_algebra (z K R X F h : ℝ)
    (hz : 1≤z) (hK : 1≤K) (hR : 1≤R) (hF : 1≤F) (hFz : F≤z)
    (hh : 1≤h) (hhz : h≤z) (hmargin : K*R*z^25≤X*F) :
    1≤X/h^3 ∧ K^2*R*F*h^3/X≤K := by
  have hz0 : 0<z := by linarith
  have hF0 : 0<F := by linarith
  have hh0 : 0<h := by linarith
  have hKR : 1≤K*R := by nlinarith
  have hp4 : z^4≤z^25 := pow_le_pow_right₀ hz (by norm_num)
  have hp5 : z^5≤z^25 := pow_le_pow_right₀ hz (by norm_num)
  have hsmall : h^3*F≤z^25 := by
    calc
      _ ≤ z^3*z := by gcongr
      _ = z^4 := by ring
      _ ≤ _ := hp4
  have hcube : h^3≤X := by
    have h1 : h^3*F≤X*F := hsmall.trans ((le_mul_of_one_le_left (by positivity) hKR).trans hmargin)
    exact (mul_le_mul_iff_left₀ hF0).mp (by simpa only [mul_comm F] using h1)
  have hX : 0<X := (pow_pos hh0 3).trans_le hcube
  refine ⟨(le_div_iff₀ (pow_pos hh0 3)).mpr (by simpa using hcube),?_⟩
  have hfh : F^2*h^3≤z^25 := by
    calc
      _ ≤ z^2*z^3 := by gcongr
      _ = z^5 := by ring
      _ ≤ _ := hp5
  have hprod : K*R*F*h^3≤X := by
    have hn : K*R*(F^2*h^3)≤X*F :=
      (mul_le_mul_of_nonneg_left hfh (by positivity)).trans hmargin
    apply (mul_le_mul_iff_right₀ hF0).mp
    nlinarith
  apply (div_le_iff₀ hX).mpr
  nlinarith [mul_le_mul_of_nonneg_left hprod (show 0≤K by linarith)]

theorem short_cube_scales (Z K R X F h : ℝ)
    (hZ : 1≤Z) (hK : 1≤K) (hR : 1≤R) (hF : 1≤F)
    (hFZ : F≤Z^(1/1000:ℝ)) (hh : 1≤h) (hhZ : h≤Z^(1/1000:ℝ))
    (hmargin : K*R≤X*F*Z^(-(1/40:ℝ))) :
    1≤X/h^3 ∧ K^2*R*F*h^3/X≤K := by
  have hZ0 : 0<Z := by linarith
  have hz : 1≤Z^(1/1000:ℝ) := Real.one_le_rpow hZ (by norm_num)
  have he : (Z^(1/1000:ℝ))^25=Z^(1/40:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ0.le]
    norm_num
  apply short_cube_scale_algebra _ K R X F h hz hK hR hF hFZ hh hhZ
  rw [he]
  have hm := mul_le_mul_of_nonneg_right hmargin (Real.rpow_nonneg hZ0.le (1/40:ℝ))
  have hp : Z^(-(1/40:ℝ))*Z^(1/40:ℝ)=1 := by
    rw [←Real.rpow_add hZ0]
    norm_num
  calc
    _ ≤ X*F*Z^(-(1/40:ℝ))*Z^(1/40:ℝ) := hm
    _ = X*F := by rw [mul_assoc (X*F),hp,mul_one]


end CompletedGauss

namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel


theorem columnSquareParts_nonzero_bounds (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤X) (A : Ideal O)
    (hA : A∈S.image squarePart) :
    A≠0 ∧ 1≤(Ideal.absNorm A:ℝ) ∧ (Ideal.absNorm A:ℝ)≤X ∧ 1≤X/(Ideal.absNorm A:ℝ)^2 := by
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hA
  have hi := hS I hI
  have hAz := squarePart_ne_zero hi.1
  have hDz := (squarefree_squarefreePart I).ne_zero
  have ha : 1≤(Ideal.absNorm (squarePart I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hAz (Ideal.absNorm_eq_zero_iff.mp hz))
  have hd : 1≤(Ideal.absNorm (squarefreePart I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hDz (Ideal.absNorm_eq_zero_iff.mp hz))
  have hn : (Ideal.absNorm (squarePart I):ℝ)^2*(Ideal.absNorm (squarefreePart I):ℝ)=(Ideal.absNorm I:ℝ) := by
    exact_mod_cast norm_decomposition I
  refine ⟨hAz,ha,by nlinarith,?_⟩
  apply (le_div_iff₀ (by positivity : 0<(Ideal.absNorm (squarePart I):ℝ)^2)).mpr
  nlinarith


end CanonicalQuadraticSieve

end

end OAI

end


