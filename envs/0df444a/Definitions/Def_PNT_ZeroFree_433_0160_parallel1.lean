-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0160_parallel1
-- name    : PNT_ZeroFree_433_0160_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:10:27.981296+00:00
-- url     : https://prove2.me/theorems/e21ea1bd-5951-4867-a2d3-fb5b5b95e58c
-- title:
--   Zero-free region foundations: MeanSquare.ReflectedDyadicSeries [0160_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.MeanSquare.ReflectedDyadicSeries
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/ReflectedDyadicSeries.lean#L84-L544

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0086
import Definitions.Def_PNT_ZeroFree_433_0142_parallel1
import Definitions.Def_PNT_ZeroFree_433_0153_parallel1
import Definitions.Def_PNT_ZeroFree_433_0154_parallel1
import Definitions.Def_PNT_ZeroFree_433_0183_parallel1
import Definitions.Def_PNT_ZeroFree_433_0197_parallel1
import Definitions.Def_PNT_ZeroFree_433_0237_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/ReflectedDyadicSeries.lean
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

namespace InitialMeanSquare

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)

lemma star_normalizedColumn {ι : Type*} (p : ι → O) (g : 𝓢(ℝ,ℂ))
    (Z : ℝ) (S : Finset ι) :
    star (normalizedColumn p (fun T => g (columnLog p Z T)) S) =
      normalizedColumn p (fun T => conjugateProfile g (columnLog p Z T)) S := by
  simp only [normalizedColumn, conjugateProfile_apply]
  simp

lemma conjugateProfile_support_bound (g : 𝓢(ℝ,ℂ)) (A : ℝ)
    (hg : ∀ t, g t ≠ 0 → |t| ≤ A) :
    ∀ t, conjugateProfile g t ≠ 0 → |t| ≤ A := by
  intro t ht
  apply hg t
  intro hz
  apply ht
  simp only [conjugateProfile_apply, hz, star_zero]

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))


end

open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)


end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedGauss


open ActualEisensteinCubic

theorem completed_fiber_scalar_cost (deltaLoss K X a t Q c D S E : ℝ)
    (hδ : 0≤deltaLoss) (hK : 1≤K) (hX : 1≤X) (ha : 1≤a) (ht : 1≤t) (hQ : 1≤Q)
    (hc0 : 0<c) (hc : c≤K*Q) (hD : 1≤D) (hS : 1≤S) (hE : 1≤E)
    (hcost : c^2/(D*S*E^4)≤a*t^2*Q) :
    let k := K/(a*t)
    let y := k^2*c^2/(X*D*E^3)
    (k*y)^(2*deltaLoss)*(k+y)/(S*E)≤(K*Q)^(10*deltaLoss)*(K+K^2*Q/X)/a := by
  dsimp only
  let k : ℝ := K/(a*t)
  let y : ℝ := k^2*c^2/(X*D*E^3)
  change (k*y)^(2*deltaLoss)*(k+y)/(S*E)≤_
  have ha0 : 0<a := by linarith
  have ht0 : 0<t := by linarith
  have hX0 : 0<X := by linarith
  have hD0 : 0<D := by linarith
  have hS0 : 0<S := by linarith
  have hE0 : 0<E := by linarith
  have hK0 : 0<K := by linarith
  have hQ0 : 0<Q := by linarith
  have hk0 : 0<k := by dsimp [k]; positivity
  have hy0 : 0<y := by dsimp [y]; positivity
  have hat : 1≤a*t := one_le_mul_of_one_le_of_one_le ha ht
  have hk : k≤K := (div_le_self hK0.le hat)
  have hden : 1≤X*D*E^3 := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hX hD) (one_le_pow₀ hE)
  have hy : y≤K^2*(K*Q)^2 := by
    calc
      y ≤ k^2*c^2 := div_le_self (by positivity) hden
      _ ≤ K^2*(K*Q)^2 := mul_le_mul
        (pow_le_pow_left₀ hk0.le hk 2) (pow_le_pow_left₀ hc0.le hc 2) (by positivity) (by positivity)
  have hky : k*y≤(K*Q)^5 := by
    have hQ3 : 1≤Q^3 := one_le_pow₀ hQ
    calc
      k*y ≤ K*(K^2*(K*Q)^2) := mul_le_mul hk hy hy0.le hK0.le
      _ ≤ (K*(K^2*(K*Q)^2))*Q^3 := le_mul_of_one_le_right (by positivity) hQ3
      _ = (K*Q)^5 := by ring
  have hp : (k*y)^(2*deltaLoss)≤(K*Q)^(10*deltaLoss) := by
    have hh := Real.rpow_le_rpow (mul_pos hk0 hy0).le hky (by positivity : 0≤2*deltaLoss)
    convert! hh using 1
    rw [←Real.rpow_natCast_mul (mul_pos hK0 hQ0).le]
    congr 1
    ring
  have hfirst : k/(S*E)≤K/a := by
    have hse : 1≤t*(S*E) := one_le_mul_of_one_le_of_one_le ht (one_le_mul_of_one_le_of_one_le hS hE)
    calc
      k/(S*E) = (K/a)/(t*(S*E)) := by dsimp [k]; field_simp
      _ ≤ K/a := div_le_self (by positivity) hse
  have hsecond : y/(S*E)≤K^2*Q/(a*X) := by
    calc
      y/(S*E) = (k^2/X)*(c^2/(D*S*E^4)) := by dsimp [y]; field_simp
      _ ≤ (k^2/X)*(a*t^2*Q) := mul_le_mul_of_nonneg_left hcost (by positivity)
      _ = K^2*Q/(a*X) := by dsimp [k]; field_simp
  have hshape : (k+y)/(S*E)≤(K+K^2*Q/X)/a := by
    rw [add_div]
    have hh := add_le_add hfirst hsecond
    convert! hh using 1
    field_simp
  calc
    _ = (k*y)^(2*deltaLoss)*((k+y)/(S*E)) := by ring
    _ ≤ (K*Q)^(10*deltaLoss)*((K+K^2*Q/X)/a) :=
      mul_le_mul hp hshape (by positivity) (by positivity)
    _ = _ := by ring

theorem completed_conductor_norm_bound {ι : Type*} [Fintype ι]
    (I Q : Ideal O) (hI : I≠0) (hQ : Q≠0)
    (P : ι→Ideal O) (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀i,P i∣I*Q) :
    (Ideal.absNorm (∏i,P i):ℝ)≤(Ideal.absNorm I:ℝ)*(Ideal.absNorm Q:ℝ) := by
  have hd : (∏i,P i)∣I*Q := Fintype.prod_dvd_of_coprime hcop hpool
  have hn : 0<Ideal.absNorm (I*Q) := Nat.pos_of_ne_zero (fun hz =>
    mul_ne_zero hI hQ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hh := Nat.le_of_dvd hn (map_dvd Ideal.absNorm hd)
  exact_mod_cast (by simpa only [map_mul] using hh)


def completedShellWindow (x : ℝ) : ℂ :=
  if -Real.log 2≤x ∧ x≤0 then 1 else 0

theorem completedShellWindow_support (x : ℝ) (h : completedShellWindow x≠0) :
    |x|≤Real.log 2 := by
  have hx : -Real.log 2≤x ∧ x≤0 := by
    by_contra hn
    exact h (by simp [completedShellWindow,hn])
  apply abs_le.mpr
  exact ⟨hx.1,hx.2.trans (Real.log_nonneg (by norm_num))⟩

theorem completedShellWindow_norm (x : ℝ) : ‖completedShellWindow x‖≤1 := by
  unfold completedShellWindow
  split_ifs <;> simp

theorem completedShellWindow_log (x U : ℝ) (hx : 0<x) (hU : 0<U)
    (hlo : U/2≤x) (hhi : x≤U) : completedShellWindow (Real.log (x/U))=1 := by
  apply if_pos
  constructor
  · have hhalf : (1/2:ℝ)≤x/U := (le_div_iff₀ hU).mpr (by linarith)
    have hh := Real.strictMonoOn_log.monotoneOn (by norm_num : (1/2:ℝ)∈Set.Ioi 0)
      (show x/U∈Set.Ioi 0 from div_pos hx hU) hhalf
    simpa only [one_div,Real.log_inv] using hh
  · exact Real.log_nonpos (div_nonneg hx.le hU.le) ((div_le_one hU).mpr hhi)

theorem dyadic_root_product_bound (u v U B : ℝ) (hu : 0<u) (_hv : 0<v)
    (hU : 0<U) (hB : 0<B) (huU : U/2≤u) (hvB : B/2≤v) :
    Real.sqrt U*B≤4*(Real.sqrt u*v) := by
  have hs : Real.sqrt U≤2*Real.sqrt u := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hU.le,Real.sq_sqrt hu.le]
    nlinarith
  calc
    _ ≤ (2*Real.sqrt u)*(2*v) := mul_le_mul hs (by linarith) hB.le (by positivity)
    _ = _ := by ring

def reflectedDyadicCoefficient {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (η : Ideal O→Ideal O→ℂ) (r : ℝ)
    (n v : Ideal O) : ℂ :=
  η n v*reflectedBranch P hg j e
    (primaryGenerator (reflectionExtractedDivisor P j e 1*n))
    (primaryGenerator (reflectionExtractedDivisor P j e 2*v))/
    ((4*r*Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 1*n):ℝ)*
      (Ideal.absNorm (reflectionExtractedDivisor P j e 2*v):ℝ):ℝ):ℂ)

theorem reflectedDyadicCoefficient_norm {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (η : Ideal O→Ideal O→ℂ) (r U B : ℝ)
    (hr : 0<r) (hU : 0<U) (hB : 0<B) (n v : Ideal O) (hn : n≠0) (hv : v≠0)
    (hη : ‖η n v‖≤1) (hlo : U/2≤(Ideal.absNorm n:ℝ)) (hlov : B/2≤(Ideal.absNorm v:ℝ)) :
    ‖reflectedDyadicCoefficient P hg j e η r n v‖≤
      1/(Real.sqrt U*B*r*Real.sqrt
        ((Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
          (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ))) := by
  let D := reflectionExtractedDivisor P j e 1
  let E := reflectionExtractedDivisor P j e 2
  let S := reflectionExtractedDivisor P j e 0
  have hnorm (J : Ideal O) (hJ : J≠0) : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hDn := hnorm D (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) j e 1)
  have hEn := hnorm E (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) j e 2)
  have hSn := hnorm S (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) j e 0)
  have hnn := hnorm n hn
  have hvn := hnorm v hv
  have hlocal := reflectedBranch_normalized_bound P hg j e
    (primaryGenerator (D*n)) (primaryGenerator (E*v))
    (Ideal.absNorm n:ℝ) (Ideal.absNorm v:ℝ) hnn hvn
  change ‖reflectedBranch P hg j e (primaryGenerator (D*n)) (primaryGenerator (E*v))‖ /
      (Real.sqrt ((Ideal.absNorm D:ℝ)*(Ideal.absNorm n:ℝ))*
        ((Ideal.absNorm E:ℝ)*(Ideal.absNorm v:ℝ)))≤
      1/(Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm v:ℝ)*
        Real.sqrt ((Ideal.absNorm S:ℝ)*(Ideal.absNorm E:ℝ))) at hlocal
  have hbase : 0<Real.sqrt ((Ideal.absNorm S:ℝ)*(Ideal.absNorm E:ℝ)) := by positivity
  have hroot := dyadic_root_product_bound _ _ U B hnn hvn hU hB hlo hlov
  unfold reflectedDyadicCoefficient
  change ‖η n v*reflectedBranch P hg j e (primaryGenerator (D*n)) (primaryGenerator (E*v))/
    ((4*r*Real.sqrt (Ideal.absNorm (D*n):ℝ)*(Ideal.absNorm (E*v):ℝ):ℝ):ℂ)‖≤_
  rw [norm_div,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  simp only [map_mul,Nat.cast_mul]
  calc
    _ ≤ ‖reflectedBranch P hg j e (primaryGenerator (D*n)) (primaryGenerator (E*v))‖/
      (4*r*Real.sqrt ((Ideal.absNorm D:ℝ)*(Ideal.absNorm n:ℝ))*
        ((Ideal.absNorm E:ℝ)*(Ideal.absNorm v:ℝ))) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_of_le_one_left (norm_nonneg _) hη
    _ = (1/(4*r))*(‖reflectedBranch P hg j e (primaryGenerator (D*n)) (primaryGenerator (E*v))‖/
      (Real.sqrt ((Ideal.absNorm D:ℝ)*(Ideal.absNorm n:ℝ))*
        ((Ideal.absNorm E:ℝ)*(Ideal.absNorm v:ℝ)))) := by ring
    _ ≤ (1/(4*r))*(1/(Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm v:ℝ)*
      Real.sqrt ((Ideal.absNorm S:ℝ)*(Ideal.absNorm E:ℝ)))) :=
        mul_le_mul_of_nonneg_left hlocal (by positivity)
    _ = 1/(4*(Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm v:ℝ))*r*
      Real.sqrt ((Ideal.absNorm S:ℝ)*(Ideal.absNorm E:ℝ))) := by ring
    _ ≤ _ := by
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hroot hr.le) hbase.le


end CompletedGauss

end

end OAI

end


