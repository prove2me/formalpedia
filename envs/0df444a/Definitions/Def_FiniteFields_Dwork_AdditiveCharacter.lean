-- Prove2me | Definitions.Def_FiniteFields_Dwork_AdditiveCharacter
-- name    : FiniteFields_Dwork_AdditiveCharacter
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-20T01:30:54.341953+00:00
-- url     : https://prove2.me/theorems/9c28093e-e822-4e44-b5ec-e7be4873c3e3
-- title:
--   Artin–Hasse–Witt products and Dwork's additive character $\psi(x)=\zeta^{\operatorname{Tr}(x)}$
-- statement:
--   Let $k$ be a finite field with $q=p^a$ elements and let $L=K_0(\zeta)$ be the ramified coefficient field. Let $\eta$ be Dwork's parameter with $E_p(\eta)=\zeta$, and let $\theta(X)=E_p(\eta X)$ be the splitting series, as in the preceding files. This file builds the multiplicative Artin–Hasse–Witt calculus and the additive character used in Dwork's character sums.
--
--   1. **Artin–Hasse series over subrings.** If the coefficients of $E_p$ in a $\mathbb Q$-algebra $K$ lie in the image of an injective ring map $R\to K$, then $E_p$ descends to $R[[X]]$. This applies in particular to $R=W(k)\subset K_0$.
--   2. **Artin–Hasse–Witt products.** For a Witt vector $w=(w_0,w_1,\dots)\in W(R)$ the file defines the truncated products and their limit,
--   $$\mathrm{AH}_N(w)=\prod_{i<N}E_p\big(w_iX^{p^i}\big),\qquad \mathrm{AH}(w)=\prod_{i\ge0}E_p\big(w_iX^{p^i}\big)\in 1+XR[[X]],$$
--   where $\mathrm{AH}(w)$ is taken coefficientwise from the stable truncations. Here $1+XR[[X]]$ is the group of formal principal units, and $w\mapsto\mathrm{AH}(w)$ is a homomorphism from the additive group of $W(R)$ to this group. The file also defines the truncated version in $R[[X]]/(X^N)$, and the series $\exp(pX)$ descended to subrings.
--   3. **Specialization at $\eta$.** $U^1_L=\{z\in L : |z-1|<1\}$ is the group of principal units of $L$. For $w\in W(W(k))$, mapping $\mathrm{AH}(w)$ to $L[[X]]$ and evaluating at $\eta$ gives a homomorphism
--   $$W(W(k))\longrightarrow U^1_L,\qquad w\longmapsto \mathrm{AH}(w)(\eta).$$
--   The file also defines the Teichmüller trace vector $\sum_{i<a}[\sigma^i(w)]\in W(W(k))$ of an element $w\in W(k)$.
--   4. **The additive character.** With $\hat x$ the Teichmüller lift of $x\in k$ and $\operatorname{Tr}=\operatorname{Tr}_{k/\mathbb F_p}$, the file defines
--   $$\psi(x)=\zeta^{\operatorname{Tr}(x)},\qquad \theta(\hat x),\qquad \Theta(x)=\prod_{i=0}^{a-1}\theta\big(\widehat{x^{p^i}}\big).$$
--   These are the additive character $k\to L^\times$, the splitting value, and the product of splitting values over the Frobenius conjugates.
--
--   The file also contains the structural lemmas needed here: logarithmic-derivative identities for the Artin–Hasse factors, additivity of $\mathrm{AH}$ (through ghost components), compatibility of truncations, and the norm bounds that make the specialization land in $U^1_L$.
--
--   These are the objects of Dwork's §1, formulas (7)–(8): the additive character obtained from the splitting function at Teichmüller points. The product $\Theta$ is the one that is shown to equal $\psi$ elsewhere in the formalization. The Artin–Hasse–Witt homomorphism is the tool, absent from Dwork's paper, that the formalization uses to prove that identity.
--
--   **Formalization Note** The descent of $E_p$ and of $\exp(pX)$ to a subring picks coefficients with `Exists.choose` from proved membership statements. The additive character is Mathlib's `AddChar`, given by the primitive root $\zeta$ composed with the absolute trace to $\mathbb Z/p$.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648, §1: the additive character $\Theta_s(t')=\prod_{i<s}\theta(t^{p^i})$ of (7)–(8) and the remark on the Artin–Hasse exponential. Lean: ported from the `finite_fields` project (commit e8b5bf14), modules `WeilConjectures/Dwork/TruncatedArtinHasse/WittCoordinateProduct.lean`, `WeilConjectures/Dwork/FormalArtinHasse/PrincipalUnits.lean`, `WeilConjectures/Dwork/FormalArtinHasse/FormalProduct.lean`, `WeilConjectures/Dwork/FormalArtinHasse/FrobeniusQuotient.lean`, `WeilConjectures/Dwork/UnramifiedFrobenius.lean`, `WeilConjectures/Dwork/AdditiveCharacter.lean`, `WeilConjectures/Dwork/WittArtinHasseSpecialization/WittHom.lean`, `WeilConjectures/Dwork/WittTraceCharacter/TraceProduct.lean`, `WeilConjectures/Dwork/WittTraceCharacter/TraceLimit.lean`.

import Mathlib
import Definitions.Def_FiniteFields_Dwork_NuclearOperator

section
noncomputable section
open PowerSeries
open scoped Classical
namespace FiniteFields.Dwork
section Integral
variable {R K : Type*} [CommRing R] [CommRing K] [Algebra ℚ K] (ι : R →+* K) (p : ℕ)
omit [Algebra ℚ K] in
theorem powerSeries_ext_of_injective (hι : Function.Injective ι) {A B : R⟦X⟧}
    (h : PowerSeries.map ι A = PowerSeries.map ι B) : A = B := by
  refine PowerSeries.ext fun n => hι ?_
  have hn := congrArg (coeff n) h
  rwa [PowerSeries.coeff_map, PowerSeries.coeff_map] at hn
variable (hR : ∀ n, coeff n (artinHasseSeries K p) ∈ Set.range ι)
def artinHasseOver : R⟦X⟧ :=
  PowerSeries.mk fun n => (hR n).choose
@[simp]
theorem map_artinHasseOver :
    PowerSeries.map ι (artinHasseOver ι p hR) = artinHasseSeries K p := by
  ext n
  rw [PowerSeries.coeff_map, artinHasseOver, PowerSeries.coeff_mk]
  exact (hR n).choose_spec
theorem map_coeff_artinHasseOver (n : ℕ) :
    ι (coeff n (artinHasseOver ι p hR)) = coeff n (artinHasseSeries K p) := by
  rw [← PowerSeries.coeff_map, map_artinHasseOver]
@[simp]
theorem constantCoeff_artinHasseOver (hι : Function.Injective ι) :
    constantCoeff (artinHasseOver ι p hR) = 1 := by
  refine hι ?_
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, map_coeff_artinHasseOver,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_artinHasseSeries, map_one]
theorem derivative_artinHasseOver (hι : Function.Injective ι) :
    PowerSeries.derivative R (artinHasseOver ι p hR)
      = artinHasseOver ι p hR * artinHasseLogDerivOf R p := by
  refine powerSeries_ext_of_injective ι hι ?_
  rw [map_derivative, map_artinHasseOver, map_mul, map_artinHasseOver,
    map_artinHasseLogDerivOf, derivative_artinHasseSeries]
end Integral
section Factors
variable {R K : Type*} [CommRing R] [CommRing K] [Algebra ℚ K] (ι : R →+* K) (p : ℕ)
  [Fact p.Prime] (hR : ∀ n, coeff n (artinHasseSeries K p) ∈ Set.range ι)
theorem pPow_ne_zero (i : ℕ) : p ^ i ≠ 0 :=
  pow_ne_zero i (Fact.out : Nat.Prime p).ne_zero
def artinHasseFactor (a : R) (i : ℕ) : R⟦X⟧ :=
  PowerSeries.expand (p ^ i) (pPow_ne_zero p i)
    (PowerSeries.rescale a (artinHasseOver ι p hR))
def artinHasseFactorLogDeriv (a : R) (i : ℕ) : R⟦X⟧ :=
  PowerSeries.C ((p : R) ^ i * a) * X ^ (p ^ i - 1) *
    PowerSeries.expand (p ^ i) (pPow_ne_zero p i)
      (PowerSeries.rescale a (artinHasseLogDerivOf R p))
omit [Fact p.Prime] in
theorem derivative_rescale (a : R) (f : R⟦X⟧) :
    PowerSeries.derivative R (PowerSeries.rescale a f)
      = PowerSeries.C a * PowerSeries.rescale a (PowerSeries.derivative R f) := by
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_rescale, PowerSeries.coeff_derivative, pow_succ]
  ring
omit [Fact p.Prime] in
theorem derivative_expand (m : ℕ) (hm : m ≠ 0) (f : R⟦X⟧) :
    PowerSeries.derivative R (PowerSeries.expand m hm f)
      = PowerSeries.expand m hm (PowerSeries.derivative R f) * ((m : R⟦X⟧) * X ^ (m - 1)) := by
  have hsub : PowerSeries.HasSubst ((X : R⟦X⟧) ^ m) := by
    refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
    rw [map_pow, PowerSeries.constantCoeff_X, zero_pow hm]
  rw [PowerSeries.expand_apply, PowerSeries.expand_apply,
    PowerSeries.derivative_subst hsub, PowerSeries.derivative_pow, PowerSeries.derivative_X,
    mul_one]
theorem derivative_artinHasseFactor (hι : Function.Injective ι) (a : R) (i : ℕ) :
    PowerSeries.derivative R (artinHasseFactor ι p hR a i)
      = artinHasseFactor ι p hR a i * artinHasseFactorLogDeriv p a i := by
  have hcast : ((p ^ i : ℕ) : R⟦X⟧) = PowerSeries.C ((p : R) ^ i) := by
    rw [map_pow, map_natCast, Nat.cast_pow]
  simp only [artinHasseFactor, artinHasseFactorLogDeriv]
  rw [derivative_expand, derivative_rescale, derivative_artinHasseOver ι p hR hι]
  simp only [map_mul, PowerSeries.expand_C, hcast]
  ring
@[simp]
theorem constantCoeff_artinHasseFactor (hι : Function.Injective ι) (a : R) (i : ℕ) :
    constantCoeff (artinHasseFactor ι p hR a i) = 1 := by
  rw [artinHasseFactor, PowerSeries.constantCoeff_expand,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_artinHasseOver ι p hR hι]
theorem coeff_artinHasseFactor_eq_zero (a : R) (i t : ℕ) (ht : 0 < t) (ht' : t < p ^ i) :
    coeff t (artinHasseFactor ι p hR a i) = 0 := by
  rw [artinHasseFactor, PowerSeries.coeff_expand_of_not_dvd]
  exact fun hdvd => absurd (Nat.le_of_dvd ht hdvd) (not_le.mpr ht')
theorem coeff_artinHasseFactorLogDeriv_of_le (a : R) (i t : ℕ) (ht : p ^ i - 1 ≤ t) :
    coeff t (artinHasseFactorLogDeriv p a i)
      = (p : R) ^ i * a *
          coeff (t - (p ^ i - 1))
            (PowerSeries.expand (p ^ i) (pPow_ne_zero p i)
              (PowerSeries.rescale a (artinHasseLogDerivOf R p))) := by
  rw [artinHasseFactorLogDeriv, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    if_pos ht]
theorem coeff_artinHasseFactorLogDeriv_of_lt' (a : R) (i t : ℕ) (ht : t < p ^ i - 1) :
    coeff t (artinHasseFactorLogDeriv p a i) = 0 := by
  rw [artinHasseFactorLogDeriv, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    if_neg (not_le.mpr ht), mul_zero]
theorem coeff_artinHasseFactorLogDeriv_pPow (a : R) (i j : ℕ) :
    coeff (p ^ (i + j) - 1) (artinHasseFactorLogDeriv p a i) = -((p : R) ^ i * a ^ p ^ j) := by
  have hA : 1 ≤ p ^ i := Nat.one_le_iff_ne_zero.mpr (pPow_ne_zero p i)
  have hB : 1 ≤ p ^ j := Nat.one_le_iff_ne_zero.mpr (pPow_ne_zero p j)
  have hAB : p ^ (i + j) = p ^ i * p ^ j := pow_add p i j
  have hmul : p ^ i ≤ p ^ i * p ^ j := Nat.le_mul_of_pos_right _ hB
  have hle : p ^ i - 1 ≤ p ^ (i + j) - 1 := by rw [hAB]; omega
  have hsub : p ^ (i + j) - 1 - (p ^ i - 1) = p ^ i * (p ^ j - 1) := by
    rw [hAB, Nat.sub_sub, Nat.add_sub_cancel' hA, Nat.mul_sub, mul_one]
  have hpow : a * a ^ (p ^ j - 1) = a ^ p ^ j := by
    rw [← pow_succ' a (p ^ j - 1), Nat.sub_add_cancel hB]
  rw [coeff_artinHasseFactorLogDeriv_of_le p a i _ hle, hsub, PowerSeries.coeff_expand_mul,
    PowerSeries.coeff_rescale, coeff_artinHasseLogDerivOf, if_pos ⟨j, by omega⟩]
  calc (p : R) ^ i * a * (a ^ (p ^ j - 1) * -1)
      = -((p : R) ^ i * (a * a ^ (p ^ j - 1))) := by ring
    _ = -((p : R) ^ i * a ^ p ^ j) := by rw [hpow]
theorem coeff_artinHasseFactorLogDeriv_eq_zero (a : R) (i t : ℕ) (ht : ∀ n, p ^ n ≠ t + 1) :
    coeff t (artinHasseFactorLogDeriv p a i) = 0 := by
  have hA : 1 ≤ p ^ i := Nat.one_le_iff_ne_zero.mpr (pPow_ne_zero p i)
  rcases lt_or_ge t (p ^ i - 1) with h | h
  · exact coeff_artinHasseFactorLogDeriv_of_lt' p a i t h
  rw [coeff_artinHasseFactorLogDeriv_of_le p a i t h, PowerSeries.coeff_expand]
  split_ifs with hdvd
  · rw [PowerSeries.coeff_rescale, coeff_artinHasseLogDerivOf, if_neg, mul_zero, mul_zero]
    rintro ⟨j, hj⟩
    refine ht (i + j) ?_
    have hu : p ^ i * ((t - (p ^ i - 1)) / p ^ i) = t - (p ^ i - 1) :=
      Nat.mul_div_cancel' hdvd
    have ht' : t - (p ^ i - 1) + (p ^ i - 1) = t := Nat.sub_add_cancel h
    calc p ^ (i + j) = p ^ i * p ^ j := pow_add p i j
      _ = p ^ i * ((t - (p ^ i - 1)) / p ^ i + 1) := by rw [hj]
      _ = p ^ i * ((t - (p ^ i - 1)) / p ^ i) + p ^ i := by ring
      _ = t + 1 := by omega
  · rw [mul_zero]
theorem coeff_artinHasseFactorLogDeriv_of_lt (a : R) (i n : ℕ) (hni : n < i) :
    coeff (p ^ n - 1) (artinHasseFactorLogDeriv p a i) = 0 := by
  refine coeff_artinHasseFactorLogDeriv_of_lt' p a i _ ?_
  have h1 : 1 ≤ p ^ n := Nat.one_le_iff_ne_zero.mpr (pPow_ne_zero p n)
  have h2 : p ^ n < p ^ i := Nat.pow_lt_pow_right (Fact.out : Nat.Prime p).one_lt hni
  omega
end Factors
section Uniqueness
variable {A : Type*} [CommRing A] [Algebra ℚ A]
theorem coeff_eq_of_derivative_eq_mul {N : ℕ} {f g h₁ h₂ : A⟦X⟧}
    (hf : PowerSeries.derivative A f = f * h₁)
    (hg : PowerSeries.derivative A g = g * h₂)
    (h0 : constantCoeff f = constantCoeff g)
    (hh : ∀ j, j + 1 < N → coeff j h₁ = coeff j h₂) :
    ∀ m, m < N → coeff m f = coeff m g := by
  letI : IsAddTorsionFree A := IsAddTorsionFree.of_module_rat A
  exact PowerSeries.coeff_eq_of_derivative_eq_mul hf hg h0 hh
end Uniqueness
end FiniteFields.Dwork
end
end

section
noncomputable section
open PowerSeries
open scoped Classical
namespace FiniteFields.Dwork
section Product
variable {R K : Type*} [CommRing R] [CommRing K] [Algebra ℚ K] (ι : R →+* K) (p : ℕ)
  [Fact p.Prime] (hR : ∀ n, coeff n (artinHasseSeries K p) ∈ Set.range ι)
def artinHasseWittSeries (N : ℕ) (w : WittVector p R) : R⟦X⟧ :=
  ∏ i ∈ Finset.range N, artinHasseFactor ι p hR (w.coeff i) i
def artinHasseWittLogDeriv (N : ℕ) (w : WittVector p R) : R⟦X⟧ :=
  ∑ i ∈ Finset.range N, artinHasseFactorLogDeriv p (w.coeff i) i
theorem constantCoeff_artinHasseWittSeries (hι : Function.Injective ι) (N : ℕ)
    (w : WittVector p R) : constantCoeff (artinHasseWittSeries ι p hR N w) = 1 := by
  rw [artinHasseWittSeries, map_prod]
  exact Finset.prod_eq_one fun i _ => constantCoeff_artinHasseFactor ι p hR hι _ i
theorem derivative_artinHasseWittSeries (hι : Function.Injective ι) (N : ℕ)
    (w : WittVector p R) :
    PowerSeries.derivative R (artinHasseWittSeries ι p hR N w)
      = artinHasseWittSeries ι p hR N w * artinHasseWittLogDeriv p N w := by
  rw [artinHasseWittSeries, artinHasseWittLogDeriv]
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ, Derivation.leibniz, ih,
      derivative_artinHasseFactor ι p hR hι]
    simp only [smul_eq_mul]
    ring
theorem coeff_artinHasseWittLogDeriv_pPow (N n : ℕ) (hn : n < N) (w : WittVector p R) :
    coeff (p ^ n - 1) (artinHasseWittLogDeriv p N w) = -WittVector.ghostComponent n w := by
  have hsub : Finset.range (n + 1) ⊆ Finset.range N := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hzero : ∀ i ∈ Finset.range N, i ∉ Finset.range (n + 1) →
      coeff (p ^ n - 1) (artinHasseFactorLogDeriv p (w.coeff i) i) = 0 := by
    intro i _ hi
    rw [Finset.mem_range, not_lt] at hi
    exact coeff_artinHasseFactorLogDeriv_of_lt p _ i n (by omega)
  have hterm : ∀ i ∈ Finset.range (n + 1),
      coeff (p ^ n - 1) (artinHasseFactorLogDeriv p (w.coeff i) i)
        = -((p : R) ^ i * w.coeff i ^ p ^ (n - i)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h := coeff_artinHasseFactorLogDeriv_pPow p (w.coeff i) i (n - i)
    rwa [show i + (n - i) = n by omega] at h
  rw [artinHasseWittLogDeriv, map_sum, ← Finset.sum_subset hsub hzero,
    Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, WittVector.ghostComponent_apply,
    aeval_wittPolynomial p ℤ w.coeff n]
theorem coeff_artinHasseWittLogDeriv_eq_zero (N t : ℕ) (ht : ∀ n, p ^ n ≠ t + 1)
    (w : WittVector p R) : coeff t (artinHasseWittLogDeriv p N w) = 0 := by
  rw [artinHasseWittLogDeriv, map_sum]
  exact Finset.sum_eq_zero fun i _ => coeff_artinHasseFactorLogDeriv_eq_zero p _ i t ht
theorem coeff_artinHasseWittLogDeriv_add (N t : ℕ) (ht : t + 1 < N) (w w' : WittVector p R) :
    coeff t (artinHasseWittLogDeriv p N (w + w'))
      = coeff t (artinHasseWittLogDeriv p N w) + coeff t (artinHasseWittLogDeriv p N w') := by
  by_cases h : ∃ n, p ^ n = t + 1
  · obtain ⟨n, hn⟩ := h
    have hlt : n < p ^ n := Nat.lt_pow_self (Fact.out : Nat.Prime p).one_lt
    have hnN : n < N := by omega
    have ht' : p ^ n - 1 = t := by omega
    rw [← ht', coeff_artinHasseWittLogDeriv_pPow p N n hnN,
      coeff_artinHasseWittLogDeriv_pPow p N n hnN, coeff_artinHasseWittLogDeriv_pPow p N n hnN,
      map_add, neg_add]
  · rw [not_exists] at h
    rw [coeff_artinHasseWittLogDeriv_eq_zero p N t h, coeff_artinHasseWittLogDeriv_eq_zero p N t h,
      coeff_artinHasseWittLogDeriv_eq_zero p N t h, add_zero]
omit [Fact p.Prime] [Algebra ℚ K] in
theorem constantCoeff_map' (f : R⟦X⟧) :
    constantCoeff (PowerSeries.map ι f) = ι (constantCoeff f) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]
theorem artinHasseFactor_of_zero (hι : Function.Injective ι) (i : ℕ) :
    artinHasseFactor ι p hR 0 i = 1 := by
  rw [artinHasseFactor, PowerSeries.rescale_zero_apply,
    constantCoeff_artinHasseOver ι p hR hι, map_one, map_one]
omit [Fact p.Prime] in
theorem constantCoeff_rescale_artinHasseOver (hι : Function.Injective ι) (a : R) :
    constantCoeff (PowerSeries.rescale a (artinHasseOver ι p hR)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero,
    one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_artinHasseOver ι p hR hι]
theorem artinHasseWittSeries_zero (hι : Function.Injective ι) (N : ℕ) :
    artinHasseWittSeries ι p hR N 0 = 1 := by
  rw [artinHasseWittSeries]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [show (0 : WittVector p R).coeff i = 0 from by simp, artinHasseFactor_of_zero ι p hR hι]
theorem truncateSeries_artinHasseFactor (hι : Function.Injective ι) (a : R) {N i : ℕ}
    (hi : N ≤ i) : truncateSeries R N (artinHasseFactor ι p hR a i) = 1 := by
  have hlt : N < p ^ i := lt_of_le_of_lt hi (Nat.lt_pow_self (Fact.out : Nat.Prime p).one_lt)
  rw [← map_one (truncateSeries R N)]
  refine truncateSeries_eq_iff.mpr fun m hm => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      constantCoeff_artinHasseFactor ι p hR hι, map_one]
  · rw [coeff_artinHasseFactor_eq_zero ι p hR a i m hm0 (by omega), PowerSeries.coeff_one,
      if_neg (by omega)]
theorem truncateSeries_artinHasseWittSeries (hι : Function.Injective ι) {N M : ℕ} (h : N ≤ M)
    (w : WittVector p R) :
    truncateSeries R N (artinHasseWittSeries ι p hR M w)
      = truncateSeries R N (artinHasseWittSeries ι p hR N w) := by
  have hsub : Finset.range N ⊆ Finset.range M := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  rw [artinHasseWittSeries, artinHasseWittSeries, map_prod, map_prod]
  refine (Finset.prod_subset hsub ?_).symm
  intro i _ hi
  rw [Finset.mem_range] at hi
  exact truncateSeries_artinHasseFactor ι p hR hι _ (by omega)
theorem derivative_artinHasseWittSeries_mul (hι : Function.Injective ι) (N : ℕ)
    (w w' : WittVector p R) :
    PowerSeries.derivative R
        (artinHasseWittSeries ι p hR N w * artinHasseWittSeries ι p hR N w')
      = artinHasseWittSeries ι p hR N w * artinHasseWittSeries ι p hR N w' *
          (artinHasseWittLogDeriv p N w + artinHasseWittLogDeriv p N w') := by
  rw [Derivation.leibniz, derivative_artinHasseWittSeries ι p hR hι,
    derivative_artinHasseWittSeries ι p hR hι]
  simp only [smul_eq_mul]
  ring
theorem coeff_artinHasseWittSeries_add (hι : Function.Injective ι) (N : ℕ)
    (w w' : WittVector p R) (m : ℕ) (hm : m < N) :
    coeff m (artinHasseWittSeries ι p hR N (w + w'))
      = coeff m (artinHasseWittSeries ι p hR N w * artinHasseWittSeries ι p hR N w') := by
  refine hι ?_
  rw [← PowerSeries.coeff_map, ← PowerSeries.coeff_map]
  refine coeff_eq_of_derivative_eq_mul (N := N)
    (h₁ := PowerSeries.map ι (artinHasseWittLogDeriv p N (w + w')))
    (h₂ := PowerSeries.map ι
      (artinHasseWittLogDeriv p N w + artinHasseWittLogDeriv p N w')) ?_ ?_ ?_ ?_ m hm
  · rw [← map_derivative, derivative_artinHasseWittSeries ι p hR hι, map_mul]
  · rw [← map_derivative, derivative_artinHasseWittSeries_mul ι p hR hι, map_mul]
  · rw [constantCoeff_map', constantCoeff_map', constantCoeff_artinHasseWittSeries ι p hR hι,
      map_mul, constantCoeff_artinHasseWittSeries ι p hR hι,
      constantCoeff_artinHasseWittSeries ι p hR hι, mul_one]
  · intro j hj
    have hadd := coeff_artinHasseWittLogDeriv_add p N j hj w w'
    simp only [PowerSeries.coeff_map, map_add, hadd]
def truncatedArtinHasseProduct (hι : Function.Injective ι) (N : ℕ) (w : WittVector p R) :
    TruncatedPrincipalUnit R N :=
  TruncatedPrincipalUnit.ofSeries (artinHasseWittSeries ι p hR N w)
    (constantCoeff_artinHasseWittSeries ι p hR hι N w)
theorem truncatedArtinHasseProduct_zero (hι : Function.Injective ι) (N : ℕ) :
    truncatedArtinHasseProduct ι p hR hι N 0 = 1 := by
  refine TruncatedPrincipalUnit.ext ?_
  rw [truncatedArtinHasseProduct, TruncatedPrincipalUnit.val_ofSeries,
    TruncatedPrincipalUnit.val_one, artinHasseWittSeries_zero ι p hR hι N, map_one]
theorem truncatedArtinHasseProduct_add (hι : Function.Injective ι) (N : ℕ)
    (w w' : WittVector p R) :
    truncatedArtinHasseProduct ι p hR hι N (w + w')
      = truncatedArtinHasseProduct ι p hR hι N w * truncatedArtinHasseProduct ι p hR hι N w' := by
  refine TruncatedPrincipalUnit.ext ?_
  rw [truncatedArtinHasseProduct, truncatedArtinHasseProduct, truncatedArtinHasseProduct,
    TruncatedPrincipalUnit.val_mul, TruncatedPrincipalUnit.val_ofSeries,
    TruncatedPrincipalUnit.val_ofSeries, TruncatedPrincipalUnit.val_ofSeries, ← map_mul]
  exact truncateSeries_eq_iff.mpr fun m hm => coeff_artinHasseWittSeries_add ι p hR hι N w w' m hm
end Product
end FiniteFields.Dwork
end
end

section
noncomputable section
open PowerSeries
open scoped Classical
namespace FiniteFields.Dwork
section DworkCarrier
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
theorem ratCast_mem_range_coefficientRingAlgebraMap (q : ℚ) (hq : Rat.padicValuation p q ≤ 1) :
    (q : CoefficientField k p) ∈ Set.range (coefficientRingAlgebraMap k p) := by
  have hden : ¬p ∣ q.den := Rat.padicValuation_le_one_iff.mp hq
  have hdenk : (q.den : k) ≠ 0 := fun hz => hden ((CharP.cast_eq_zero_iff k p q.den).mp hz)
  have hdenUnit : IsUnit (q.den : CoefficientRing k p) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    change WittVector.constantCoeff (q.den : CoefficientRing k p) ≠ 0
    simpa only [map_natCast] using hdenk
  obtain ⟨u, hu⟩ := hdenUnit
  refine ⟨(q.num : CoefficientRing k p) * ((u⁻¹ : (CoefficientRing k p)ˣ) :
    CoefficientRing k p), ?_⟩
  have hden' : coefficientRingAlgebraMap k p ((u : (CoefficientRing k p)ˣ) : CoefficientRing k p)
      = (q.den : CoefficientField k p) := by
    rw [hu, map_natCast]
  have hden0 : (q.den : CoefficientField k p) ≠ 0 := by
    rw [← hden']
    exact (u.isUnit.map (coefficientRingAlgebraMap k p)).ne_zero
  rw [Rat.cast_def, eq_div_iff hden0, ← hden', ← map_mul,
    ← map_intCast (coefficientRingAlgebraMap k p) q.num]
  congr 1
  rw [mul_assoc, Units.inv_mul, mul_one]
theorem artinHasseSeries_mem_range_coefficientRingAlgebraMap (n : ℕ) :
    coeff n (artinHasseSeries (CoefficientField k p) p)
      ∈ Set.range (coefficientRingAlgebraMap k p) := by
  rw [artinHasseSeries, PowerSeries.coeff_map,
    eq_ratCast (algebraMap ℚ (CoefficientField k p))]
  exact ratCast_mem_range_coefficientRingAlgebraMap k p _
    (artinHasseExponential_isPIntegral p n)
def dworkArtinHasseOver : (CoefficientRing k p)⟦X⟧ :=
  artinHasseOver (coefficientRingAlgebraMap k p) p
    (artinHasseSeries_mem_range_coefficientRingAlgebraMap k p)
end DworkCarrier
end FiniteFields.Dwork
end
end

section
noncomputable section
open PowerSeries
namespace FiniteFields.Dwork
structure FormalPrincipalUnit (R : Type*) [CommRing R] where
  val : R⟦X⟧
  constantCoeff_val : constantCoeff val = 1
namespace FormalPrincipalUnit
variable {R : Type*} [CommRing R]
@[ext]
theorem ext {a b : FormalPrincipalUnit R} (h : a.val = b.val) : a = b := by
  cases a
  cases b
  subst h
  rfl
instance instMul : Mul (FormalPrincipalUnit R) where
  mul a b := ⟨a.val * b.val, by rw [map_mul, a.constantCoeff_val, b.constantCoeff_val, one_mul]⟩
instance instOne : One (FormalPrincipalUnit R) where
  one := ⟨1, map_one _⟩
instance instInv : Inv (FormalPrincipalUnit R) where
  inv a := ⟨invOfUnit a.val 1, by rw [constantCoeff_invOfUnit]; simp⟩
@[simp] theorem val_mul (a b : FormalPrincipalUnit R) : (a * b).val = a.val * b.val := rfl
@[simp] theorem val_one : (1 : FormalPrincipalUnit R).val = 1 := rfl
@[simp] theorem val_inv (a : FormalPrincipalUnit R) : a⁻¹.val = invOfUnit a.val 1 := rfl
instance instCommGroup : CommGroup (FormalPrincipalUnit R) where
  mul_assoc _ _ _ := ext (mul_assoc _ _ _)
  one_mul _ := ext (one_mul _)
  mul_one _ := ext (mul_one _)
  mul_comm _ _ := ext (mul_comm _ _)
  inv_mul_cancel a := by
    refine ext ?_
    rw [val_mul, val_inv, val_one, invOfUnit_mul a.val 1 (by simp [a.constantCoeff_val])]
end FormalPrincipalUnit
def formalPrincipalUnit_truncate (R : Type*) [CommRing R] (N : ℕ) :
    FormalPrincipalUnit R →* TruncatedPrincipalUnit R N where
  toFun a := TruncatedPrincipalUnit.ofSeries a.val a.constantCoeff_val
  map_one' := TruncatedPrincipalUnit.ofSeries_one
  map_mul' _ _ := TruncatedPrincipalUnit.ofSeries_mul _ _
@[simp]
theorem formalPrincipalUnit_truncate_apply {R : Type*} [CommRing R] (N : ℕ)
    (a : FormalPrincipalUnit R) :
    formalPrincipalUnit_truncate R N a = TruncatedPrincipalUnit.ofSeries a.val a.constantCoeff_val :=
  rfl
theorem formalPrincipalUnit_ext {R : Type*} [CommRing R] {a b : FormalPrincipalUnit R}
    (h : ∀ N, formalPrincipalUnit_truncate R N a = formalPrincipalUnit_truncate R N b) : a = b := by
  refine FormalPrincipalUnit.ext (PowerSeries.ext fun m => ?_)
  exact (TruncatedPrincipalUnit.ofSeries_eq_ofSeries_iff a.constantCoeff_val
    b.constantCoeff_val).mp (h (m + 1)) m (by omega)
end FiniteFields.Dwork
end
end

section
noncomputable section
open PowerSeries
namespace FiniteFields.Dwork
section Formal
variable {R K : Type*} [CommRing R] [CommRing K] [Algebra ℚ K] (ι : R →+* K) (p : ℕ)
  [Fact p.Prime] (hR : ∀ n, coeff n (artinHasseSeries K p) ∈ Set.range ι)
theorem coeff_artinHasseWittSeries_stable (hι : Function.Injective ι) {N M m : ℕ} (hm : m < N)
    (hNM : N ≤ M) (w : WittVector p R) :
    coeff m (artinHasseWittSeries ι p hR M w) = coeff m (artinHasseWittSeries ι p hR N w) :=
  truncateSeries_eq_iff.mp (truncateSeries_artinHasseWittSeries ι p hR hι hNM w) m hm
def formalArtinHasseSeries (w : WittVector p R) : R⟦X⟧ :=
  PowerSeries.mk fun m => coeff m (artinHasseWittSeries ι p hR (m + 1) w)
theorem coeff_formalArtinHasseSeries (hι : Function.Injective ι) (w : WittVector p R) {N m : ℕ}
    (hm : m < N) :
    coeff m (formalArtinHasseSeries ι p hR w) = coeff m (artinHasseWittSeries ι p hR N w) := by
  rw [formalArtinHasseSeries, PowerSeries.coeff_mk]
  rcases le_total (m + 1) N with h | h
  · exact (coeff_artinHasseWittSeries_stable ι p hR hι (by omega) h w).symm
  · exact coeff_artinHasseWittSeries_stable ι p hR hι hm h w
theorem constantCoeff_formalArtinHasseSeries (hι : Function.Injective ι) (w : WittVector p R) :
    constantCoeff (formalArtinHasseSeries ι p hR w) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_formalArtinHasseSeries ι p hR hι w (N := 1) (by omega),
    PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_artinHasseWittSeries ι p hR hι]
def formalArtinHasseProduct (hι : Function.Injective ι) (w : WittVector p R) :
    FormalPrincipalUnit R :=
  ⟨formalArtinHasseSeries ι p hR w, constantCoeff_formalArtinHasseSeries ι p hR hι w⟩
@[simp]
theorem val_formalArtinHasseProduct (hι : Function.Injective ι) (w : WittVector p R) :
    (formalArtinHasseProduct ι p hR hι w).val = formalArtinHasseSeries ι p hR w := rfl
theorem formalArtinHasseProduct_truncate (hι : Function.Injective ι) (N : ℕ)
    (w : WittVector p R) :
    formalPrincipalUnit_truncate R N (formalArtinHasseProduct ι p hR hι w)
      = truncatedArtinHasseProduct ι p hR hι N w :=
  (TruncatedPrincipalUnit.ofSeries_eq_ofSeries_iff
    (constantCoeff_formalArtinHasseSeries ι p hR hι w)
    (constantCoeff_artinHasseWittSeries ι p hR hι N w)).mpr fun _ hm =>
      coeff_formalArtinHasseSeries ι p hR hι w hm
theorem formalArtinHasseProduct_zero (hι : Function.Injective ι) :
    formalArtinHasseProduct ι p hR hι 0 = 1 := by
  refine formalPrincipalUnit_ext fun N => ?_
  rw [formalArtinHasseProduct_truncate, map_one, truncatedArtinHasseProduct_zero]
theorem formalArtinHasseProduct_add (hι : Function.Injective ι) (w w' : WittVector p R) :
    formalArtinHasseProduct ι p hR hι (w + w')
      = formalArtinHasseProduct ι p hR hι w * formalArtinHasseProduct ι p hR hι w' := by
  refine formalPrincipalUnit_ext fun N => ?_
  rw [formalArtinHasseProduct_truncate, map_mul, formalArtinHasseProduct_truncate,
    formalArtinHasseProduct_truncate, truncatedArtinHasseProduct_add]
def formalArtinHasseHom (hι : Function.Injective ι) :
    WittVector p R →+ Additive (FormalPrincipalUnit R) where
  toFun w := Additive.ofMul (formalArtinHasseProduct ι p hR hι w)
  map_zero' := congrArg Additive.ofMul (formalArtinHasseProduct_zero ι p hR hι)
  map_add' w w' := congrArg Additive.ofMul (formalArtinHasseProduct_add ι p hR hι w w')
@[simp]
theorem toMul_formalArtinHasseHom (hι : Function.Injective ι) (w : WittVector p R) :
    Additive.toMul (formalArtinHasseHom ι p hR hι w) = formalArtinHasseProduct ι p hR hι w := rfl
end Formal
end FiniteFields.Dwork
end
end

section
noncomputable section
open PowerSeries
namespace FiniteFields.Dwork
section Formal
def frobeniusQuotientSeries (K : Type*) [CommRing K] [Algebra ℚ K] (p : ℕ) : K⟦X⟧ :=
  PowerSeries.map (algebraMap ℚ K) (PowerSeries.rescale (p : ℚ) (PowerSeries.exp ℚ))
section FrobeniusQuotient
variable {R K : Type*} [CommRing R] [CommRing K] [Algebra ℚ K] (ι : R →+* K) (p : ℕ)
  (hE : ∀ n, coeff n (frobeniusQuotientSeries K p) ∈ Set.range ι)
def frobeniusQuotientOver : R⟦X⟧ :=
  PowerSeries.mk fun n => (hE n).choose
end FrobeniusQuotient
end Formal
end FiniteFields.Dwork
end
end

section
noncomputable section
open PowerSeries
namespace FiniteFields.Dwork
section DworkCarrier
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
omit [Field k] [CharP k p] [Finite k] in
theorem frobeniusQuotient_isPIntegral (n : ℕ) :
    Rat.padicValuation p (coeff n (PowerSeries.rescale (p : ℚ) (PowerSeries.exp ℚ))) ≤ 1 := by
  have hpv : Rat.padicValuation p ((p : ℚ)) ≤ 1 := by
    rw [show ((p : ℚ)) = (((p : ℤ)) : ℚ) by push_cast; ring, Rat.padicValuation_cast]
    exact Int.padicValuation_le_one p (p : ℤ)
  obtain ⟨h0, hpos⟩ := artinHasse_frobeniusQuotient_pDivisible p
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_one]
  · obtain ⟨a, ha, hcoeff⟩ := hpos n (by omega)
    rw [hcoeff, map_mul]
    exact mul_le_one' hpv ha
theorem frobeniusQuotientSeries_mem_range_coefficientRingAlgebraMap (n : ℕ) :
    coeff n (frobeniusQuotientSeries (CoefficientField k p) p)
      ∈ Set.range (coefficientRingAlgebraMap k p) := by
  rw [frobeniusQuotientSeries, PowerSeries.coeff_map,
    eq_ratCast (algebraMap ℚ (CoefficientField k p))]
  exact ratCast_mem_range_coefficientRingAlgebraMap k p _ (frobeniusQuotient_isPIntegral p n)
def dworkFormalArtinHasseProduct (w : WittVector p (CoefficientRing k p)) :
    FormalPrincipalUnit (CoefficientRing k p) :=
  formalArtinHasseProduct (coefficientRingAlgebraMap k p) p
    (artinHasseSeries_mem_range_coefficientRingAlgebraMap k p)
    (coefficientRingAlgebraMap_injective k p) w
theorem dworkFormalArtinHasseProduct_zero : dworkFormalArtinHasseProduct k p 0 = 1 :=
  formalArtinHasseProduct_zero _ _ _ (coefficientRingAlgebraMap_injective k p)
theorem dworkFormalArtinHasseProduct_add (w w' : WittVector p (CoefficientRing k p)) :
    dworkFormalArtinHasseProduct k p (w + w')
      = dworkFormalArtinHasseProduct k p w * dworkFormalArtinHasseProduct k p w' :=
  formalArtinHasseProduct_add _ _ _ (coefficientRingAlgebraMap_injective k p) w w'
end DworkCarrier
end FiniteFields.Dwork
end
end

section
noncomputable section
open scoped BigOperators WithZero
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [hpChar : CharP k p] [Finite k]
local instance dw4eResiduePrimeAlgebra : Algebra (ZMod p) k := ZMod.algebra k p
local instance dw4eDecidableEq : DecidableEq k := Classical.decEq k
def ramifiedTeichmullerLift (x : k) : DworkCyclotomicField k p :=
  algebraMap (CoefficientField k p) (DworkCyclotomicField k p)
    (coefficientRingAlgebraMap k p (teichmullerLift k p x))
def dworkSplittingValue (x : k) : DworkCyclotomicField k p :=
  dworkPowerSeriesEval k p (dworkSplittingFunction k p)
    (ramifiedTeichmullerLift k p x)
 def dworkPrimeFieldCharacter :
    AddChar (ZMod p) (DworkCyclotomicField k p) :=
  AddChar.zmodChar p (dworkPrimitiveRoot_isPrimitiveRoot k p).pow_eq_one
def dworkTraceAdditiveCharacter : AddChar k (DworkCyclotomicField k p) :=
  (dworkPrimeFieldCharacter k p).compAddMonoidHom
    (Algebra.trace (ZMod p) k).toAddMonoidHom
@[simp]
theorem dworkTraceAdditiveCharacter_apply (x : k) :
    dworkTraceAdditiveCharacter k p x =
      dworkPrimitiveRoot k p ^ (Algebra.trace (ZMod p) k x).val :=
  rfl
def dworkFrobeniusConjugateProduct (x : k) : DworkCyclotomicField k p :=
  ∏ i ∈ Finset.range (Module.finrank (ZMod p) k),
    dworkSplittingValue k p (x ^ (p ^ i))
section Extension
variable (k₀ : Type) (p₀ : ℕ) [Fact p₀.Prime]
  [Field k₀] [CharP k₀ p₀] [Finite k₀]
local instance dw4eExtensionCharP (n : ℕ) :
    CharP (FiniteFields.Extension k₀ p₀ n) p₀ :=
  charP_of_injective_algebraMap
    (algebraMap k₀ (FiniteFields.Extension k₀ p₀ n)).injective p₀
end Extension
end FiniteFields.Dwork
end
end

section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
def cyclotomicCoefficientMap : CoefficientRing k p →+* DworkCyclotomicField k p :=
  (algebraMap (CoefficientField k p) (DworkCyclotomicField k p)).comp
    (coefficientRingAlgebraMap k p)
@[simp]
theorem cyclotomicCoefficientMap_apply (x : CoefficientRing k p) :
    cyclotomicCoefficientMap k p x
      = algebraMap (CoefficientField k p) (DworkCyclotomicField k p)
          (coefficientRingAlgebraMap k p x) := rfl
theorem norm_coefficientRingAlgebraMap_le_one (x : CoefficientRing k p) :
    ‖coefficientRingAlgebraMap k p x‖ ≤ 1 := by
  rw [Valued.toNormedField.norm_le_one_iff]
  rw [show coefficientRingAlgebraMap k p x =
      (((WithVal.equiv (coefficientValuation k p)).symm
        (algebraMap (CoefficientRing k p) (CoefficientFractionField k p) x) :
          WithVal (coefficientValuation k p)) : CoefficientField k p) by rfl]
  rw [Valued.valuedCompletion_apply]
  change coefficientValuation k p
      (algebraMap (CoefficientRing k p) (CoefficientFractionField k p) x) ≤ 1
  exact (IsDiscreteValuationRing.maximalIdeal (CoefficientRing k p)).valuation_le_one
    (K := CoefficientFractionField k p) x
theorem norm_cyclotomicCoefficientMap_le_one (x : CoefficientRing k p) :
    ‖cyclotomicCoefficientMap k p x‖ ≤ 1 := by
  rw [cyclotomicCoefficientMap_apply, dworkCyclotomicField_norm_algebraMap]
  exact norm_coefficientRingAlgebraMap_le_one k p x
def mapFormalPrincipalUnitToCyclotomic (a : FormalPrincipalUnit (CoefficientRing k p)) :
    FormalPrincipalUnit (DworkCyclotomicField k p) where
  val := PowerSeries.map (cyclotomicCoefficientMap k p) a.val
  constantCoeff_val := by
    rw [constantCoeff_map' (cyclotomicCoefficientMap k p), a.constantCoeff_val, map_one]
@[simp]
theorem val_mapFormalPrincipalUnitToCyclotomic (a : FormalPrincipalUnit (CoefficientRing k p)) :
    (mapFormalPrincipalUnitToCyclotomic k p a).val
      = PowerSeries.map (cyclotomicCoefficientMap k p) a.val := rfl
theorem norm_coeff_mapFormalPrincipalUnitToCyclotomic_le_one
    (a : FormalPrincipalUnit (CoefficientRing k p)) (n : ℕ) :
    ‖coeff n (mapFormalPrincipalUnitToCyclotomic k p a).val‖ ≤ 1 := by
  rw [val_mapFormalPrincipalUnitToCyclotomic, PowerSeries.coeff_map]
  exact norm_cyclotomicCoefficientMap_le_one k p _
theorem mapFormalPrincipalUnitToCyclotomic_one :
    mapFormalPrincipalUnitToCyclotomic k p 1 = 1 :=
  FormalPrincipalUnit.ext (by
    rw [val_mapFormalPrincipalUnitToCyclotomic, FormalPrincipalUnit.val_one,
      FormalPrincipalUnit.val_one, map_one])
theorem mapFormalPrincipalUnitToCyclotomic_mul (a b : FormalPrincipalUnit (CoefficientRing k p)) :
    mapFormalPrincipalUnitToCyclotomic k p (a * b)
      = mapFormalPrincipalUnitToCyclotomic k p a * mapFormalPrincipalUnitToCyclotomic k p b :=
  FormalPrincipalUnit.ext (by
    rw [val_mapFormalPrincipalUnitToCyclotomic, FormalPrincipalUnit.val_mul,
      FormalPrincipalUnit.val_mul, val_mapFormalPrincipalUnitToCyclotomic,
      val_mapFormalPrincipalUnitToCyclotomic, map_mul])
end FiniteFields.Dwork
end
end

section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
def boundedFormalPrincipalUnit (a : FormalPrincipalUnit (CoefficientRing k p)) :
    BoundedDworkPowerSeries k p :=
  ⟨(mapFormalPrincipalUnitToCyclotomic k p a).val,
    norm_coeff_mapFormalPrincipalUnitToCyclotomic_le_one k p a⟩
@[simp]
theorem coe_boundedFormalPrincipalUnit (a : FormalPrincipalUnit (CoefficientRing k p)) :
    (boundedFormalPrincipalUnit k p a : (DworkCyclotomicField k p)⟦X⟧)
      = (mapFormalPrincipalUnitToCyclotomic k p a).val := rfl
theorem boundedFormalPrincipalUnit_one : boundedFormalPrincipalUnit k p 1 = 1 := by
  refine Subtype.ext ?_
  rw [coe_boundedFormalPrincipalUnit, mapFormalPrincipalUnitToCyclotomic_one]
  rfl
theorem boundedFormalPrincipalUnit_mul (a b : FormalPrincipalUnit (CoefficientRing k p)) :
    boundedFormalPrincipalUnit k p (a * b)
      = boundedFormalPrincipalUnit k p a * boundedFormalPrincipalUnit k p b := by
  refine Subtype.ext ?_
  rw [coe_boundedFormalPrincipalUnit, mapFormalPrincipalUnitToCyclotomic_mul]
  rfl
def formalArtinHasseSpecialization (a : FormalPrincipalUnit (CoefficientRing k p)) :
    DworkCyclotomicField k p :=
  dworkPowerSeriesEval k p (mapFormalPrincipalUnitToCyclotomic k p a).val
    (dworkArtinHasseParameter k p)
theorem formalArtinHasseSpecialization_hasSum (a : FormalPrincipalUnit (CoefficientRing k p)) :
    HasSum (fun n : ℕ => coeff n (mapFormalPrincipalUnitToCyclotomic k p a).val *
        dworkArtinHasseParameter k p ^ n)
      (formalArtinHasseSpecialization k p a) :=
  hasSum_dworkPowerSeriesEval k p _ _
    (norm_coeff_mapFormalPrincipalUnitToCyclotomic_le_one k p a)
    (dworkArtinHasseParameter_norm_lt_one k p)
theorem formalArtinHasseSpecialization_mul (a b : FormalPrincipalUnit (CoefficientRing k p)) :
    formalArtinHasseSpecialization k p (a * b)
      = formalArtinHasseSpecialization k p a * formalArtinHasseSpecialization k p b := by
  have h := map_mul (dworkPowerSeriesEvalRingHom k p (dworkArtinHasseParameter k p)
    (dworkArtinHasseParameter_norm_lt_one k p))
    (boundedFormalPrincipalUnit k p a) (boundedFormalPrincipalUnit k p b)
  rw [← boundedFormalPrincipalUnit_mul] at h
  exact h
theorem formalArtinHasseSpecialization_one :
    formalArtinHasseSpecialization k p 1 = 1 := by
  have h := map_one (dworkPowerSeriesEvalRingHom k p (dworkArtinHasseParameter k p)
    (dworkArtinHasseParameter_norm_lt_one k p))
  rw [← boundedFormalPrincipalUnit_one] at h
  exact h
end FiniteFields.Dwork
end
end

section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
structure DworkPrincipalUnit where
  val : DworkCyclotomicField k p
  norm_sub_one_lt : ‖val - 1‖ < 1
namespace DworkPrincipalUnit
variable {k p}
@[ext]
theorem ext {a b : DworkPrincipalUnit k p} (h : a.val = b.val) : a = b := by
  cases a
  cases b
  subst h
  rfl
theorem norm_val (a : DworkPrincipalUnit k p) : ‖a.val‖ = 1 := by
  have h1 : ‖a.val‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (a.val - 1) (1 : DworkCyclotomicField k p)
    rw [sub_add_cancel] at h
    exact h.trans (max_le a.norm_sub_one_lt.le (by rw [norm_one]))
  have h2 : (1 : ℝ) ≤ ‖a.val‖ := by
    by_contra hlt
    rw [not_le] at hlt
    have h := IsUltrametricDist.norm_add_le_max a.val (-(a.val - 1))
    rw [show a.val + -(a.val - 1) = 1 by ring, norm_neg, norm_one] at h
    exact absurd h (not_le.mpr (max_lt hlt a.norm_sub_one_lt))
  linarith
theorem val_ne_zero (a : DworkPrincipalUnit k p) : a.val ≠ 0 := by
  intro h
  have := a.norm_val
  rw [h, norm_zero] at this
  exact zero_ne_one this
instance instOne : One (DworkPrincipalUnit k p) where
  one := ⟨1, by rw [sub_self, norm_zero]; exact zero_lt_one⟩
@[simp] theorem val_one : (1 : DworkPrincipalUnit k p).val = 1 := rfl
instance instMul : Mul (DworkPrincipalUnit k p) where
  mul a b :=
    ⟨a.val * b.val, by
      have hb : ‖b.val‖ = 1 := b.norm_val
      have hsplit : a.val * b.val - 1 = (a.val - 1) * b.val + (b.val - 1) := by ring
      rw [hsplit]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ b.norm_sub_one_lt)
      rw [norm_mul, hb, mul_one]
      exact a.norm_sub_one_lt⟩
@[simp] theorem val_mul (a b : DworkPrincipalUnit k p) : (a * b).val = a.val * b.val := rfl
instance instInv : Inv (DworkPrincipalUnit k p) where
  inv a :=
    ⟨a.val⁻¹, by
      have hne := a.val_ne_zero
      have hsplit : a.val⁻¹ - 1 = -(a.val⁻¹ * (a.val - 1)) := by
        field_simp
        ring
      rw [hsplit, norm_neg, norm_mul, norm_inv, a.norm_val, inv_one, one_mul]
      exact a.norm_sub_one_lt⟩
@[simp] theorem val_inv (a : DworkPrincipalUnit k p) : a⁻¹.val = a.val⁻¹ := rfl
instance instCommGroup : CommGroup (DworkPrincipalUnit k p) where
  mul_assoc _ _ _ := ext (mul_assoc _ _ _)
  one_mul _ := ext (one_mul _)
  mul_one _ := ext (mul_one _)
  mul_comm _ _ := ext (mul_comm _ _)
  inv_mul_cancel a := ext (by rw [val_mul, val_inv, val_one, inv_mul_cancel₀ a.val_ne_zero])
end DworkPrincipalUnit
end FiniteFields.Dwork
end
end

section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
theorem formalArtinHasseSpecialization_norm_sub_one_lt
    (a : FormalPrincipalUnit (CoefficientRing k p)) :
    ‖formalArtinHasseSpecialization k p a - 1‖ < 1 := by
  have hsum := formalArtinHasseSpecialization_hasSum k p a
  have hsplit := (hsum.summable).tsum_eq_zero_add
  have hzero : coeff 0 (mapFormalPrincipalUnitToCyclotomic k p a).val *
      dworkArtinHasseParameter k p ^ 0 = 1 := by
    rw [pow_zero, mul_one, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      (mapFormalPrincipalUnitToCyclotomic k p a).constantCoeff_val]
  have hval : formalArtinHasseSpecialization k p a
      = 1 + ∑' n : ℕ, coeff (n + 1) (mapFormalPrincipalUnitToCyclotomic k p a).val *
          dworkArtinHasseParameter k p ^ (n + 1) := by
    rw [hsum.tsum_eq] at hsplit
    rw [hsplit, hzero]
  rw [hval, add_sub_cancel_left]
  refine lt_of_le_of_lt (norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _) ?_)
    (dworkArtinHasseParameter_norm_lt_one k p)
  intro n
  rw [norm_mul, norm_pow]
  calc ‖coeff (n + 1) (mapFormalPrincipalUnitToCyclotomic k p a).val‖ *
        ‖dworkArtinHasseParameter k p‖ ^ (n + 1)
      ≤ 1 * ‖dworkArtinHasseParameter k p‖ ^ (n + 1) :=
        mul_le_mul_of_nonneg_right
          (norm_coeff_mapFormalPrincipalUnitToCyclotomic_le_one k p a (n + 1)) (by positivity)
    _ = ‖dworkArtinHasseParameter k p‖ ^ (n + 1) := one_mul _
    _ ≤ ‖dworkArtinHasseParameter k p‖ ^ 1 :=
        pow_le_pow_of_le_one (norm_nonneg _) (dworkArtinHasseParameter_norm_lt_one k p).le
          (by omega)
    _ = ‖dworkArtinHasseParameter k p‖ := pow_one _
def specializationPrincipalUnit (a : FormalPrincipalUnit (CoefficientRing k p)) :
    DworkPrincipalUnit k p :=
  ⟨formalArtinHasseSpecialization k p a, formalArtinHasseSpecialization_norm_sub_one_lt k p a⟩
@[simp]
theorem val_specializationPrincipalUnit (a : FormalPrincipalUnit (CoefficientRing k p)) :
    (specializationPrincipalUnit k p a).val = formalArtinHasseSpecialization k p a := rfl
end FiniteFields.Dwork
end
end

section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
def artinHasseWittHom :
    WittVector p (CoefficientRing k p) →+ Additive (DworkPrincipalUnit k p) where
  toFun w := Additive.ofMul (specializationPrincipalUnit k p (dworkFormalArtinHasseProduct k p w))
  map_zero' := by
    have h : specializationPrincipalUnit k p (dworkFormalArtinHasseProduct k p 0) = 1 := by
      refine DworkPrincipalUnit.ext ?_
      rw [val_specializationPrincipalUnit, DworkPrincipalUnit.val_one,
        dworkFormalArtinHasseProduct_zero, formalArtinHasseSpecialization_one]
    exact congrArg Additive.ofMul h
  map_add' w w' := by
    have h : specializationPrincipalUnit k p (dworkFormalArtinHasseProduct k p (w + w'))
        = specializationPrincipalUnit k p (dworkFormalArtinHasseProduct k p w) *
          specializationPrincipalUnit k p (dworkFormalArtinHasseProduct k p w') := by
      refine DworkPrincipalUnit.ext ?_
      rw [val_specializationPrincipalUnit, DworkPrincipalUnit.val_mul,
        val_specializationPrincipalUnit, val_specializationPrincipalUnit,
        dworkFormalArtinHasseProduct_add, formalArtinHasseSpecialization_mul]
    exact congrArg Additive.ofMul h
@[simp]
theorem toMul_artinHasseWittHom (w : WittVector p (CoefficientRing k p)) :
    Additive.toMul (artinHasseWittHom k p w)
      = specializationPrincipalUnit k p (dworkFormalArtinHasseProduct k p w) := rfl
end FiniteFields.Dwork
end
end

section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
def cyclotomicFrobeniusQuotient : (DworkCyclotomicField k p)⟦X⟧ :=
  PowerSeries.map (cyclotomicCoefficientMap k p)
    (frobeniusQuotientOver (coefficientRingAlgebraMap k p) p
      (frobeniusQuotientSeries_mem_range_coefficientRingAlgebraMap k p))
end FiniteFields.Dwork
end
end

section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
local instance dw4e2ResiduePrimeAlgebra : Algebra (ZMod p) k := ZMod.algebra k p
namespace DworkPrincipalUnit
end DworkPrincipalUnit
def artinHasseWittUnit (u : WittVector p (CoefficientRing k p)) : DworkPrincipalUnit k p :=
  Additive.toMul (artinHasseWittHom k p u)
@[simp]
theorem artinHasseWittUnit_apply (u : WittVector p (CoefficientRing k p)) :
    artinHasseWittUnit k p u = Additive.toMul (artinHasseWittHom k p u) := rfl
def wittTraceTeichmuller (w : CoefficientRing k p) : WittVector p (CoefficientRing k p) :=
  ∑ i ∈ Finset.range (Module.finrank (ZMod p) k),
    WittVector.teichmuller p ((frobeniusLift k p)^[i] w)
end FiniteFields.Dwork
end
end

section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
def artinHasseEvalAt (u : WittVector p (CoefficientRing k p))
    (z : DworkCyclotomicField k p) : DworkCyclotomicField k p :=
  dworkPowerSeriesEval k p
    (mapFormalPrincipalUnitToCyclotomic k p (dworkFormalArtinHasseProduct k p u)).val z
end FiniteFields.Dwork
end
end

section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
local instance dw4e2TraceLimitResiduePrimeAlgebra : Algebra (ZMod p) k := ZMod.algebra k p
end FiniteFields.Dwork
end
end


