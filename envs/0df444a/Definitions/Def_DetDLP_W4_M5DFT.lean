-- Prove2me | Definitions.Def_DetDLP_W4_M5DFT
-- name    : DetDLP_W4_M5DFT
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T20:32:06.193836+00:00
-- url     : https://prove2.me/theorems/4c24c978-e80e-4fec-a646-93f1f34988c3
-- title:
--   Dyadic Fourier inversion over the Fermat ring
-- statement:
--   Proves dyadic orthogonality over commutative rings and recovers ordinary convolution coefficients by a padded forward transform, pointwise multiplication and an inverse transform.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Lemma 2.3 (pp. 8–9)

import Theorems.Thm_DetDLP_schonhage_strassen_fermat_dft_and_carry
import Definitions.Def_DetDLP_W4_M5Convolution

set_option autoImplicit false

namespace DetDLP
namespace w4_FermatDFT

open Finset

/-! The geometric-sum proof below works in a commutative ring, not merely a field.
A root with half-period `-1` is principal at a power-of-two length: odd frequencies
cancel between two halves, and even frequencies reduce to a transform of half the
length. Only the subsequent inverse transform needs an invertible length. -/

private theorem sum_two_halves {R : Type*} [CommRing R] (w : R) (n j : ℕ) :
    (∑ i ∈ range (2 * n), w ^ (j * i)) =
      (1 + (w ^ n) ^ j) * ∑ i ∈ range n, w ^ (j * i) := by
  rw [show 2 * n = n + n by omega, sum_range_add]
  have hs : (∑ i ∈ range n, w ^ (j * (n + i))) =
      (w ^ n) ^ j * ∑ i ∈ range n, w ^ (j * i) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [Nat.mul_add, pow_add, ← pow_mul]
    rw [Nat.mul_comm j n]
  rw [hs]
  ring

/-- A power-of-two root with half-period `-1` has vanishing geometric sums at
all nonzero frequencies below its length. No cancellation or domain hypothesis
is used; in particular the statement applies to composite Fermat moduli. -/
theorem dyadic_sum_zero {R : Type*} [CommRing R] (m : ℕ) (w : R)
    (hhalf : w ^ (2 ^ m) = -1) {j : ℕ} (hj0 : 0 < j) (hj : j < 2 ^ (m + 1)) :
    ∑ i ∈ range (2 ^ (m + 1)), w ^ (j * i) = 0 := by
  induction m generalizing w j with
  | zero =>
      have hj1 : j = 1 := by norm_num at hj; omega
      have hw : w = -1 := by simpa using hhalf
      simp [hj1, hw, sum_range_succ]
  | succ m ih =>
      rw [pow_succ', sum_two_halves, hhalf]
      rcases Nat.even_or_odd j with heven | hodd
      · obtain ⟨q, hq⟩ := heven
        have hq0 : 0 < q := by omega
        have hqL : q < 2 ^ (m + 1) := by
          rw [pow_succ'] at hj
          omega
        have hhalf2 : (w ^ 2) ^ (2 ^ m) = -1 := by
          rw [← pow_mul, ← pow_succ']
          exact hhalf
        have hs := ih (w ^ 2) hhalf2 hq0 hqL
        have heq : (∑ i ∈ range (2 ^ (m + 1)), w ^ (j * i)) =
            ∑ i ∈ range (2 ^ (m + 1)), (w ^ 2) ^ (q * i) := by
          apply sum_congr rfl
          intro i _
          rw [← pow_mul, hq]
          congr 1
          ring
        rw [heq, hs, mul_zero]
      · rw [hodd.neg_one_pow]
        simp

/-- The full period follows from the half-period equation. -/
theorem dyadic_full_period {R : Type*} [CommRing R] {m : ℕ} {w : R}
    (hhalf : w ^ (2 ^ m) = -1) : w ^ (2 ^ (m + 1)) = 1 := by
  rw [pow_succ, pow_mul, hhalf]
  norm_num

private theorem pow_mod_period {R : Type*} [CommRing R] {L : ℕ} {w : R}
    (hperiod : w ^ L = 1) (a : ℕ) : w ^ a = w ^ (a % L) := by
  calc
    w ^ a = w ^ (a % L + L * (a / L)) := by rw [Nat.mod_add_div]
    _ = w ^ (a % L) := by rw [pow_add, pow_mul, hperiod, one_pow, mul_one]

/-- Exact discrete orthogonality, including frequencies outside the first period. -/
theorem dyadic_orthogonality {R : Type*} [CommRing R] {m : ℕ} {w : R}
    (hhalf : w ^ (2 ^ m) = -1) (j : ℕ) :
    (∑ i ∈ range (2 ^ (m + 1)), w ^ (j * i)) =
      if j % (2 ^ (m + 1)) = 0 then ((2 ^ (m + 1) : ℕ) : R) else 0 := by
  have hperiod := dyadic_full_period hhalf
  have hreindex : (∑ i ∈ range (2 ^ (m + 1)), w ^ (j * i)) =
      ∑ i ∈ range (2 ^ (m + 1)), w ^ ((j % (2 ^ (m + 1))) * i) := by
    apply sum_congr rfl
    intro i _
    rw [pow_mod_period hperiod (j * i), pow_mod_period hperiod ((j % (2 ^ (m + 1))) * i)]
    simp [Nat.mul_mod]
  rw [hreindex]
  split_ifs with hj
  · simp [hj]
  · simpa only [Nat.cast_zero] using
      dyadic_sum_zero m w hhalf (Nat.pos_of_ne_zero hj) (Nat.mod_lt _ (by positivity))

/-- The forward transform with an explicitly supplied root. -/
def forward {R : Type*} [CommRing R] (L : ℕ) (w : R) (x : ℕ → R) (t : ℕ) : R :=
  ∑ j ∈ range L, x j * w ^ (j * t)

/-- The inverse uses only nonnegative exponents. At an output index `u < L`,
`w^((L-u)t)` is exactly the inverse character. -/
def inverse {R : Type*} [CommRing R] (L : ℕ) (w invL : R)
    (x : ℕ → R) (u : ℕ) : R :=
  invL * ∑ t ∈ range L, x t * w ^ ((L - u) * t)

private theorem kernel_mod_iff {L a u : ℕ} (hu : u < L) :
    (a + (L - u)) % L = 0 ↔ a % L = u := by
  have hsum : (a + (L - u)) + u = a + L := by omega
  constructor
  · intro h
    have heq : (a + (L - u)) + u ≡ 0 + u [MOD L] :=
      (show a + (L - u) ≡ 0 [MOD L] by simpa only [Nat.ModEq, Nat.zero_mod] using h).add_right u
    rw [hsum] at heq
    simpa only [Nat.ModEq, Nat.add_mod_right, zero_add, Nat.mod_eq_of_lt hu] using heq
  · intro h
    have heq : (a + (L - u)) + u ≡ 0 + u [MOD L] := by
      rw [hsum]
      simpa only [Nat.ModEq, Nat.add_mod_right, zero_add, Nat.mod_eq_of_lt hu] using h
    have := heq.add_right_cancel' u
    simpa only [Nat.ModEq, Nat.zero_mod] using this

/-- Orthogonality in the form used by the inverse transform. -/
theorem inverse_kernel {R : Type*} [CommRing R] {m : ℕ} {w : R}
    (hhalf : w ^ (2 ^ m) = -1) (a u : ℕ) (hu : u < 2 ^ (m + 1)) :
    (∑ t ∈ range (2 ^ (m + 1)), w ^ (a * t) * w ^ ((2 ^ (m + 1) - u) * t)) =
      if a % (2 ^ (m + 1)) = u then ((2 ^ (m + 1) : ℕ) : R) else 0 := by
  simp_rw [← pow_add, ← Nat.add_mul]
  rw [dyadic_orthogonality hhalf]
  simp only [kernel_mod_iff hu]

/-- The normalized inverse recovers every input coordinate. The sole unit
assumption is the explicit inverse of the transform length. -/
theorem inverse_forward {R : Type*} [CommRing R] {m : ℕ} {w invL : R}
    (hhalf : w ^ (2 ^ m) = -1) (hinv : invL * (2 ^ (m + 1) : ℕ) = 1)
    (x : ℕ → R) {u : ℕ} (hu : u < 2 ^ (m + 1)) :
    inverse (2 ^ (m + 1)) w invL (forward (2 ^ (m + 1)) w x) u = x u := by
  classical
  unfold inverse forward
  simp_rw [sum_mul]
  rw [sum_comm]
  have hs : (∑ j ∈ range (2 ^ (m + 1)), ∑ t ∈ range (2 ^ (m + 1)),
      (x j * w ^ (j * t)) * w ^ ((2 ^ (m + 1) - u) * t)) =
      ∑ j ∈ range (2 ^ (m + 1)), x j *
        (if j = u then ((2 ^ (m + 1) : ℕ) : R) else 0) := by
    apply sum_congr rfl
    intro j hj
    simp_rw [mul_assoc]
    rw [← mul_sum, inverse_kernel hhalf j u hu,
      Nat.mod_eq_of_lt (mem_range.mp hj)]
  rw [hs]
  simp only [mul_ite, mul_zero, sum_ite_eq', mem_range, hu, if_true]
  calc
    invL * (x u * (2 ^ (m + 1) : ℕ)) =
        x u * (invL * (2 ^ (m + 1) : ℕ)) := by ring
    _ = x u := by rw [hinv, mul_one]

/-- Circular convolution. Reduction of the sum of the two indices is explicit;
ordinary convolution is recovered below only after the zero-padding hypothesis. -/
def circularCoefficient {R : Type*} [CommRing R] (L : ℕ) (x y : ℕ → R) (u : ℕ) : R :=
  ∑ i ∈ range L, ∑ j ∈ range L, if (i + j) % L = u then x i * y j else 0

private theorem forward_mul {R : Type*} [CommRing R]
    (L : ℕ) (w : R) (x y : ℕ → R) (t : ℕ) :
    forward L w x t * forward L w y t =
      ∑ i ∈ range L, ∑ j ∈ range L, (x i * y j) * w ^ ((i + j) * t) := by
  unfold forward
  rw [sum_mul]
  apply sum_congr rfl
  intro i _
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  rw [Nat.add_mul, pow_add]
  ring

/-- The direct DFT summand, indexed as `j = L2*j1+j2`, equals the
factored row/column summand at `t = t1+L1*t2`, provided the root has full period
`L1*L2`. This is the algebraic identity used to implement the DFT in two layers. -/
theorem two_layer_summand {R : Type*} [CommRing R] (L1 L2 : ℕ) (w : R)
    (hperiod : w ^ (L1 * L2) = 1) (x : ℕ → R)
    (j1 j2 t1 t2 : ℕ) :
    x (L2 * j1 + j2) * w ^ ((L2 * j1 + j2) * (t1 + L1 * t2)) =
      w ^ (L1 * j2 * t2) *
        (w ^ (j2 * t1) * (w ^ (L2 * j1 * t1) * x (L2 * j1 + j2))) := by
  have hexp : (L2 * j1 + j2) * (t1 + L1 * t2) =
      L1 * j2 * t2 + j2 * t1 + L2 * j1 * t1 + (L1 * L2) * (j1 * t2) := by ring
  rw [hexp, pow_add, pow_add, pow_add, pow_mul w (L1 * L2) (j1 * t2), hperiod,
    one_pow, mul_one]
  ring

/-- Summed two-layer DFT formula. No primality or domain property is used. -/
theorem two_layer_forward {R : Type*} [CommRing R] (L1 L2 : ℕ) (w : R)
    (hperiod : w ^ (L1 * L2) = 1) (x : ℕ → R) (t1 t2 : ℕ) :
    (∑ j1 ∈ range L1, ∑ j2 ∈ range L2,
      x (L2 * j1 + j2) * w ^ ((L2 * j1 + j2) * (t1 + L1 * t2))) =
    ∑ j2 ∈ range L2, w ^ (L1 * j2 * t2) *
      (w ^ (j2 * t1) *
        ∑ j1 ∈ range L1, w ^ (L2 * j1 * t1) * x (L2 * j1 + j2)) := by
  rw [sum_comm]
  apply sum_congr rfl
  intro j2 hj2
  rw [Finset.mul_sum, Finset.mul_sum]
  apply sum_congr rfl
  intro j1 hj1
  exact two_layer_summand L1 L2 w hperiod x j1 j2 t1 t2

/-- The full Fourier convolution theorem over a possibly non-domain ring. -/
theorem inverse_pointwise_forward {R : Type*} [CommRing R] {m : ℕ} {w invL : R}
    (hhalf : w ^ (2 ^ m) = -1) (hinv : invL * (2 ^ (m + 1) : ℕ) = 1)
    (x y : ℕ → R) {u : ℕ} (hu : u < 2 ^ (m + 1)) :
    inverse (2 ^ (m + 1)) w invL
      (fun t => forward (2 ^ (m + 1)) w x t * forward (2 ^ (m + 1)) w y t) u =
        circularCoefficient (2 ^ (m + 1)) x y u := by
  classical
  unfold inverse circularCoefficient
  simp_rw [forward_mul, sum_mul]
  rw [sum_comm]
  have hs : (∑ i ∈ range (2 ^ (m + 1)), ∑ t ∈ range (2 ^ (m + 1)),
      ∑ j ∈ range (2 ^ (m + 1)),
        ((x i * y j) * w ^ ((i + j) * t)) * w ^ ((2 ^ (m + 1) - u) * t)) =
      ∑ i ∈ range (2 ^ (m + 1)), ∑ j ∈ range (2 ^ (m + 1)),
        (x i * y j) *
          (if (i + j) % (2 ^ (m + 1)) = u then ((2 ^ (m + 1) : ℕ) : R) else 0) := by
    apply sum_congr rfl
    intro i _
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    simp_rw [mul_assoc]
    rw [← mul_sum, ← mul_sum, inverse_kernel hhalf (i + j) u hu]
  rw [hs, mul_sum]
  apply sum_congr rfl
  intro i _
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  split_ifs
  · calc
      invL * (x i * y j * (2 ^ (m + 1) : ℕ)) =
          (x i * y j) * (invL * (2 ^ (m + 1) : ℕ)) := by ring
      _ = x i * y j := by rw [hinv, mul_one]
  · simp

/-- Ordinary, non-cyclic convolution of two length-`n` inputs. -/
def coefficient {R : Type*} [CommRing R] (n : ℕ) (x y : ℕ → R) (u : ℕ) : R :=
  ∑ i ∈ range n, ∑ j ∈ range n, if i + j = u then x i * y j else 0

/-- Padding to at least twice the input length prevents every cyclic wraparound. -/
theorem circular_eq_coefficient {R : Type*} [CommRing R] {n L : ℕ}
    (hpad : 2 * n ≤ L) (x y : ℕ → R)
    (hx : ∀ i, n ≤ i → x i = 0) (hy : ∀ i, n ≤ i → y i = 0) (u : ℕ) :
    circularCoefficient L x y u = coefficient n x y u := by
  classical
  unfold circularCoefficient coefficient
  have hnL : n ≤ L := by omega
  rw [← sum_subset (range_mono hnL)]
  · apply sum_congr rfl
    intro i hi
    rw [← sum_subset (range_mono hnL)]
    · apply sum_congr rfl
      intro j hj
      have hij : i + j < L := by
        have := mem_range.mp hi
        have := mem_range.mp hj
        omega
      rw [Nat.mod_eq_of_lt hij]
    · intro j _ hj
      have hjn : n ≤ j := by simpa only [mem_range, not_lt] using hj
      rw [hy j hjn]
      simp
  · intro i _ hi
    have hin : n ≤ i := by simpa only [mem_range, not_lt] using hi
    rw [hx i hin]
    simp

/-- Forward transforms, pointwise multiplication, and the normalized inverse
compute ordinary coefficients for zero-padded inputs, without any field assumption. -/
theorem inverse_pointwise_eq_coefficient {R : Type*} [CommRing R]
    {m n : ℕ} {w invL : R}
    (hhalf : w ^ (2 ^ m) = -1) (hinv : invL * (2 ^ (m + 1) : ℕ) = 1)
    (hpad : 2 * n ≤ 2 ^ (m + 1)) (x y : ℕ → R)
    (hx : ∀ i, n ≤ i → x i = 0) (hy : ∀ i, n ≤ i → y i = 0)
    {u : ℕ} (hu : u < 2 ^ (m + 1)) :
    inverse (2 ^ (m + 1)) w invL
      (fun t => forward (2 ^ (m + 1)) w x t * forward (2 ^ (m + 1)) w y t) u =
        coefficient n x y u := by
  rw [inverse_pointwise_forward hhalf hinv x y hu]
  exact circular_eq_coefficient hpad x y hx hy u

/-! ## Specialization to the Fermat ring

The accepted source supplies the half-period equation. The principal-root and
inversion results above are new consequences proved here. The length here is
`2^(m+1)`, not `2^m`; the normalizing factor therefore uses `J-(m+1)`. -/

abbrev Ring (J : ℕ) := ZMod (2 ^ J + 1)

def root (J step : ℕ) : Ring J := (2 : Ring J) ^ step

def lengthInverse (J m : ℕ) : Ring J := -(2 : Ring J) ^ (J - (m + 1))

/-- Accepted half-period fact, reused under an independent name. -/
theorem root_half {J m step : ℕ} (hmJ : m ≤ J) (hJ : J = 2 ^ m * step) :
    root J step ^ (2 ^ m) = -1 :=
  (DetDLP.schonhage_strassen_fermat_dft_and_carry.2.1.1 J m step hmJ hJ).2.1

/-- Explicit inverse for the full transform length. This checks the extra factor
of two absent from the accepted source's inverse for the half-length. -/
theorem lengthInverse_mul_length {J m step : ℕ} (hmJ : m + 1 ≤ J)
    (hJ : J = 2 ^ m * step) :
    lengthInverse J m * (2 ^ (m + 1) : ℕ) = 1 := by
  have htwo : (2 : Ring J) ^ J = -1 :=
    (DetDLP.schonhage_strassen_fermat_dft_and_carry.2.1.1 J m step (by omega) hJ).1
  unfold lengthInverse
  push_cast
  rw [neg_mul, ← pow_add, Nat.sub_add_cancel hmJ, htwo, neg_neg]

/-- Principal-root orthogonality in the actual Fermat ring. -/
theorem fermat_orthogonality {J m step : ℕ} (hmJ : m ≤ J)
    (hJ : J = 2 ^ m * step) (j : ℕ) :
    (∑ i ∈ range (2 ^ (m + 1)), root J step ^ (j * i)) =
      if j % (2 ^ (m + 1)) = 0 then ((2 ^ (m + 1) : ℕ) : Ring J) else 0 :=
  dyadic_orthogonality (root_half hmJ hJ) j

/-- True, normalized Fermat-ring inverse transform. -/
theorem fermat_inverse_forward {J m step : ℕ} (hmJ : m + 1 ≤ J)
    (hJ : J = 2 ^ m * step) (x : ℕ → Ring J)
    {u : ℕ} (hu : u < 2 ^ (m + 1)) :
    inverse (2 ^ (m + 1)) (root J step) (lengthInverse J m)
      (forward (2 ^ (m + 1)) (root J step) x) u = x u :=
  inverse_forward (root_half (by omega) hJ) (lengthInverse_mul_length hmJ hJ) x hu

/-- The complete multiplication pipeline, before decoding residues as words. -/
def productPipeline (J m step : ℕ) (x y : ℕ → Ring J) : ℕ → Ring J :=
  inverse (2 ^ (m + 1)) (root J step) (lengthInverse J m)
    (fun t => forward (2 ^ (m + 1)) (root J step) x t *
      forward (2 ^ (m + 1)) (root J step) y t)

/-- The Fermat forward/pointwise/inverse pipeline computes ordinary convolution
for any inputs supported on fewer than half the transform coordinates. -/
theorem fermat_productPipeline_eq_coefficient {J m step n : ℕ} (hmJ : m + 1 ≤ J)
    (hJ : J = 2 ^ m * step) (hpad : 2 * n ≤ 2 ^ (m + 1))
    (x y : ℕ → Ring J) (hx : ∀ i, n ≤ i → x i = 0) (hy : ∀ i, n ≤ i → y i = 0)
    {u : ℕ} (hu : u < 2 ^ (m + 1)) :
    productPipeline J m step x y u = coefficient n x y u :=
  inverse_pointwise_eq_coefficient (root_half (by omega) hJ)
    (lengthInverse_mul_length hmJ hJ) hpad x y hx hy hu

/-- Embed a finite list of unsigned input values, with hardcoded zero padding. -/
def padded (J n : ℕ) (x : ℕ → ℕ) (i : ℕ) : Ring J :=
  if i < n then (x i : Ring J) else 0

/-- Unsigned ordinary convolution, used to compare ring outputs with true integers. -/
def natCoefficient (n : ℕ) (x y : ℕ → ℕ) (u : ℕ) : ℕ :=
  ∑ i ∈ range n, ∑ j ∈ range n, if i + j = u then x i * y j else 0

/-- The ring coefficient is the cast of the integer coefficient. -/
theorem coefficient_padded (J n : ℕ) (x y : ℕ → ℕ) (u : ℕ) :
    coefficient n (padded J n x) (padded J n y) u =
      (natCoefficient n x y u : Ring J) := by
  classical
  unfold coefficient natCoefficient
  push_cast
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  simp only [padded, mem_range.mp hi, mem_range.mp hj, if_true]

/-- Casting removes the modular reductions, but the equality is a consequence
of the proved inverse transform, not merely a rearrangement of forward sums. -/
theorem fermat_productPipeline_eq_natCoefficient {J m step n : ℕ}
    (hmJ : m + 1 ≤ J) (hJ : J = 2 ^ m * step) (hpad : 2 * n ≤ 2 ^ (m + 1))
    (x y : ℕ → ℕ) {u : ℕ} (hu : u < 2 ^ (m + 1)) :
    productPipeline J m step (padded J n x) (padded J n y) u =
      (natCoefficient n x y u : Ring J) := by
  rw [fermat_productPipeline_eq_coefficient hmJ hJ hpad
    (padded J n x) (padded J n y)
    (fun i hi => by simp [padded, Nat.not_lt.mpr hi])
    (fun i hi => by simp [padded, Nat.not_lt.mpr hi]) hu]
  exact coefficient_padded J n x y u

/-- Canonical natural output of the actual inverse pipeline. -/
def productResidue (J m step n : ℕ) (x y : ℕ → ℕ) (u : ℕ) : ℕ :=
  (productPipeline J m step (padded J n x) (padded J n y) u).val

/-- An integer coefficient below the Fermat modulus is recovered exactly,
not merely modulo that modulus. -/
theorem productResidue_eq_natCoefficient {J m step n : ℕ}
    (hmJ : m + 1 ≤ J) (hJ : J = 2 ^ m * step) (hpad : 2 * n ≤ 2 ^ (m + 1))
    (x y : ℕ → ℕ) {u : ℕ} (hu : u < 2 ^ (m + 1))
    (hc : natCoefficient n x y u < 2 ^ J + 1) :
    productResidue J m step n x y u = natCoefficient n x y u := by
  unfold productResidue
  rw [fermat_productPipeline_eq_natCoefficient hmJ hJ hpad x y hu,
    ZMod.val_natCast, Nat.mod_eq_of_lt hc]

/-! ## Canonical binary words for every stage

The encoding is explicitly little-endian and fixed-width. Uniqueness uses the
already proved residue-array theorem, so it applies jointly to whole stage
bundles (forward transforms, pointwise products, inverse transforms) rather
than just to each wire considered in isolation. -/

/-- Every Fermat canonical residue fits in `J+1` bits. -/
theorem fermat_modulus_le_wordspace (J : ℕ) :
    2 ^ J + 1 ≤ 2 ^ (J + 1) := by
  rw [pow_succ]
  have hp : 1 ≤ 2 ^ J := Nat.one_le_two_pow
  omega

/-- The fixed-width encoding selected for a Fermat residue. -/
def canonicalWord (J : ℕ) (r : Ring J) : Fin (J + 1) → Bool :=
  w4_ConvolutionArithmetic.canonicalBits (J + 1) r.val

/-- Each intermediate residue has exactly one bounded binary witness satisfying
its canonical-residue equation. -/
theorem canonicalWord_unique (J : ℕ) (r : Ring J) :
    ∃! v : Fin (J + 1) → Bool,
      bitsToNat v < 2 ^ J + 1 ∧ bitsToNat v % (2 ^ J + 1) = r.val := by
  have := w4_ConvolutionArithmetic.canonical_residue_bits_unique
    (d := J + 1) (Q := 2 ^ J + 1) (r := r.val)
    (fermat_modulus_le_wordspace J) (ZMod.val_lt r)
  simpa only using this

/-- Canonical bit assignments for any finite or infinite indexed stage bundle
are jointly unique. -/
theorem canonicalBundle_unique {I : Type*} (J : ℕ) (r : I → Ring J) :
    ∃! words : I → Fin (J + 1) → Bool,
      ∀ i, bitsToNat (words i) < 2 ^ J + 1 ∧
        bitsToNat (words i) % (2 ^ J + 1) = (r i).val := by
  exact w4_ConvolutionArithmetic.canonical_residue_array_unique
    (I := I) (d := J + 1) (Q := 2 ^ J + 1)
    (fermat_modulus_le_wordspace J) (fun i => (r i).val)
    (fun i => ZMod.val_lt (r i))

/-- The unique bundle witness is concretely the pointwise canonical word. -/
theorem canonicalBundle_is_canonical {I : Type*} (J : ℕ) (r : I → Ring J) :
    (fun i => canonicalWord J (r i)) =
      Classical.choose (canonicalBundle_unique J r) := by
  have hcan : ∀ i, bitsToNat (canonicalWord J (r i)) < 2 ^ J + 1 ∧
      bitsToNat (canonicalWord J (r i)) % (2 ^ J + 1) = (r i).val := by
    intro i
    rw [canonicalWord, w4_ConvolutionArithmetic.bitsToNat_canonicalBits
      ((ZMod.val_lt (r i)).trans_le (fermat_modulus_le_wordspace J))]
    exact ⟨ZMod.val_lt (r i), Nat.mod_eq_of_lt (ZMod.val_lt (r i))⟩
  have hchoose := Classical.choose_spec (canonicalBundle_unique J r)
  exact (canonicalBundle_unique J r).unique hcan hchoose.1

/-- All output words of the actual inverse pipeline are simultaneously unique. -/
theorem productPipeline_words_unique {J m step n : ℕ} (x y : ℕ → ℕ)
    (u : ℕ → ℕ) :
    ∃! words : ℕ → Fin (J + 1) → Bool,
      ∀ i, bitsToNat (words i) < 2 ^ J + 1 ∧
        bitsToNat (words i) % (2 ^ J + 1) =
          (productPipeline J m step (padded J n x) (padded J n y) (u i)).val := by
  exact canonicalBundle_unique J
    (fun i => productPipeline J m step (padded J n x) (padded J n y) (u i))

/-- For each inverse coefficient, canonical word decoding recovers the true
integer coefficient whenever it lies below the modulus. -/
theorem canonical_product_word_decodes {J m step n : ℕ}
    (hmJ : m + 1 ≤ J) (hJ : J = 2 ^ m * step) (hpad : 2 * n ≤ 2 ^ (m + 1))
    (x y : ℕ → ℕ) {u : ℕ} (hu : u < 2 ^ (m + 1))
    (hc : natCoefficient n x y u < 2 ^ J + 1) :
    bitsToNat (canonicalWord J
      (productPipeline J m step (padded J n x) (padded J n y) u)) =
        natCoefficient n x y u := by
  change bitsToNat (w4_ConvolutionArithmetic.canonicalBits (J + 1)
    (productPipeline J m step (padded J n x) (padded J n y) u).val) = _
  rw [w4_ConvolutionArithmetic.bitsToNat_canonicalBits
    ((ZMod.val_lt _).trans_le (fermat_modulus_le_wordspace J))]
  exact productResidue_eq_natCoefficient hmJ hJ hpad x y hu hc


end w4_FermatDFT
end DetDLP


