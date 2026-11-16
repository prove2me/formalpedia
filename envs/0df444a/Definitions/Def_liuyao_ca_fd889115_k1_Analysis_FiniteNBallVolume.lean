-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteNBallVolume
-- name    : liuyao_ca_fd889115_k1_Analysis_FiniteNBallVolume
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:42:10.442595+00:00
-- url     : https://prove2.me/theorems/4906ee35-9bee-40ea-8e6c-6b3612d45305
-- title:
--   Analysis · FiniteNBallVolume
-- statement:
--   Private portability check of the frozen foundation, with concrete rational decision proofs checked by the Lean kernel.

import Init.Grind.Ordered.Rat

set_option autoImplicit true

/-!
# A computable volume model for the n-ball

The project treats the volume of an `n`-ball through a finite recurrence rather
than through Lebesgue measure.  The rational coefficient records everything
except the chosen computable approximation to `pi`:

`V₀(r) = 1`, `V₁(r) = 2r`, and
`Vₙ₊₂(r) = (2 * pi * r² / (n+2)) * Vₙ(r)`.

This file formalizes the coefficient and finite evaluation layer.  A later
bridge can replace the rational `pi` input by any valid `RealCompute` presentation.
-/

namespace ComputableAnalysis

def nBallCoeff : Nat -> Rat
  | 0 => 1
  | 1 => 2
  | n + 2 => (2 : Rat) / (n + 2) * nBallCoeff n

def nBallPiExponent (n : Nat) : Nat := n / 2

def nBallVolumeModel (n : Nat) (piApprox radius : Rat) : Rat :=
  nBallCoeff n * piApprox ^ nBallPiExponent n * radius ^ n

/-! A literal finite product-integral surrogate.  The lists are the sampled
coordinates and the functions are rational cell values; no completed domain
or measure is hidden in this definition. -/

def finiteProductSum2D (xs ys : List Rat) (f g : Rat -> Rat) : Rat :=
  (xs.map (fun x =>
    (ys.map (fun y => f x * g y)).foldl (fun acc value => acc + value) 0)).foldl
      (fun acc value => acc + value) 0

private theorem foldl_add_initial (xs : List Rat) (term : Rat -> Rat)
    (initial : Rat) :
    xs.foldl (fun acc value => acc + term value) initial =
      initial + xs.foldl (fun acc value => acc + term value) 0 := by
  induction xs generalizing initial with
  | nil =>
      simp
      grind
  | cons x xs ih =>
      simp only [List.foldl]
      simp only [Rat.zero_add]
      rw [ih]
      rw [ih (initial := term x)]
      grind [Rat.add_assoc]

private theorem foldl_add_map_mul_left (ys : List Rat) (a : Rat)
    (g : Rat -> Rat) :
    (ys.map (fun y => a * g y)).foldl (fun acc value => acc + value) 0 =
      a * (ys.map g).foldl (fun acc value => acc + value) 0 := by
  induction ys with
  | nil =>
      simp
  | cons y ys ih =>
      simp only [List.map_cons, List.foldl]
      simp only [Rat.zero_add]
      rw [foldl_add_initial]
      have hright :
          (ys.map g).foldl (fun acc value => acc + value) (g y) =
            g y + (ys.map g).foldl (fun acc value => acc + value) 0 := by
        simpa only [id] using
          (foldl_add_initial (ys.map g) (fun z => z) (g y))
      rw [hright]
      rw [ih]
      grind [Rat.mul_add, Rat.add_assoc, Rat.mul_assoc]

private theorem foldl_add_map_mul_right (xs : List Rat) (b : Rat)
    (f : Rat -> Rat) :
    (xs.map (fun x => f x * b)).foldl (fun acc value => acc + value) 0 =
      (xs.map f).foldl (fun acc value => acc + value) 0 * b := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.map_cons, List.foldl]
      simp only [Rat.zero_add]
      rw [foldl_add_initial]
      have hright :
          (xs.map f).foldl (fun acc value => acc + value) (f x) =
            f x + (xs.map f).foldl (fun acc value => acc + value) 0 := by
        simpa only [id] using
          (foldl_add_initial (xs.map f) (fun z => z) (f x))
      rw [hright]
      rw [ih]
      grind [Rat.add_mul, Rat.add_assoc, Rat.mul_assoc]

private theorem foldl_add_map_mul_right_general {α : Type}
    (xs : List α) (b : Rat) (f : α -> Rat) :
    (xs.map (fun x => f x * b)).foldl (fun acc value => acc + value) 0 =
      (xs.map f).foldl (fun acc value => acc + value) 0 * b := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.map_cons, List.foldl]
      simp only [Rat.zero_add]
      rw [foldl_add_initial]
      have hright :
          (xs.map f).foldl (fun acc value => acc + value) (f x) =
            f x + (xs.map f).foldl (fun acc value => acc + value) 0 := by
        simpa only [id] using
          (foldl_add_initial (xs.map f) (fun z => z) (f x))
      rw [hright, ih]
      grind [Rat.add_mul, Rat.add_assoc, Rat.mul_assoc]

theorem finiteProductSum2D_factorized (xs ys : List Rat) (f g : Rat -> Rat) :
    finiteProductSum2D xs ys f g =
      (xs.map f).foldl (fun acc value => acc + value) 0 *
      (ys.map g).foldl (fun acc value => acc + value) 0 := by
  induction xs with
  | nil =>
      simp [finiteProductSum2D]
  | cons x xs ih =>
      simp only [finiteProductSum2D, List.map_cons, List.foldl]
      simp only [Rat.zero_add]
      rw [foldl_add_map_mul_left ys (f x) g]
      rw [foldl_add_initial]
      have ih' := ih
      have ih'' :
          (xs.map (fun x =>
            (ys.map (fun y => f x * g y)).foldl
              (fun acc value => acc + value) 0)).foldl
              (fun acc value => acc + value) 0 =
            (xs.map f).foldl (fun acc value => acc + value) 0 *
              (ys.map g).foldl (fun acc value => acc + value) 0 := by
        simpa [finiteProductSum2D] using ih'
      rw [ih'']
      have hright :
          (xs.map f).foldl (fun acc value => acc + value) (f x) =
            f x + (xs.map f).foldl (fun acc value => acc + value) 0 := by
        simpa only [id] using
          (foldl_add_initial (xs.map f) (fun z => z) (f x))
      rw [hright]
      grind [Rat.add_mul, Rat.mul_add, Rat.add_assoc, Rat.mul_assoc]

/-! The same finite algebra in arbitrary dimension.  A list of sample lists
and a list of one-variable factors describes a separable rectangular sum. -/

def finiteProductNestedSum : List (List Rat) -> List (Rat -> Rat) -> Rat
  | [], [] => 1
  | samples :: restSamples, factor :: restFactors =>
      (samples.map (fun x =>
        factor x * finiteProductNestedSum restSamples restFactors)).foldl
        (fun acc value => acc + value) 0
  | _, _ => 0

def finiteProductSum : List (List Rat) -> List (Rat -> Rat) -> Rat
  | [], [] => 1
  | samples :: restSamples, factor :: restFactors =>
      (samples.map factor).foldl (fun acc value => acc + value) 0 *
        finiteProductSum restSamples restFactors
  | _, _ => 0

theorem finiteProductNestedSum_factorized
    (samples : List (List Rat)) (factors : List (Rat -> Rat)) :
    finiteProductNestedSum samples factors =
      finiteProductSum samples factors := by
  induction samples generalizing factors with
  | nil =>
      cases factors <;> rfl
  | cons sample rest ih =>
      cases factors with
      | nil => rfl
      | cons factor restFactors =>
          simp only [finiteProductNestedSum, finiteProductSum]
          induction sample with
          | nil => simp
          | cons x xs ihx =>
              simp only [List.map_cons, List.foldl]
              rw [foldl_add_initial]
              rw [ihx]
              have htail := ih restFactors
              rw [htail]
              have hright :
                  (xs.map factor).foldl (fun acc value => acc + value)
                      (factor x) =
                    factor x +
                      (xs.map factor).foldl
                        (fun acc value => acc + value) 0 := by
                simpa only [id] using
                  (foldl_add_initial (xs.map factor) (fun z => z)
                    (factor x))
              simp only [Rat.zero_add]
              rw [hright]
              grind [Rat.add_mul, Rat.mul_add, Rat.add_assoc, Rat.mul_assoc]

def finiteProductIntegralNestedSum :
    List (List (Rat × Rat)) -> List (Rat -> Rat) -> Rat
  | [], [] => 1
  | cells :: restCells, factor :: restFactors =>
      (cells.map (fun cell =>
        cell.2 * factor cell.1 *
          finiteProductIntegralNestedSum restCells restFactors)).foldl
        (fun acc value => acc + value) 0
  | _, _ => 0

def finiteProductIntegralSum :
    List (List (Rat × Rat)) -> List (Rat -> Rat) -> Rat
  | [], [] => 1
  | cells :: restCells, factor :: restFactors =>
      (cells.map (fun cell => cell.2 * factor cell.1)).foldl
          (fun acc value => acc + value) 0 *
        finiteProductIntegralSum restCells restFactors
  | _, _ => 0

theorem finiteProductIntegralNestedSum_factorized
    (samples : List (List (Rat × Rat))) (factors : List (Rat -> Rat)) :
    finiteProductIntegralNestedSum samples factors =
      finiteProductIntegralSum samples factors := by
  induction samples generalizing factors with
  | nil =>
      cases factors <;> rfl
  | cons cells rest ih =>
      cases factors with
      | nil => rfl
      | cons factor restFactors =>
          simp only [finiteProductIntegralNestedSum, finiteProductIntegralSum]
          rw [foldl_add_map_mul_right_general cells
            (finiteProductIntegralNestedSum rest restFactors)
            (fun cell => cell.2 * factor cell.1)]
          rw [ih]

/-! The weighted form is the rectangle-integral interface: each sample carries
its rational cell width.  It is definitionally a separable product sum, so the
factorization theorem above supplies the algebraic multiple-integral law. -/

def finiteProductIntegralSum2D (xs ys : List (Rat × Rat))
    (f g : Rat -> Rat) : Rat :=
  finiteProductSum2D
    (xs.map (fun cell => cell.2 * f cell.1))
    (ys.map (fun cell => cell.2 * g cell.1))
    (fun value => value) (fun value => value)

theorem finiteProductIntegralSum2D_factorized
    (xs ys : List (Rat × Rat)) (f g : Rat -> Rat) :
    finiteProductIntegralSum2D xs ys f g =
      (xs.map (fun cell => cell.2 * f cell.1)).foldl
          (fun acc value => acc + value) 0 *
      (ys.map (fun cell => cell.2 * g cell.1)).foldl
          (fun acc value => acc + value) 0 := by
  simpa [finiteProductIntegralSum2D, Function.comp_def] using
    (finiteProductSum2D_factorized
      (xs.map (fun cell => cell.2 * f cell.1))
      (ys.map (fun cell => cell.2 * g cell.1))
      (fun value => value) (fun value => value))

/- A concrete weighted rectangular computation.  The two sample lists carry
cell widths, so this is a finite two-dimensional integral cell sum rather than
an unweighted Cartesian product. -/
theorem finiteProductIntegralSum2D_weighted_stage :
    finiteProductIntegralSum2D
      [(0, 1 / 2), (1, 1 / 2)]
      [(0, 1), (1, 1)]
      (fun x => x + 1) (fun y => 2 - y) = 9 / 2 := by
  decide +kernel

theorem finiteProductIntegralNestedSum_two_factor
    (xs ys : List (Rat × Rat)) (f g : Rat -> Rat) :
    finiteProductIntegralNestedSum [xs, ys] [f, g] =
      finiteProductIntegralSum2D xs ys f g := by
  rw [finiteProductIntegralNestedSum_factorized]
  rw [finiteProductIntegralSum2D_factorized]
  simp [finiteProductIntegralSum]

def gaussianProductModel (n : Nat) (oneDimensionalGaussian : Rat) : Rat :=
  oneDimensionalGaussian ^ n

private theorem rat_pow_add (q : Rat) (m n : Nat) :
    q ^ (m + n) = q ^ m * q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, Rat.pow_succ, ih, Rat.pow_succ]
      grind [Rat.mul_assoc, Rat.mul_comm]

theorem gaussianProductModel_split (m n : Nat) (oneDimensionalGaussian : Rat) :
    gaussianProductModel (m + n) oneDimensionalGaussian =
      gaussianProductModel m oneDimensionalGaussian *
        gaussianProductModel n oneDimensionalGaussian := by
  unfold gaussianProductModel
  rw [rat_pow_add]

theorem finiteProductSum2D_separable_stage :
    finiteProductSum2D [0, 1, 2] [0, 1] (fun x => x + 1) (fun y => 2 - y) = 18 := by
  decide +kernel

theorem finiteProductSum2D_separable_stage_factorized :
    finiteProductSum2D [0, 1, 2] [0, 1] (fun x => x + 1) (fun y => 2 - y) =
      (([0, 1, 2].map (fun x => x + 1)).foldl (fun acc value => acc + value) 0) *
        (([0, 1].map (fun y => 2 - y)).foldl (fun acc value => acc + value) 0) := by
  decide +kernel

theorem nBallCoeff_zero : nBallCoeff 0 = 1 := by
  rfl

theorem nBallCoeff_one : nBallCoeff 1 = 2 := by
  rfl

theorem nBallCoeff_succ_two (n : Nat) :
    nBallCoeff (n + 2) = (2 : Rat) / (n + 2) * nBallCoeff n := by
  rfl

theorem nBallVolumeModel_zero (piApprox radius : Rat) :
    nBallVolumeModel 0 piApprox radius = 1 := by
  simp [nBallVolumeModel, nBallCoeff, nBallPiExponent]

theorem nBallVolumeModel_one (piApprox radius : Rat) :
    nBallVolumeModel 1 piApprox radius = 2 * radius := by
  unfold nBallVolumeModel nBallCoeff nBallPiExponent
  simp [Rat.pow_one, Rat.mul_assoc, Rat.mul_comm]

theorem nBallVolumeModel_two (piApprox radius : Rat) :
    nBallVolumeModel 2 piApprox radius = piApprox * radius ^ 2 := by
  unfold nBallVolumeModel nBallPiExponent
  simp [nBallCoeff]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem nBallVolumeModel_three (piApprox radius : Rat) :
    nBallVolumeModel 3 piApprox radius =
      (4 / 3 : Rat) * piApprox * radius ^ 3 := by
  unfold nBallVolumeModel nBallPiExponent
  simp [nBallCoeff]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem nBallVolumeModel_four (piApprox radius : Rat) :
    nBallVolumeModel 4 piApprox radius =
      (1 / 2 : Rat) * piApprox ^ 2 * radius ^ 4 := by
  unfold nBallVolumeModel nBallPiExponent
  simp [nBallCoeff]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem nBallVolumeModel_five (piApprox radius : Rat) :
    nBallVolumeModel 5 piApprox radius =
      (8 / 15 : Rat) * piApprox ^ 2 * radius ^ 5 := by
  unfold nBallVolumeModel nBallPiExponent
  simp [nBallCoeff]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem nBallVolumeModel_six (piApprox radius : Rat) :
    nBallVolumeModel 6 piApprox radius =
      (1 / 6 : Rat) * piApprox ^ 3 * radius ^ 6 := by
  unfold nBallVolumeModel nBallPiExponent
  simp [nBallCoeff]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem nBallVolumeModel_seven (piApprox radius : Rat) :
    nBallVolumeModel 7 piApprox radius =
      (16 / 105 : Rat) * piApprox ^ 3 * radius ^ 7 := by
  unfold nBallVolumeModel nBallPiExponent
  simp [nBallCoeff]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem nBallVolumeModel_eight (piApprox radius : Rat) :
    nBallVolumeModel 8 piApprox radius =
      (1 / 24 : Rat) * piApprox ^ 4 * radius ^ 8 := by
  unfold nBallVolumeModel nBallPiExponent
  simp [nBallCoeff]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem nBallVolumeModel_nine (piApprox radius : Rat) :
    nBallVolumeModel 9 piApprox radius =
      (32 / 945 : Rat) * piApprox ^ 4 * radius ^ 9 := by
  unfold nBallVolumeModel nBallPiExponent
  simp [nBallCoeff]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem nBallVolumeModel_ten (piApprox radius : Rat) :
    nBallVolumeModel 10 piApprox radius =
      (1 / 120 : Rat) * piApprox ^ 5 * radius ^ 10 := by
  unfold nBallVolumeModel nBallPiExponent
  simp [nBallCoeff]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem nBallVolumeModel_eleven (piApprox radius : Rat) :
    nBallVolumeModel 11 piApprox radius =
      (64 / 10395 : Rat) * piApprox ^ 5 * radius ^ 11 := by
  have hc : nBallCoeff 11 = (64 / 10395 : Rat) := by
    decide +kernel
  unfold nBallVolumeModel nBallPiExponent
  rw [hc]

theorem nBallVolumeModel_twelve (piApprox radius : Rat) :
    nBallVolumeModel 12 piApprox radius =
      (1 / 720 : Rat) * piApprox ^ 6 * radius ^ 12 := by
  unfold nBallVolumeModel nBallPiExponent
  simp [nBallCoeff]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem nBallVolumeModel_thirteen (piApprox radius : Rat) :
    nBallVolumeModel 13 piApprox radius =
      (128 / 135135 : Rat) * piApprox ^ 6 * radius ^ 13 := by
  have hc : nBallCoeff 13 = (128 / 135135 : Rat) := by
    decide +kernel
  unfold nBallVolumeModel nBallPiExponent
  rw [hc]

theorem nBallVolumeModel_recurrence (n : Nat) (piApprox radius : Rat) :
    nBallVolumeModel (n + 2) piApprox radius =
      (2 * piApprox * radius * radius / (n + 2)) *
        nBallVolumeModel n piApprox radius := by
  unfold nBallVolumeModel nBallPiExponent
  have hexp : (n + 2) / 2 = n / 2 + 1 := by omega
  rw [nBallCoeff_succ_two, hexp, Rat.pow_succ]
  rw [rat_pow_add radius n 2]
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

theorem nBallVolumeModel_scale (n : Nat) (piApprox radius scale : Rat) :
    nBallVolumeModel n piApprox (radius * scale) =
      nBallVolumeModel n piApprox radius * scale ^ n := by
  unfold nBallVolumeModel
  have hpow : ∀ k : Nat, (radius * scale) ^ k = radius ^ k * scale ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Rat.pow_succ, ih, Rat.pow_succ, Rat.pow_succ]
        grind [Rat.mul_assoc, Rat.mul_comm]
  rw [hpow]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem nBallCoeff_nonneg : ∀ n, 0 <= nBallCoeff n := by
  have heven : ∀ k, 0 <= nBallCoeff (2 * k) := by
    intro k
    induction k with
    | zero =>
        decide +kernel
    | succ k ih =>
        have hindex : 2 * (k + 1) = 2 * k + 2 := by omega
        rw [hindex, nBallCoeff_succ_two]
        have hden : 0 < ((2 * k : Nat) : Rat) + 2 := by
          have hk : 0 <= (k : Rat) := Rat.natCast_nonneg
          grind
        have hfactor : 0 <= (2 : Rat) / ((2 * k : Nat) + 2) := by
          rw [Rat.div_def]
          exact Rat.mul_nonneg (by decide +kernel)
            (Rat.le_of_lt ((Rat.inv_pos).2 hden))
        exact Rat.mul_nonneg
          hfactor ih
  have hodd : ∀ k, 0 <= nBallCoeff (2 * k + 1) := by
    intro k
    induction k with
    | zero =>
        decide +kernel
    | succ k ih =>
        have hindex : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
        rw [hindex, nBallCoeff_succ_two]
        have hden : 0 < ((2 * k + 1 : Nat) : Rat) + 2 := by
          have hk : 0 <= (k : Rat) := Rat.natCast_nonneg
          grind
        have hfactor : 0 <= (2 : Rat) / ((2 * k + 1 : Nat) + 2) := by
          rw [Rat.div_def]
          exact Rat.mul_nonneg (by decide +kernel)
            (Rat.le_of_lt ((Rat.inv_pos).2 hden))
        exact Rat.mul_nonneg
          hfactor ih
  intro n
  by_cases he : n % 2 = 0
  · have hindex : n = 2 * (n / 2) := by omega
    rw [hindex]
    exact heven _
  · have hindex : n = 2 * (n / 2) + 1 := by omega
    rw [hindex]
    exact hodd _

theorem nBallVolumeModel_nonneg
    (n : Nat) {piApprox radius : Rat}
    (hpi : 0 <= piApprox) (hradius : 0 <= radius) :
    0 <= nBallVolumeModel n piApprox radius := by
  unfold nBallVolumeModel
  exact Rat.mul_nonneg
    (Rat.mul_nonneg (nBallCoeff_nonneg n)
      (Rat.pow_nonneg hpi))
    (Rat.pow_nonneg hradius)

theorem nBallVolumeModel_stage_six :
    nBallVolumeModel 6 (355 / 113) 1 = 44738875 / 8657382 := by
  decide +kernel

theorem nBallVolumeModel_stage_seven :
    nBallVolumeModel 7 (355 / 113) 1 = 143164400 / 30300837 := by
  decide +kernel

theorem nBallVolumeModel_stage_ten :
    nBallVolumeModel 10 (355 / 113) 1 = 1127643344375 / 442184443032 := by
  decide +kernel

theorem nBallVolumeModel_stage_eleven :
    nBallVolumeModel 11 (355 / 113) 1 = 72169174040000 / 38304227377647 := by
  decide +kernel

theorem nBallVolumeModel_stage_twelve :
    nBallVolumeModel 12 (355 / 113) 1 =
      400313387253125 / 299801052375696 := by
  decide +kernel

theorem nBallVolumeModel_stage_thirteen :
    nBallVolumeModel 13 (355 / 113) 1 =
      51240113568400000 / 56268910017763443 := by
  decide +kernel

end ComputableAnalysis


