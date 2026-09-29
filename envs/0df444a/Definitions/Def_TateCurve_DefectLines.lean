-- Prove2me | Definitions.Def_TateCurve_DefectLines
-- name    : TateCurve_DefectLines
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/6f20681f-a826-5d1e-b03e-d684b33e37f0
-- title:
--   Defect lines: regrouping the Tate defect over the Fk​ basis
-- statement:
--   Standing context: a nontrivially normed field $K$ (ultrametric, complete and of characteristic zero where needed) and a parameter $u \in K$ with $u \neq 0$, $u \neq 1$. The objects introduced here dissect the defect coefficients $D_N(u) =$ `defectCoeff u N`, the $N$-th Cauchy coefficient of $y^2 + xy - (x^3 + a_4x + a_6)$ evaluated on the Tate point series, whose coefficients are the divisor sums $x_N = \sum_{d \mid N} d\,(u^d + u^{-d} - 2)$, $y_N = \sum_{d \mid N}\big(\binom{d}{2}(u^d-u^{-d}) - d\,u^{-d} + d\big)$, $-\sum_{d\mid N}5d^3$ and $-\sum_{d\mid N} b(d)$, with $b(d) = (5d^3+7d^5)/12$, extended at $N=0$ by $x(u)=u/(1-u)^2$, $y(u)=u^2/(1-u)^3$ and $0$. The basis functions are $F_a(u) = u^a + u^{-a} - 2$ (`Fz`) and $G_a(u) = u^a - u^{-a}$ (`Gz`) for $a \in \mathbb{Z}$, with the product rules expressing $F_aF_b$, $G_aG_b$, $F_aG_b$ in terms of $F$ and $G$ at $a\pm b$; `tent u m` is $u(\sum_{i<m}u^i)^2(u^m)^{-1}$, equal to $x(u)F_m(u)$ and to $m^2 + \sum_{j<m}(m-j)F_j(u)$. The convolutions `cauchyMulInt c d N` $= \sum_{i=1}^{N-1} c_i d_{N-i}$ and `cauchyMulInt3 c N` isolate the interior of the Cauchy products; the boundary part is carried by `boundaryTerm u d` and by the natural-number weights `boundaryWeight d j` $= d(d-j)^2(2d-j)/2$. Interior convolutions of divisor sums are transported to the set `Sols N` of positive quadruples with $ab+ce=N$, and the cubic convolution to `Sols3 N`, the positive sextuples $(d,f,a,b,c,e)$ with $df + (ab+ce) = N$, cut out of a product of intervals. Finally the integer line coefficients `boundaryLine`, `mixedLine`, `tentWeight`/`tentLine`, `sFiveLine`, `tripleLine` collect, for each $k$, the total weight attached to $F_k$ from each source, and $$c_{N,k} = -4\,\mathrm{boundaryLine} + \mathrm{mixedLine} - 12\,\mathrm{tentLine} + 4\,\mathrm{sFiveLine} - 4\,\mathrm{tripleLine}.$$ The module's conclusions are $4D_N(u) = \sum_{k=1}^{N} c_{N,k} F_k(u)$, the deduction of $D_N(u)=0$ from vanishing of all $c_{N,k}$, and, by explicit computation, $D_N(u) = 0$ for $1 \le N \le 4$. Auxiliary closed forms for $\sum_{j<n}(a_0+a_1j+a_2j^2+a_3j^3)v^j$ and for $\sum_{j<n}(a_0+a_1j+a_2j^2+a_3j^3)$ serve the boundary and tent evaluations.
--
--   **Relation to Mathlib.** Mathlib has no counterpart for these divisor-sum coefficients of the Tate parametrisation; the basis functions $F$, $G$, the interior convolutions, the index sets and the integer line coefficients are the project's own, built on Mathlib's `Nat.divisors`, `Nat.divisorsAntidiagonal`, `Finset` sums and the geometric-sum identity `geom_sum_mul`.
--
--   **Where it is used.** The line coefficients reduce the Weierstrass identity for the Tate $q$-expansions $x(u)$, $y(u)$ on $y^2+xy = x^3+a_4x+a_6$ to purely integral identities $c_{N,k}=0$, independent of the ground field. The resulting Tate parametrisation is the local model at primes of multiplicative reduction used in the analysis of the Frey curve and its Galois representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_TateCurve_DefectLines.lean

import Mathlib
import Definitions.Def_TateCurve_Defect
import Definitions.Def_NumberTheory_DivisorConvolution
import Theorems.Thm_TateCurve_defectCoeff_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped NNReal

namespace TateCurve

section SmallCauchy

variable {K : Type*} [NontriviallyNormedField K]

theorem cauchyMul_eq_sum_range (c d : ℕ → K) (N : ℕ) :
    cauchyMul c d N = ∑ k ∈ Finset.range (N + 1), c k * d (N - k) := by
  rw [cauchyMul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem cauchyMul_two (c d : ℕ → K) :
    cauchyMul c d 2 = c 0 * d 2 + c 1 * d 1 + c 2 * d 0 := by
  rw [cauchyMul_eq_sum_range]
  simp [Finset.sum_range_succ]

theorem cauchyMul_three (c d : ℕ → K) :
    cauchyMul c d 3 = c 0 * d 3 + c 1 * d 2 + c 2 * d 1 + c 3 * d 0 := by
  rw [cauchyMul_eq_sum_range]
  simp [Finset.sum_range_succ]

theorem cauchyMul_four (c d : ℕ → K) :
    cauchyMul c d 4 = c 0 * d 4 + c 1 * d 3 + c 2 * d 2 + c 3 * d 1 + c 4 * d 0 := by
  rw [cauchyMul_eq_sum_range]
  simp [Finset.sum_range_succ]

end SmallCauchy

section SmallCoefficients

variable {K : Type*} [NontriviallyNormedField K]

private theorem divisors_four : (4 : ℕ).divisors = {1, 2, 4} := by decide

private theorem one_notMem_pair : (1 : ℕ) ∉ ({2} : Finset ℕ) := by decide

private theorem one_notMem_triple : (1 : ℕ) ∉ ({2, 4} : Finset ℕ) := by decide

private theorem two_notMem_single : (2 : ℕ) ∉ ({4} : Finset ℕ) := by decide

private theorem one_notMem_three : (1 : ℕ) ∉ ({3} : Finset ℕ) := by decide

private theorem xCoeffFull_one_eq (u : K) : xCoeffFull u 1 = u + u⁻¹ - 2 := by
  have e : xCoeffFull u 1 = ∑ d ∈ (1 : ℕ).divisors, xDivTerm u d := rfl
  rw [e, Nat.divisors_one, Finset.sum_singleton, xDivTerm]
  push_cast
  ring

private theorem yCoeffFull_one_eq (u : K) : yCoeffFull u 1 = 1 - u⁻¹ := by
  have e : yCoeffFull u 1 = ∑ d ∈ (1 : ℕ).divisors, yDivTerm u d := rfl
  rw [e, Nat.divisors_one, Finset.sum_singleton, yDivTerm]
  norm_num [show Nat.choose 1 2 = 0 from rfl]
  ring

private theorem xCoeffFull_two_eq (u : K) :
    xCoeffFull u 2 = (u + u⁻¹ - 2) + (2 * u ^ 2 + 2 * u⁻¹ ^ 2 - 4) := by
  have e : xCoeffFull u 2 = ∑ d ∈ (2 : ℕ).divisors, xDivTerm u d := rfl
  rw [e, Nat.prime_two.divisors, Finset.sum_insert one_notMem_pair, Finset.sum_singleton,
    xDivTerm, xDivTerm]
  push_cast
  ring

private theorem yCoeffFull_two_eq (u : K) :
    yCoeffFull u 2 = (1 - u⁻¹) + (u ^ 2 - 3 * u⁻¹ ^ 2 + 2) := by
  have e : yCoeffFull u 2 = ∑ d ∈ (2 : ℕ).divisors, yDivTerm u d := rfl
  rw [e, Nat.prime_two.divisors, Finset.sum_insert one_notMem_pair, Finset.sum_singleton,
    yDivTerm, yDivTerm]
  norm_num [show Nat.choose 1 2 = 0 from rfl, show Nat.choose 2 2 = 1 from rfl]
  ring

private theorem xCoeffFull_three_eq (u : K) :
    xCoeffFull u 3 = (u + u⁻¹ - 2) + (3 * u ^ 3 + 3 * u⁻¹ ^ 3 - 6) := by
  have e : xCoeffFull u 3 = ∑ d ∈ (3 : ℕ).divisors, xDivTerm u d := rfl
  rw [e, Nat.prime_three.divisors, Finset.sum_insert one_notMem_three, Finset.sum_singleton,
    xDivTerm, xDivTerm]
  push_cast
  ring

private theorem yCoeffFull_three_eq (u : K) :
    yCoeffFull u 3 = (1 - u⁻¹) + (3 * u ^ 3 - 6 * u⁻¹ ^ 3 + 3) := by
  have e : yCoeffFull u 3 = ∑ d ∈ (3 : ℕ).divisors, yDivTerm u d := rfl
  rw [e, Nat.prime_three.divisors, Finset.sum_insert one_notMem_three, Finset.sum_singleton,
    yDivTerm, yDivTerm]
  norm_num [show Nat.choose 1 2 = 0 from rfl, show Nat.choose 3 2 = 3 from rfl]
  ring

private theorem xCoeffFull_four_eq (u : K) :
    xCoeffFull u 4
      = (u + u⁻¹ - 2) + (2 * u ^ 2 + 2 * u⁻¹ ^ 2 - 4) + (4 * u ^ 4 + 4 * u⁻¹ ^ 4 - 8) := by
  have e : xCoeffFull u 4 = ∑ d ∈ (4 : ℕ).divisors, xDivTerm u d := rfl
  rw [e, divisors_four, Finset.sum_insert one_notMem_triple, Finset.sum_insert two_notMem_single,
    Finset.sum_singleton, xDivTerm, xDivTerm, xDivTerm]
  push_cast
  ring

private theorem yCoeffFull_four_eq (u : K) :
    yCoeffFull u 4
      = (1 - u⁻¹) + (u ^ 2 - 3 * u⁻¹ ^ 2 + 2) + (6 * u ^ 4 - 10 * u⁻¹ ^ 4 + 4) := by
  have e : yCoeffFull u 4 = ∑ d ∈ (4 : ℕ).divisors, yDivTerm u d := rfl
  rw [e, divisors_four, Finset.sum_insert one_notMem_triple, Finset.sum_insert two_notMem_single,
    Finset.sum_singleton, yDivTerm, yDivTerm, yDivTerm]
  norm_num [show Nat.choose 1 2 = 0 from rfl, show Nat.choose 2 2 = 1 from rfl,
    show Nat.choose 4 2 = 6 from rfl]
  ring

private theorem a₄Coeff_one_eq : a₄Coeff (K := K) 1 = -5 := by
  have e : a₄Coeff (K := K) 1 = -(∑ d ∈ (1 : ℕ).divisors, ((5 * d ^ 3 : ℕ) : K)) := rfl
  rw [e, Nat.divisors_one, Finset.sum_singleton]
  norm_num

private theorem a₄Coeff_two_eq : a₄Coeff (K := K) 2 = -45 := by
  have e : a₄Coeff (K := K) 2 = -(∑ d ∈ (2 : ℕ).divisors, ((5 * d ^ 3 : ℕ) : K)) := rfl
  rw [e, Nat.prime_two.divisors, Finset.sum_insert one_notMem_pair, Finset.sum_singleton]
  norm_num

private theorem a₄Coeff_three_eq : a₄Coeff (K := K) 3 = -140 := by
  have e : a₄Coeff (K := K) 3 = -(∑ d ∈ (3 : ℕ).divisors, ((5 * d ^ 3 : ℕ) : K)) := rfl
  rw [e, Nat.prime_three.divisors, Finset.sum_insert one_notMem_three, Finset.sum_singleton]
  norm_num

private theorem a₄Coeff_four_eq : a₄Coeff (K := K) 4 = -365 := by
  have e : a₄Coeff (K := K) 4 = -(∑ d ∈ (4 : ℕ).divisors, ((5 * d ^ 3 : ℕ) : K)) := rfl
  rw [e, divisors_four, Finset.sum_insert one_notMem_triple, Finset.sum_insert two_notMem_single,
    Finset.sum_singleton]
  norm_num

private theorem a₆Coeff_one_eq : a₆Coeff (K := K) 1 = -1 := by
  have e : a₆Coeff (K := K) 1 = -(∑ d ∈ (1 : ℕ).divisors, ((b d : ℕ) : K)) := rfl
  rw [e, Nat.divisors_one, Finset.sum_singleton, b_one]
  norm_num

private theorem a₆Coeff_two_eq : a₆Coeff (K := K) 2 = -23 := by
  have e : a₆Coeff (K := K) 2 = -(∑ d ∈ (2 : ℕ).divisors, ((b d : ℕ) : K)) := rfl
  rw [e, Nat.prime_two.divisors, Finset.sum_insert one_notMem_pair, Finset.sum_singleton]
  norm_num [b]

private theorem a₆Coeff_three_eq : a₆Coeff (K := K) 3 = -154 := by
  have e : a₆Coeff (K := K) 3 = -(∑ d ∈ (3 : ℕ).divisors, ((b d : ℕ) : K)) := rfl
  rw [e, Nat.prime_three.divisors, Finset.sum_insert one_notMem_three, Finset.sum_singleton]
  norm_num [b]

private theorem a₆Coeff_four_eq : a₆Coeff (K := K) 4 = -647 := by
  have e : a₆Coeff (K := K) 4 = -(∑ d ∈ (4 : ℕ).divisors, ((b d : ℕ) : K)) := rfl
  rw [e, divisors_four, Finset.sum_insert one_notMem_triple, Finset.sum_insert two_notMem_single,
    Finset.sum_singleton]
  norm_num [b]

end SmallCoefficients

section Identities

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u : K}

theorem defectCoeff_two (hu0 : u ≠ 0) (hu1 : u ≠ 1) : defectCoeff u 2 = 0 := by
  have h1u : (1 : K) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  simp only [defectCoeff, cauchyMul_two, cauchyMul_one, cauchyMul_zero,
    xCoeffFull_zero, yCoeffFull_zero, a₄Coeff_zero, a₆Coeff_zero,
    xCoeffFull_one_eq, yCoeffFull_one_eq, xCoeffFull_two_eq, yCoeffFull_two_eq,
    a₄Coeff_one_eq, a₄Coeff_two_eq, a₆Coeff_two_eq, xfun, yfun]
  field_simp
  ring

theorem defectCoeff_three (hu0 : u ≠ 0) (hu1 : u ≠ 1) : defectCoeff u 3 = 0 := by
  have h1u : (1 : K) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  simp only [defectCoeff, cauchyMul_three, cauchyMul_two, cauchyMul_one, cauchyMul_zero,
    xCoeffFull_zero, yCoeffFull_zero, a₄Coeff_zero, a₆Coeff_zero,
    xCoeffFull_one_eq, yCoeffFull_one_eq, xCoeffFull_two_eq, yCoeffFull_two_eq,
    xCoeffFull_three_eq, yCoeffFull_three_eq,
    a₄Coeff_one_eq, a₄Coeff_two_eq, a₄Coeff_three_eq, a₆Coeff_three_eq, xfun, yfun]
  field_simp
  ring

theorem defectCoeff_four (hu0 : u ≠ 0) (hu1 : u ≠ 1) : defectCoeff u 4 = 0 := by
  have h1u : (1 : K) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  simp only [defectCoeff, cauchyMul_four, cauchyMul_three, cauchyMul_two, cauchyMul_one,
    cauchyMul_zero, xCoeffFull_zero, yCoeffFull_zero, a₄Coeff_zero, a₆Coeff_zero,
    xCoeffFull_one_eq, yCoeffFull_one_eq, xCoeffFull_two_eq, yCoeffFull_two_eq,
    xCoeffFull_three_eq, yCoeffFull_three_eq, xCoeffFull_four_eq, yCoeffFull_four_eq,
    a₄Coeff_one_eq, a₄Coeff_two_eq, a₄Coeff_three_eq, a₄Coeff_four_eq, a₆Coeff_four_eq,
    xfun, yfun]
  field_simp
  ring

theorem defectCoeff_eq_zero_of_le_four (hu0 : u ≠ 0) (hu1 : u ≠ 1) {N : ℕ} (hN : 0 < N)
    (hN4 : N ≤ 4) : defectCoeff u N = 0 := by
  interval_cases N
  · exact defectCoeff_one hu0 hu1
  · exact defectCoeff_two hu0 hu1
  · exact defectCoeff_three hu0 hu1
  · exact defectCoeff_four hu0 hu1

end Identities

end TateCurve

open scoped NNReal

namespace TateCurve

section InteriorConvolution

variable {K : Type*} [NontriviallyNormedField K]

noncomputable def cauchyMulInt (c d : ℕ → K) (N : ℕ) : K :=
  ∑ i ∈ Finset.Ico 1 N, c i * d (N - i)

@[simp] theorem cauchyMulInt_zero (c d : ℕ → K) : cauchyMulInt c d 0 = 0 := by
  simp [cauchyMulInt]

@[simp] theorem cauchyMulInt_one (c d : ℕ → K) : cauchyMulInt c d 1 = 0 := by
  simp [cauchyMulInt]

theorem cauchyMulInt_congr_pos {c c' d d' : ℕ → K} (N : ℕ)
    (hc : ∀ i, 0 < i → c i = c' i) (hd : ∀ i, 0 < i → d i = d' i) :
    cauchyMulInt c d N = cauchyMulInt c' d' N := by
  rw [cauchyMulInt, cauchyMulInt]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_Ico] at hi
  rw [hc i (by omega), hd (N - i) (by omega)]

theorem cauchyMul_eq_boundary_add_int (c d : ℕ → K) {N : ℕ} (hN : 0 < N) :
    cauchyMul c d N = c 0 * d N + c N * d 0 + cauchyMulInt c d N := by
  rw [cauchyMul_eq_sum_range, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos N)]
  simp only [Nat.zero_add, Nat.sub_zero]
  rw [Finset.sum_Ico_succ_top hN, Nat.sub_self, cauchyMulInt]
  ring

noncomputable def cauchyMulInt3 (c : ℕ → K) (N : ℕ) : K :=
  ∑ i ∈ Finset.Ico 1 N, c i * cauchyMulInt c c (N - i)

@[simp] theorem cauchyMulInt3_zero (c : ℕ → K) : cauchyMulInt3 c 0 = 0 := by
  simp [cauchyMulInt3]

theorem cauchyMul_cube_eq_boundary_add_int (c : ℕ → K) {N : ℕ} (hN : 0 < N) :
    cauchyMul c (cauchyMul c c) N
      = 3 * (c 0 * c 0) * c N + 3 * c 0 * cauchyMulInt c c N + cauchyMulInt3 c N := by
  have hterm : ∀ i ∈ Finset.Ico 1 N,
      c i * cauchyMul c c (N - i)
        = 2 * c 0 * (c i * c (N - i)) + c i * cauchyMulInt c c (N - i) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [cauchyMul_eq_boundary_add_int c c (show 0 < N - i by omega)]
    ring
  have hsplit : cauchyMulInt c (cauchyMul c c) N
      = 2 * c 0 * cauchyMulInt c c N + cauchyMulInt3 c N := by
    rw [cauchyMulInt, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
      cauchyMulInt, cauchyMulInt3]
  rw [cauchyMul_eq_boundary_add_int c (cauchyMul c c) hN, hsplit,
    cauchyMul_eq_boundary_add_int c c hN, cauchyMul_zero]
  ring

end InteriorConvolution

section PositiveIndex

variable {K : Type*} [NontriviallyNormedField K]

theorem xCoeffFull_of_pos (u : K) {N : ℕ} (hN : 0 < N) : xCoeffFull u N = xCoeff u N := by
  cases N with
  | zero => exact absurd hN (lt_irrefl 0)
  | succ M => rfl

theorem yCoeffFull_of_pos (u : K) {N : ℕ} (hN : 0 < N) : yCoeffFull u N = yCoeff u N := by
  cases N with
  | zero => exact absurd hN (lt_irrefl 0)
  | succ M => rfl

end PositiveIndex

section SolsBridge

open FLT.DivisorConvolution

variable {R : Type*} [CommSemiring R]

private theorem fiber_eval_mul (f g : ℕ → R) (N i : ℕ) (hi : i ∈ Finset.Ico 1 N) :
    ∑ x ∈ (Sols N).filter (fun x => x.1 * x.2.1 = i), f x.1 * g x.2.2.1
      = (∑ d ∈ i.divisors, f d) * ∑ e ∈ (N - i).divisors, g e := by
  rw [Finset.mem_Ico] at hi
  have hi0 : i ≠ 0 := by omega
  have hNi0 : N - i ≠ 0 := by omega
  rw [show (∑ d ∈ i.divisors, f d) = ∑ p ∈ i.divisorsAntidiagonal, f p.1 from
      (Nat.sum_divisorsAntidiagonal (fun a _ => f a)).symm,
    show (∑ e ∈ (N - i).divisors, g e) = ∑ p ∈ (N - i).divisorsAntidiagonal, g p.1 from
      (Nat.sum_divisorsAntidiagonal (fun a _ => g a)).symm,
    Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (i := fun x => ((x.1, x.2.1), (x.2.2.1, x.2.2.2)))
    (j := fun p => (p.1.1, p.1.2, p.2.1, p.2.2)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxS, hab⟩ := hx
    obtain ⟨ha, hb, hc, hd, heq⟩ := mem_Sols.1 hxS
    rw [Finset.mem_product, Nat.mem_divisorsAntidiagonal, Nat.mem_divisorsAntidiagonal]
    refine ⟨⟨hab, hi0⟩, ?_, hNi0⟩
    show x.2.2.1 * x.2.2.2 = N - i
    omega
  · intro p hp
    rw [Finset.mem_product, Nat.mem_divisorsAntidiagonal, Nat.mem_divisorsAntidiagonal] at hp
    obtain ⟨⟨hab, _⟩, hcd, _⟩ := hp
    rw [Finset.mem_filter]
    constructor
    · refine mem_Sols.2 ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact Nat.pos_of_ne_zero (left_ne_zero_of_mul (hab ▸ hi0))
      · exact Nat.pos_of_ne_zero (right_ne_zero_of_mul (hab ▸ hi0))
      · exact Nat.pos_of_ne_zero (left_ne_zero_of_mul (hcd ▸ hNi0))
      · exact Nat.pos_of_ne_zero (right_ne_zero_of_mul (hcd ▸ hNi0))
      · show p.1.1 * p.1.2 + p.2.1 * p.2.2 = N
        rw [hab, hcd]
        omega
    · exact hab
  · intro x _
    rfl
  · intro p _
    rfl
  · intro x _
    rfl

theorem sum_Ico_divisorSum_mul_eq_sum_Sols (f g : ℕ → R) (N : ℕ) :
    ∑ i ∈ Finset.Ico 1 N, (∑ d ∈ i.divisors, f d) * ∑ e ∈ (N - i).divisors, g e
      = ∑ x ∈ Sols N, f x.1 * g x.2.2.1 := by
  have hmaps : ∀ x ∈ Sols N, x.1 * x.2.1 ∈ Finset.Ico 1 N := by
    intro x hx
    obtain ⟨ha, hb, hc, hd, heq⟩ := mem_Sols.1 hx
    rw [Finset.mem_Ico]
    constructor
    · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    · have h1 : 0 < x.2.2.1 * x.2.2.2 := Nat.mul_pos hc hd
      omega
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.Ico 1 N) hmaps
    (fun x => f x.1 * g x.2.2.1)]
  exact Finset.sum_congr rfl fun i hi => (fiber_eval_mul f g N i hi).symm

end SolsBridge

section TateBridge

open FLT.DivisorConvolution

variable {K : Type*} [NontriviallyNormedField K]

theorem cauchyMulInt_eq_sum_Sols {c d : ℕ → K} {f g : ℕ → K} (N : ℕ)
    (hc : ∀ i, 0 < i → c i = ∑ a ∈ i.divisors, f a)
    (hd : ∀ i, 0 < i → d i = ∑ a ∈ i.divisors, g a) :
    cauchyMulInt c d N = ∑ x ∈ Sols N, f x.1 * g x.2.2.1 := by
  have h1 : cauchyMulInt c d N
      = ∑ i ∈ Finset.Ico 1 N, (∑ a ∈ i.divisors, f a) * ∑ e ∈ (N - i).divisors, g e := by
    rw [cauchyMulInt]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    rw [hc i (by omega), hd (N - i) (by omega)]
  rw [h1]
  exact sum_Ico_divisorSum_mul_eq_sum_Sols f g N

theorem cauchyMulInt_yy_eq_sum_Sols (u : K) (N : ℕ) :
    cauchyMulInt (yCoeffFull u) (yCoeffFull u) N
      = ∑ x ∈ Sols N, yDivTerm u x.1 * yDivTerm u x.2.2.1 :=
  cauchyMulInt_eq_sum_Sols N (fun i hi => by rw [yCoeffFull_of_pos u hi, yCoeff])
    (fun i hi => by rw [yCoeffFull_of_pos u hi, yCoeff])

theorem cauchyMulInt_xy_eq_sum_Sols (u : K) (N : ℕ) :
    cauchyMulInt (xCoeffFull u) (yCoeffFull u) N
      = ∑ x ∈ Sols N, xDivTerm u x.1 * yDivTerm u x.2.2.1 :=
  cauchyMulInt_eq_sum_Sols N (fun i hi => by rw [xCoeffFull_of_pos u hi, xCoeff])
    (fun i hi => by rw [yCoeffFull_of_pos u hi, yCoeff])

theorem cauchyMulInt_xx_eq_sum_Sols (u : K) (N : ℕ) :
    cauchyMulInt (xCoeffFull u) (xCoeffFull u) N
      = ∑ x ∈ Sols N, xDivTerm u x.1 * xDivTerm u x.2.2.1 :=
  cauchyMulInt_eq_sum_Sols N (fun i hi => by rw [xCoeffFull_of_pos u hi, xCoeff])
    (fun i hi => by rw [xCoeffFull_of_pos u hi, xCoeff])

end TateBridge

section DefectSplit

variable {K : Type*} [NontriviallyNormedField K]

theorem defectCoeff_eq_boundary_add_int (u : K) {N : ℕ} (hN : 0 < N) :
    defectCoeff u N
      = ((2 * yfun u + xfun u) * yCoeff u N + (yfun u - 3 * xfun u ^ 2) * xCoeff u N
          - xfun u * a₄Coeff N - a₆Coeff N)
        + (cauchyMulInt (yCoeffFull u) (yCoeffFull u) N
            + cauchyMulInt (xCoeffFull u) (yCoeffFull u) N
            - 3 * xfun u * cauchyMulInt (xCoeffFull u) (xCoeffFull u) N
            - cauchyMulInt a₄Coeff (xCoeffFull u) N
            - cauchyMulInt3 (xCoeffFull u) N) := by
  have hx0 : xCoeffFull u 0 = xfun u := rfl
  have hy0 : yCoeffFull u 0 = yfun u := rfl
  have ha0 : a₄Coeff (K := K) 0 = 0 := rfl
  rw [defectCoeff,
    cauchyMul_eq_boundary_add_int (yCoeffFull u) (yCoeffFull u) hN,
    cauchyMul_eq_boundary_add_int (xCoeffFull u) (yCoeffFull u) hN,
    cauchyMul_cube_eq_boundary_add_int (xCoeffFull u) hN,
    cauchyMul_eq_boundary_add_int a₄Coeff (xCoeffFull u) hN,
    xCoeffFull_of_pos u hN, yCoeffFull_of_pos u hN, hx0, hy0, ha0]
  ring

end DefectSplit

end TateCurve

open scoped NNReal

namespace TateCurve

section FGBasis

variable {K : Type*} [Field K] (u : K)

noncomputable def Fz (a : ℤ) : K := u ^ a + u ^ (-a) - 2

noncomputable def Gz (a : ℤ) : K := u ^ a - u ^ (-a)

@[simp] theorem Fz_zero : Fz u 0 = 0 := by norm_num [Fz]

@[simp] theorem Gz_zero : Gz u 0 = 0 := by simp [Gz]

theorem Fz_neg (a : ℤ) : Fz u (-a) = Fz u a := by simp only [Fz, neg_neg]; ring

theorem Gz_neg (a : ℤ) : Gz u (-a) = -Gz u a := by simp only [Gz, neg_neg]; ring

theorem Fz_natCast (d : ℕ) : Fz u (d : ℤ) = u ^ d + u⁻¹ ^ d - 2 := by
  simp [Fz, zpow_natCast, zpow_neg, inv_pow]

theorem Gz_natCast (d : ℕ) : Gz u (d : ℤ) = u ^ d - u⁻¹ ^ d := by
  simp [Gz, zpow_natCast, zpow_neg, inv_pow]

variable {u}

theorem Fz_mul_Fz (hu : u ≠ 0) (a b : ℤ) :
    Fz u a * Fz u b = Fz u (a + b) + Fz u (a - b) - 2 * Fz u a - 2 * Fz u b := by
  have ha : u ^ a ≠ 0 := zpow_ne_zero a hu
  have hb : u ^ b ≠ 0 := zpow_ne_zero b hu
  simp only [Fz, zpow_add₀ hu, zpow_sub₀ hu, zpow_neg]
  field_simp
  ring

theorem Gz_mul_Gz (hu : u ≠ 0) (a b : ℤ) :
    Gz u a * Gz u b = Fz u (a + b) - Fz u (a - b) := by
  have ha : u ^ a ≠ 0 := zpow_ne_zero a hu
  have hb : u ^ b ≠ 0 := zpow_ne_zero b hu
  simp only [Fz, Gz, zpow_add₀ hu, zpow_sub₀ hu, zpow_neg]
  field_simp
  ring

theorem Fz_mul_Gz (hu : u ≠ 0) (a b : ℤ) :
    Fz u a * Gz u b = Gz u (a + b) - Gz u (a - b) - 2 * Gz u b := by
  have ha : u ^ a ≠ 0 := zpow_ne_zero a hu
  have hb : u ^ b ≠ 0 := zpow_ne_zero b hu
  simp only [Fz, Gz, zpow_add₀ hu, zpow_sub₀ hu, zpow_neg]
  field_simp
  ring

end FGBasis

section Factorization

variable {K : Type*} [NontriviallyNormedField K] {u : K}

theorem xDivTerm_eq_mul_Fz (u : K) (d : ℕ) : xDivTerm u d = (d : K) * Fz u (d : ℤ) := by
  rw [xDivTerm, Fz_natCast]

theorem two_mul_yDivTerm (u : K) (d : ℕ) :
    2 * yDivTerm u d = (d : K) ^ 2 * Gz u (d : ℤ) - (d : K) * Fz u (d : ℤ) := by
  rcases d with _ | m
  · simp [yDivTerm]
  · rw [yDivTerm, Gz_natCast, Fz_natCast]
    have h2 : (m + 1).choose 2 * 2 = (m + 1) * m := by
      rw [Nat.choose_two_right, Nat.succ_sub_one,
        Nat.div_mul_cancel (by simpa [Nat.mul_comm] using (Nat.even_mul_succ_self m).two_dvd)]
    have hcast : (((m + 1).choose 2 : ℕ) : K) * 2 = ((m + 1 : ℕ) : K) * (m : K) := by
      have h := congrArg (Nat.cast : ℕ → K) h2
      push_cast at h ⊢
      linear_combination h
    push_cast at hcast ⊢
    linear_combination (u ^ (m + 1) - u⁻¹ ^ (m + 1)) * hcast

theorem Fz_natCast_eq_geomSum (hu : u ≠ 0) (d : ℕ) :
    Fz u (d : ℤ) = (u - 1) ^ 2 * (∑ i ∈ Finset.range d, u ^ i) ^ 2 * (u ^ d)⁻¹ := by
  have hz : u ^ d ≠ 0 := pow_ne_zero d hu
  have hg : (∑ i ∈ Finset.range d, u ^ i) * (u - 1) = u ^ d - 1 := geom_sum_mul u d
  rw [Fz_natCast, inv_pow,
    show (u - 1) ^ 2 * (∑ i ∈ Finset.range d, u ^ i) ^ 2
      = ((∑ i ∈ Finset.range d, u ^ i) * (u - 1)) ^ 2 by ring, hg]
  field_simp
  ring

theorem Gz_natCast_eq_geomSum (hu : u ≠ 0) (d : ℕ) :
    Gz u (d : ℤ) = (u - 1) * (∑ i ∈ Finset.range d, u ^ i) * (u ^ d + 1) * (u ^ d)⁻¹ := by
  have hz : u ^ d ≠ 0 := pow_ne_zero d hu
  have hg : (∑ i ∈ Finset.range d, u ^ i) * (u - 1) = u ^ d - 1 := geom_sum_mul u d
  rw [Gz_natCast, inv_pow,
    show (u - 1) * (∑ i ∈ Finset.range d, u ^ i) * (u ^ d + 1)
      = (∑ i ∈ Finset.range d, u ^ i) * (u - 1) * (u ^ d + 1) by ring, hg]
  field_simp
  ring

theorem xfun_mul_Fz_natCast (hu : u ≠ 0) (hu1 : u ≠ 1) (d : ℕ) :
    xfun u * Fz u (d : ℤ) = u * (∑ i ∈ Finset.range d, u ^ i) ^ 2 * (u ^ d)⁻¹ := by
  have h1u : (1 : K) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  have hz : u ^ d ≠ 0 := pow_ne_zero d hu
  rw [Fz_natCast_eq_geomSum hu, xfun]
  field_simp
  ring

end Factorization

section CubicSums

variable {R : Type*} [CommRing R]

theorem sum_cubic_mul_geom_pow (a₀ a₁ a₂ a₃ v : R) (n : ℕ) :
    (∑ j ∈ Finset.range n, (a₀ + a₁ * (j : R) + a₂ * (j : R) ^ 2 + a₃ * (j : R) ^ 3) * v ^ j)
        * (v - 1) ^ 4
      = (a₀ * (v - 1) ^ 3 + a₁ * (v - 1) ^ 2 * ((n : R) * v - n - v)
          + a₂ * (v - 1) * ((n : R) ^ 2 * (v - 1) ^ 2 - 2 * n * v * (v - 1) + v ^ 2 + v)
          + a₃ * ((n : R) ^ 3 * (v - 1) ^ 3 - 3 * (n : R) ^ 2 * v * (v - 1) ^ 2
              + 3 * (n : R) * v * (v ^ 2 - 1) - v * (v ^ 2 + 4 * v + 1))) * v ^ n
        + (a₀ * (-(v - 1) ^ 3) + a₁ * (v - 1) ^ 2 * v + a₂ * (v - 1) * (-(v ^ 2) - v)
            + a₃ * (v * (v ^ 2 + 4 * v + 1))) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    push_cast
    ring

theorem sum_cubic_mul_twelve (a₀ a₁ a₂ a₃ : R) (n : ℕ) :
    (∑ j ∈ Finset.range n, (a₀ + a₁ * (j : R) + a₂ * (j : R) ^ 2 + a₃ * (j : R) ^ 3)) * 12
      = 12 * a₀ * (n : R) + 6 * a₁ * ((n : R) ^ 2 - n)
        + 2 * a₂ * (2 * (n : R) ^ 3 - 3 * (n : R) ^ 2 + n)
        + 3 * a₃ * ((n : R) ^ 4 - 2 * (n : R) ^ 3 + (n : R) ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    push_cast
    ring

end CubicSums

section CubicSumsField

variable {K : Type*} [Field K]

theorem sum_cubic_geom_eq_div (a₀ a₁ a₂ a₃ : K) {v : K} (hv : v ≠ 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, (a₀ + a₁ * (j : K) + a₂ * (j : K) ^ 2 + a₃ * (j : K) ^ 3) * v ^ j
      = ((a₀ * (v - 1) ^ 3 + a₁ * (v - 1) ^ 2 * ((n : K) * v - n - v)
          + a₂ * (v - 1) * ((n : K) ^ 2 * (v - 1) ^ 2 - 2 * n * v * (v - 1) + v ^ 2 + v)
          + a₃ * ((n : K) ^ 3 * (v - 1) ^ 3 - 3 * (n : K) ^ 2 * v * (v - 1) ^ 2
              + 3 * (n : K) * v * (v ^ 2 - 1) - v * (v ^ 2 + 4 * v + 1))) * v ^ n
        + (a₀ * (-(v - 1) ^ 3) + a₁ * (v - 1) ^ 2 * v + a₂ * (v - 1) * (-(v ^ 2) - v)
            + a₃ * (v * (v ^ 2 + 4 * v + 1)))) / (v - 1) ^ 4 := by
  rw [eq_div_iff (pow_ne_zero 4 (sub_ne_zero.mpr hv))]
  exact sum_cubic_mul_geom_pow a₀ a₁ a₂ a₃ v n

theorem sum_cubic_eq_div [CharZero K] (a₀ a₁ a₂ a₃ : K) (n : ℕ) :
    ∑ j ∈ Finset.range n, (a₀ + a₁ * (j : K) + a₂ * (j : K) ^ 2 + a₃ * (j : K) ^ 3)
      = (12 * a₀ * (n : K) + 6 * a₁ * ((n : K) ^ 2 - n)
          + 2 * a₂ * (2 * (n : K) ^ 3 - 3 * (n : K) ^ 2 + n)
          + 3 * a₃ * ((n : K) ^ 4 - 2 * (n : K) ^ 3 + (n : K) ^ 2)) / 12 := by
  rw [eq_div_iff (by norm_num : (12 : K) ≠ 0)]
  exact sum_cubic_mul_twelve a₀ a₁ a₂ a₃ n

end CubicSumsField

def boundaryWeight (d j : ℕ) : ℕ := d * (d - j) ^ 2 * (2 * d - j) / 2

theorem even_boundaryWeight_num (d j : ℕ) : Even (d * (d - j) ^ 2 * (2 * d - j)) := by
  rcases Nat.even_or_odd d with hd | hd
  · exact (hd.mul_right _).mul_right _
  · rcases Nat.even_or_odd j with hj | hj
    ·
      have h2d : Even (2 * d - j) := by
        rcases Nat.le_total j (2 * d) with h | h
        · exact (Nat.even_sub h).mpr (by simp [hj])
        · simp [Nat.sub_eq_zero_of_le h]
      exact h2d.mul_left _
    ·
      have hdj : Even (d - j) := by
        rcases Nat.le_total j d with h | h
        · exact (Nat.even_sub h).mpr (by simp [Nat.not_even_iff_odd.mpr hd,
            Nat.not_even_iff_odd.mpr hj])
        · simp [Nat.sub_eq_zero_of_le h]
      exact (((by simpa [sq] using hdj.mul_right (d - j)) : Even ((d - j) ^ 2)).mul_left _).mul_right _

theorem two_mul_boundaryWeight (d j : ℕ) :
    2 * boundaryWeight d j = d * (d - j) ^ 2 * (2 * d - j) :=
  Nat.mul_div_cancel' (even_boundaryWeight_num d j).two_dvd

section BoundaryTerm

variable {K : Type*} [NontriviallyNormedField K] {u : K}

noncomputable def boundaryTerm (u : K) (d : ℕ) : K :=
  (2 * yfun u + xfun u) * yDivTerm u d + (yfun u - 3 * xfun u ^ 2) * xDivTerm u d
    + ((5 * d ^ 3 : ℕ) : K) * xfun u + ((b d : ℕ) : K)

theorem boundaryTerm_eq_neg_sum [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (d : ℕ) :
    boundaryTerm u d
      = -∑ j ∈ Finset.Ico 1 d, ((boundaryWeight d j : ℕ) : K) * Fz u (j : ℤ) := by
  haveI : NeZero (2 : K) := ⟨by norm_num⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, neg_zero]
    have h1 : xDivTerm u 0 = 0 := by simp [xDivTerm]
    have h2 : yDivTerm u 0 = 0 := by simp [yDivTerm]
    simp [boundaryTerm, h1, h2]

  have h1u : (1 : K) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  have hu1' : u - 1 ≠ 0 := sub_ne_zero.mpr hu1
  have hui1 : u⁻¹ ≠ 1 := fun h => hu1 (by rwa [inv_eq_one] at h)
  have hui1' : u⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr hui1
  have hzd : u ^ d ≠ 0 := pow_ne_zero d hu0
  have h2 : (2 : K) ≠ 0 := by norm_num
  have h12 : (12 : K) ≠ 0 := by norm_num

  have hIco : (∑ j ∈ Finset.Ico 1 d, ((boundaryWeight d j : ℕ) : K) * Fz u (j : ℤ))
      = ∑ j ∈ Finset.range d, ((boundaryWeight d j : ℕ) : K) * Fz u (j : ℤ) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hd]
    simp

  have hterm : ∀ j ∈ Finset.range d,
      (2 : K) * (((boundaryWeight d j : ℕ) : K) * Fz u (j : ℤ))
        = (2 * (d : K) ^ 4 + -(5 * (d : K) ^ 3) * (j : K) + 4 * (d : K) ^ 2 * (j : K) ^ 2
              + -(d : K) * (j : K) ^ 3) * u ^ j
          + (2 * (d : K) ^ 4 + -(5 * (d : K) ^ 3) * (j : K) + 4 * (d : K) ^ 2 * (j : K) ^ 2
              + -(d : K) * (j : K) ^ 3) * u⁻¹ ^ j
          + (-2) * (2 * (d : K) ^ 4 + -(5 * (d : K) ^ 3) * (j : K) + 4 * (d : K) ^ 2 * (j : K) ^ 2
              + -(d : K) * (j : K) ^ 3) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hcast : (2 : K) * ((boundaryWeight d j : ℕ) : K)
        = (d : K) * ((d : K) - (j : K)) ^ 2 * (2 * (d : K) - (j : K)) := by
      have h := congrArg (Nat.cast : ℕ → K) (two_mul_boundaryWeight d j)
      push_cast [Nat.cast_sub hj.le, Nat.cast_sub (by omega : j ≤ 2 * d)] at h
      linear_combination h
    rw [Fz_natCast]
    linear_combination (u ^ j + u⁻¹ ^ j - 2) * hcast

  have hSA : ∑ j ∈ Finset.range d,
      (2 * (d : K) ^ 4 + -(5 * (d : K) ^ 3) * (j : K) + 4 * (d : K) ^ 2 * (j : K) ^ 2
        + -(d : K) * (j : K) ^ 3) * u ^ j
      = _ := sum_cubic_geom_eq_div (2 * (d : K) ^ 4) (-(5 * (d : K) ^ 3)) (4 * (d : K) ^ 2)
          (-(d : K)) hu1 d
  have hSB : ∑ j ∈ Finset.range d,
      (2 * (d : K) ^ 4 + -(5 * (d : K) ^ 3) * (j : K) + 4 * (d : K) ^ 2 * (j : K) ^ 2
        + -(d : K) * (j : K) ^ 3) * u⁻¹ ^ j
      = _ := sum_cubic_geom_eq_div (2 * (d : K) ^ 4) (-(5 * (d : K) ^ 3)) (4 * (d : K) ^ 2)
          (-(d : K)) hui1 d
  have hSC : ∑ j ∈ Finset.range d,
      (2 * (d : K) ^ 4 + -(5 * (d : K) ^ 3) * (j : K) + 4 * (d : K) ^ 2 * (j : K) ^ 2
        + -(d : K) * (j : K) ^ 3)
      = _ := sum_cubic_eq_div (2 * (d : K) ^ 4) (-(5 * (d : K) ^ 3)) (4 * (d : K) ^ 2)
          (-(d : K)) d

  have hb12 : ((b d : ℕ) : K) = (5 * (d : K) ^ 3 + 7 * (d : K) ^ 5) / 12 := by
    have h := congrArg (Nat.cast : ℕ → K) (b_mul_twelve d)
    push_cast at h
    rw [eq_div_iff h12]
    linear_combination h

  apply mul_left_cancel₀ h2
  rw [hIco, mul_neg, Finset.mul_sum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, hSA, hSB, hSC]
  simp only [boundaryTerm, xDivTerm, yDivTerm, xfun, yfun]
  rw [Nat.cast_choose_two, hb12]
  push_cast
  simp only [inv_pow]
  field_simp
  ring

end BoundaryTerm

section NormalForm

variable {K : Type*} [NontriviallyNormedField K] {u : K}

theorem a₄Coeff_of_pos {N : ℕ} (hN : 0 < N) :
    a₄Coeff (K := K) N = -(∑ d ∈ N.divisors, ((5 * d ^ 3 : ℕ) : K)) := by
  cases N with
  | zero => exact absurd hN (lt_irrefl 0)
  | succ M => rfl

theorem a₆Coeff_of_pos {N : ℕ} (hN : 0 < N) :
    a₆Coeff (K := K) N = -(∑ d ∈ N.divisors, ((b d : ℕ) : K)) := by
  cases N with
  | zero => exact absurd hN (lt_irrefl 0)
  | succ M => rfl

theorem sum_boundaryTerm_eq (u : K) {N : ℕ} (hN : 0 < N) :
    (2 * yfun u + xfun u) * yCoeff u N + (yfun u - 3 * xfun u ^ 2) * xCoeff u N
        - xfun u * a₄Coeff N - a₆Coeff N
      = ∑ d ∈ N.divisors, boundaryTerm u d := by
  rw [a₄Coeff_of_pos hN, a₆Coeff_of_pos hN]
  simp only [xCoeff, yCoeff, Finset.mul_sum, mul_neg, sub_neg_eq_add]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun d _ => by simp only [boundaryTerm]; ring

theorem defectCoeff_eq_sum_boundaryTerm_add_int (u : K) {N : ℕ} (hN : 0 < N) :
    defectCoeff u N
      = (∑ d ∈ N.divisors, boundaryTerm u d)
        + (cauchyMulInt (yCoeffFull u) (yCoeffFull u) N
            + cauchyMulInt (xCoeffFull u) (yCoeffFull u) N
            - 3 * xfun u * cauchyMulInt (xCoeffFull u) (xCoeffFull u) N
            - cauchyMulInt a₄Coeff (xCoeffFull u) N
            - cauchyMulInt3 (xCoeffFull u) N) := by
  rw [defectCoeff_eq_boundary_add_int u hN, sum_boundaryTerm_eq u hN]

theorem defectCoeff_eq_neg_sum_boundaryWeight_add_int [CharZero K]
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) {N : ℕ} (hN : 0 < N) :
    defectCoeff u N
      = -(∑ d ∈ N.divisors, ∑ j ∈ Finset.Ico 1 d, ((boundaryWeight d j : ℕ) : K) * Fz u (j : ℤ))
        + (cauchyMulInt (yCoeffFull u) (yCoeffFull u) N
            + cauchyMulInt (xCoeffFull u) (yCoeffFull u) N
            - 3 * xfun u * cauchyMulInt (xCoeffFull u) (xCoeffFull u) N
            - cauchyMulInt a₄Coeff (xCoeffFull u) N
            - cauchyMulInt3 (xCoeffFull u) N) := by
  rw [defectCoeff_eq_sum_boundaryTerm_add_int u hN]
  congr 1
  rw [Finset.sum_congr rfl fun d _ => boundaryTerm_eq_neg_sum hu0 hu1 d, ← Finset.sum_neg_distrib]

end NormalForm

end TateCurve

open scoped NNReal

namespace TateCurve

section Tent

variable {K : Type*} [NontriviallyNormedField K] {u : K}

noncomputable def tent (u : K) (m : ℕ) : K :=
  u * (∑ i ∈ Finset.range m, u ^ i) ^ 2 * (u ^ m)⁻¹

@[simp] theorem tent_zero : tent u 0 = 0 := by simp [tent]

@[simp] theorem tent_one (hu0 : u ≠ 0) : tent u 1 = 1 := by
  simp [tent, mul_inv_cancel₀ hu0]

theorem xfun_mul_Fz_eq_tent (hu0 : u ≠ 0) (hu1 : u ≠ 1) (m : ℕ) :
    xfun u * Fz u (m : ℤ) = tent u m :=
  xfun_mul_Fz_natCast hu0 hu1 m

theorem Fz_natAbs (u : K) (a : ℤ) : Fz u (a.natAbs : ℤ) = Fz u a := by
  rcases Int.natAbs_eq a with ha | ha
  · exact (congrArg (Fz u) ha).symm
  · rw [show ((a.natAbs : ℤ)) = -a by omega, Fz_neg]

theorem xfun_mul_Fz_int_eq_tent (hu0 : u ≠ 0) (hu1 : u ≠ 1) (a : ℤ) :
    xfun u * Fz u a = tent u a.natAbs := by
  rw [← Fz_natAbs u a]
  exact xfun_mul_Fz_eq_tent hu0 hu1 a.natAbs

end Tent

section Bridges

open FLT.DivisorConvolution

variable {K : Type*} [NontriviallyNormedField K]

theorem cauchyMulInt_a4x_eq_neg_sum_Sols (u : K) (N : ℕ) :
    cauchyMulInt a₄Coeff (xCoeffFull u) N
      = -(∑ x ∈ Sols N, ((5 * x.1 ^ 3 : ℕ) : K) * xDivTerm u x.2.2.1) := by
  have hc : ∀ i, 0 < i → a₄Coeff (K := K) i = ∑ a ∈ i.divisors, -((5 * a ^ 3 : ℕ) : K) := by
    intro i hi
    rw [a₄Coeff_of_pos hi, ← Finset.sum_neg_distrib]
  have hd : ∀ i, 0 < i → xCoeffFull u i = ∑ a ∈ i.divisors, xDivTerm u a := by
    intro i hi
    rw [xCoeffFull_of_pos u hi, xCoeff]
  rw [cauchyMulInt_eq_sum_Sols N hc hd, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem cauchyMulInt3_x_eq_sum (u : K) (N : ℕ) :
    cauchyMulInt3 (xCoeffFull u) N
      = ∑ i ∈ Finset.Ico 1 N, xCoeff u i *
          ∑ x ∈ Sols (N - i), xDivTerm u x.1 * xDivTerm u x.2.2.1 := by
  rw [cauchyMulInt3]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_Ico] at hi
  rw [xCoeffFull_of_pos u (by omega), cauchyMulInt_xx_eq_sum_Sols]

end Bridges

section XfunElimination

open FLT.DivisorConvolution

variable {K : Type*} [NontriviallyNormedField K] {u : K}

theorem xfun_mul_xDivTerm_mul_xDivTerm (hu0 : u ≠ 0) (hu1 : u ≠ 1) (a c : ℕ) :
    xfun u * (xDivTerm u a * xDivTerm u c)
      = (a : K) * (c : K) *
          (tent u (a + c) + tent u ((a : ℤ) - c).natAbs - 2 * tent u a - 2 * tent u c) := by
  have hprod := Fz_mul_Fz (u := u) hu0 (a : ℤ) (c : ℤ)
  have ht1 : xfun u * Fz u ((a : ℤ) + c) = tent u (a + c) := by
    rw [show ((a : ℤ) + c) = ((a + c : ℕ) : ℤ) by push_cast; ring]
    exact xfun_mul_Fz_eq_tent hu0 hu1 (a + c)
  have ht2 : xfun u * Fz u ((a : ℤ) - c) = tent u ((a : ℤ) - c).natAbs :=
    xfun_mul_Fz_int_eq_tent hu0 hu1 _
  have ht3 : xfun u * Fz u (a : ℤ) = tent u a := xfun_mul_Fz_eq_tent hu0 hu1 a
  have ht4 : xfun u * Fz u (c : ℤ) = tent u c := xfun_mul_Fz_eq_tent hu0 hu1 c
  calc xfun u * (xDivTerm u a * xDivTerm u c)
      = (a : K) * (c : K) * (xfun u * (Fz u (a : ℤ) * Fz u (c : ℤ))) := by
        rw [xDivTerm_eq_mul_Fz, xDivTerm_eq_mul_Fz]; ring
    _ = (a : K) * (c : K) *
          (xfun u * Fz u ((a : ℤ) + c) + xfun u * Fz u ((a : ℤ) - c)
            - 2 * (xfun u * Fz u (a : ℤ)) - 2 * (xfun u * Fz u (c : ℤ))) := by
        rw [hprod]; ring
    _ = _ := by rw [ht1, ht2, ht3, ht4]

theorem xfun_mul_cauchyMulInt_xx (hu0 : u ≠ 0) (hu1 : u ≠ 1) (N : ℕ) :
    xfun u * cauchyMulInt (xCoeffFull u) (xCoeffFull u) N
      = ∑ x ∈ Sols N, (x.1 : K) * (x.2.2.1 : K) *
          (tent u (x.1 + x.2.2.1) + tent u ((x.1 : ℤ) - x.2.2.1).natAbs
            - 2 * tent u x.1 - 2 * tent u x.2.2.1) := by
  rw [cauchyMulInt_xx_eq_sum_Sols, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => xfun_mul_xDivTerm_mul_xDivTerm hu0 hu1 _ _

end XfunElimination

section NormalForm

open FLT.DivisorConvolution

variable {K : Type*} [NontriviallyNormedField K] {u : K}

theorem defectCoeff_eq_interior_normal_form [CharZero K]
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) {N : ℕ} (hN : 0 < N) :
    defectCoeff u N
      = -(∑ d ∈ N.divisors, ∑ j ∈ Finset.Ico 1 d, ((boundaryWeight d j : ℕ) : K) * Fz u (j : ℤ))
        + (∑ x ∈ Sols N, yDivTerm u x.1 * yDivTerm u x.2.2.1)
        + (∑ x ∈ Sols N, xDivTerm u x.1 * yDivTerm u x.2.2.1)
        - 3 * (∑ x ∈ Sols N, (x.1 : K) * (x.2.2.1 : K) *
            (tent u (x.1 + x.2.2.1) + tent u ((x.1 : ℤ) - x.2.2.1).natAbs
              - 2 * tent u x.1 - 2 * tent u x.2.2.1))
        + (∑ x ∈ Sols N, ((5 * x.1 ^ 3 : ℕ) : K) * xDivTerm u x.2.2.1)
        - (∑ i ∈ Finset.Ico 1 N, xCoeff u i *
            ∑ x ∈ Sols (N - i), xDivTerm u x.1 * xDivTerm u x.2.2.1) := by
  have hyy := cauchyMulInt_yy_eq_sum_Sols u N
  have hxy := cauchyMulInt_xy_eq_sum_Sols u N
  have hxx := xfun_mul_cauchyMulInt_xx (u := u) hu0 hu1 N
  have ha4 := cauchyMulInt_a4x_eq_neg_sum_Sols u N
  have h3 := cauchyMulInt3_x_eq_sum u N
  rw [defectCoeff_eq_neg_sum_boundaryWeight_add_int hu0 hu1 hN]
  linear_combination hyy + hxy - 3 * hxx - ha4 - h3

end NormalForm

end TateCurve

open Finset

namespace TateCurve

open FLT.DivisorConvolution FLT.DivisorConvolution.BesgeCertificate

variable {K : Type*} [NontriviallyNormedField K] {u : K}

theorem four_mul_yy_add_two_xy_symm (hu : u ≠ 0) (a c : ℕ) :
    4 * (yDivTerm u a * yDivTerm u c)
        + 2 * (xDivTerm u a * yDivTerm u c) + 2 * (xDivTerm u c * yDivTerm u a)
      = ((a : K) ^ 2 * (c : K) ^ 2 - (a : K) * (c : K)) * Fz u ((a : ℤ) + (c : ℤ))
          - ((a : K) ^ 2 * (c : K) ^ 2 + (a : K) * (c : K)) * Fz u ((a : ℤ) - (c : ℤ))
          + 2 * ((a : K) * (c : K)) * Fz u (a : ℤ) + 2 * ((a : K) * (c : K)) * Fz u (c : ℤ) := by
  have hL : 4 * (yDivTerm u a * yDivTerm u c)
        + 2 * (xDivTerm u a * yDivTerm u c) + 2 * (xDivTerm u c * yDivTerm u a)
      = (2 * yDivTerm u a) * (2 * yDivTerm u c)
          + xDivTerm u a * (2 * yDivTerm u c) + xDivTerm u c * (2 * yDivTerm u a) := by
    ring
  rw [hL, two_mul_yDivTerm u a, two_mul_yDivTerm u c,
    xDivTerm_eq_mul_Fz u a, xDivTerm_eq_mul_Fz u c]
  linear_combination ((a : K) ^ 2 * (c : K) ^ 2) * Gz_mul_Gz (u := u) hu (a : ℤ) (c : ℤ)
    - ((a : K) * (c : K)) * Fz_mul_Fz (u := u) hu (a : ℤ) (c : ℤ)

theorem sum_Sols_swap₁ {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ × ℕ × ℕ × ℕ → M) :
    ∑ x ∈ Sols N, f x = ∑ x ∈ Sols N, f (swap₁ x) := by
  refine Finset.sum_nbij' swap₁ swap₁ ?_ ?_ ?_ ?_ ?_
  · intro x hx; exact swap₁_mem_Sols hx
  · intro x hx; exact swap₁_mem_Sols hx
  · intro x _; exact swap₁_swap₁ x
  · intro x _; exact swap₁_swap₁ x
  · intro x _; rfl

theorem four_mul_sum_Sols_yy_add_xy (hu : u ≠ 0) (N : ℕ) :
    4 * ((∑ x ∈ Sols N, yDivTerm u x.1 * yDivTerm u x.2.2.1)
          + ∑ x ∈ Sols N, xDivTerm u x.1 * yDivTerm u x.2.2.1)
      = ∑ x ∈ Sols N,
          (((x.1 : K) ^ 2 * (x.2.2.1 : K) ^ 2 - (x.1 : K) * (x.2.2.1 : K))
              * Fz u ((x.1 : ℤ) + (x.2.2.1 : ℤ))
            - ((x.1 : K) ^ 2 * (x.2.2.1 : K) ^ 2 + (x.1 : K) * (x.2.2.1 : K))
              * Fz u ((x.1 : ℤ) - (x.2.2.1 : ℤ))
            + 2 * ((x.1 : K) * (x.2.2.1 : K)) * Fz u (x.1 : ℤ)
            + 2 * ((x.1 : K) * (x.2.2.1 : K)) * Fz u (x.2.2.1 : ℤ)) := by

  have hswap : (∑ x ∈ Sols N, xDivTerm u x.1 * yDivTerm u x.2.2.1)
      = ∑ x ∈ Sols N, xDivTerm u x.2.2.1 * yDivTerm u x.1 := by
    simpa [swap₁] using sum_Sols_swap₁ N fun x => xDivTerm u x.1 * yDivTerm u x.2.2.1

  have hsplit : 4 * ((∑ x ∈ Sols N, yDivTerm u x.1 * yDivTerm u x.2.2.1)
        + ∑ x ∈ Sols N, xDivTerm u x.1 * yDivTerm u x.2.2.1)
      = ∑ x ∈ Sols N,
          (4 * (yDivTerm u x.1 * yDivTerm u x.2.2.1)
            + 2 * (xDivTerm u x.1 * yDivTerm u x.2.2.1)
            + 2 * (xDivTerm u x.2.2.1 * yDivTerm u x.1)) := by
    rw [show 4 * ((∑ x ∈ Sols N, yDivTerm u x.1 * yDivTerm u x.2.2.1)
            + ∑ x ∈ Sols N, xDivTerm u x.1 * yDivTerm u x.2.2.1)
        = 4 * (∑ x ∈ Sols N, yDivTerm u x.1 * yDivTerm u x.2.2.1)
            + 2 * (∑ x ∈ Sols N, xDivTerm u x.1 * yDivTerm u x.2.2.1)
            + 2 * (∑ x ∈ Sols N, xDivTerm u x.1 * yDivTerm u x.2.2.1) by ring]
    nth_rewrite 2 [hswap]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
  rw [hsplit]
  exact Finset.sum_congr rfl fun x _ => four_mul_yy_add_two_xy_symm hu x.1 x.2.2.1

end TateCurve

open Finset

namespace TateCurve

open FLT.DivisorConvolution FLT.DivisorConvolution.BesgeCertificate
  FLT.DivisorConvolution.Weight6Certificate

section TentClosedForm

variable {K : Type*} [NontriviallyNormedField K] {u : K}

theorem tent_eq_sq_add_sum [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (m : ℕ) :
    tent u m = (m : K) ^ 2 + ∑ j ∈ Finset.range m, ((m - j : ℕ) : K) * Fz u (j : ℤ) := by
  have h1u : (1 : K) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  have hu1' : u - 1 ≠ 0 := sub_ne_zero.mpr hu1
  have hui1 : u⁻¹ ≠ 1 := fun h => hu1 (by rwa [inv_eq_one] at h)
  have hui1' : u⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr hui1
  have hzm : u ^ m ≠ 0 := pow_ne_zero m hu0
  have h2 : (2 : K) ≠ 0 := by norm_num
  have h12 : (12 : K) ≠ 0 := by norm_num

  have hsplit : ∑ j ∈ Finset.range m, ((m - j : ℕ) : K) * Fz u (j : ℤ)
      = (∑ j ∈ Finset.range m,
            ((m : K) + (-1) * (j : K) + 0 * (j : K) ^ 2 + 0 * (j : K) ^ 3) * u ^ j)
        + (∑ j ∈ Finset.range m,
            ((m : K) + (-1) * (j : K) + 0 * (j : K) ^ 2 + 0 * (j : K) ^ 3) * u⁻¹ ^ j)
        + (-2) * (∑ j ∈ Finset.range m,
            ((m : K) + (-1) * (j : K) + 0 * (j : K) ^ 2 + 0 * (j : K) ^ 3)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [Fz_natCast, Nat.cast_sub hj.le]
    ring
  have hA := sum_cubic_geom_eq_div (K := K) (m : K) (-1) 0 0 hu1 m
  have hB := sum_cubic_geom_eq_div (K := K) (m : K) (-1) 0 0 hui1 m
  have hC := sum_cubic_eq_div (K := K) (m : K) (-1) 0 0 m

  rw [← xfun_mul_Fz_eq_tent hu0 hu1 m, hsplit, hA, hB, hC, Fz_natCast]
  simp only [xfun, inv_pow]
  field_simp
  ring

theorem tent_eq_sq_add_sum_Ico [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (m : ℕ) :
    tent u m = (m : K) ^ 2 + ∑ j ∈ Finset.Ico 1 m, ((m - j : ℕ) : K) * Fz u (j : ℤ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [tent]
  · rw [tent_eq_sq_add_sum hu0 hu1 m]
    congr 1
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hm]
    simp

end TentClosedForm

section SupportBound

theorem add_le_of_mem_Sols {N : ℕ} {x : ℕ × ℕ × ℕ × ℕ} (hx : x ∈ Sols N) :
    x.1 + x.2.2.1 ≤ N := by
  obtain ⟨ha, hb, hc, he, heq⟩ := mem_Sols.mp hx
  have h1 : x.1 ≤ x.1 * x.2.1 := Nat.le_mul_of_pos_right x.1 hb
  have h2 : x.2.2.1 ≤ x.2.2.1 * x.2.2.2 := Nat.le_mul_of_pos_right x.2.2.1 he
  omega

theorem eq_one_of_mem_Sols_add_eq {N : ℕ} {x : ℕ × ℕ × ℕ × ℕ} (hx : x ∈ Sols N)
    (hsum : x.1 + x.2.2.1 = N) : x.2.1 = 1 ∧ x.2.2.2 = 1 := by
  obtain ⟨ha, hb, hc, he, heq⟩ := mem_Sols.mp hx
  constructor
  · by_contra hb1
    have hb2 : 2 ≤ x.2.1 := by omega
    have h1 : x.1 * 2 ≤ x.1 * x.2.1 := Nat.mul_le_mul_left x.1 hb2
    have h2 : x.2.2.1 ≤ x.2.2.1 * x.2.2.2 := Nat.le_mul_of_pos_right x.2.2.1 he
    omega
  · by_contra he1
    have he2 : 2 ≤ x.2.2.2 := by omega
    have h1 : x.1 ≤ x.1 * x.2.1 := Nat.le_mul_of_pos_right x.1 hb
    have h2 : x.2.2.1 * 2 ≤ x.2.2.1 * x.2.2.2 := Nat.mul_le_mul_left x.2.2.1 he2
    omega

theorem eq_of_mem_Sols_add_eq {N : ℕ} {x : ℕ × ℕ × ℕ × ℕ} (hx : x ∈ Sols N)
    (hsum : x.1 + x.2.2.1 = N) : x = (x.1, 1, N - x.1, 1) := by
  obtain ⟨hb, he⟩ := eq_one_of_mem_Sols_add_eq hx hsum
  obtain ⟨a, b, c, e⟩ := x
  simp only at hb he hsum ⊢
  subst hb he
  have : c = N - a := by omega
  subst this
  rfl

theorem sum_Sols_filter_add_eq_top {M : Type*} [AddCommMonoid M] (N : ℕ)
    (f : ℕ × ℕ × ℕ × ℕ → M) :
    ∑ x ∈ (Sols N).filter (fun x => x.1 + x.2.2.1 = N), f x
      = ∑ a ∈ Finset.Ico 1 N, f (a, 1, N - a, 1) := by
  refine Finset.sum_nbij' (fun x => x.1) (fun a => (a, 1, N - a, 1)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hmem, hsum⟩ := hx
    have hsum' : x.1 + x.2.2.1 = N := hsum
    obtain ⟨ha, _, hc, _, _⟩ := mem_Sols.mp hmem
    simp only [Finset.mem_Ico]
    omega
  · intro a ha
    rw [Finset.mem_Ico] at ha
    rw [Finset.mem_filter, mem_Sols]
    dsimp only
    exact ⟨⟨ha.1, one_pos, by omega, one_pos, by omega⟩, by omega⟩
  · intro x hx
    rw [Finset.mem_filter] at hx
    exact (eq_of_mem_Sols_add_eq hx.1 hx.2).symm
  · intro a _
    rfl
  · intro x hx
    rw [Finset.mem_filter] at hx
    exact congrArg f (eq_of_mem_Sols_add_eq hx.1 hx.2)

end SupportBound

section TopLine

theorem sum_top_line (N : ℕ) :
    ∑ a ∈ Finset.Ico 1 N, ((a : ℤ) ^ 2 * ((N : ℤ) - a) ^ 2 - (a : ℤ) * ((N : ℤ) - a))
      = 4 * ∑ i ∈ Finset.Ico 1 N, (i : ℤ) *
          ∑ a ∈ Finset.Ico 1 (N - i), ((a : ℤ) * (((N - i : ℕ) : ℤ) - a)) := by
  apply mul_left_cancel₀ (by norm_num : (90 : ℤ) ≠ 0)

  have h1 := thirty_mul_sum_Ico_sq_mul_sq_rev N
  have h2 := six_mul_sum_Ico_mul_rev N
  have h3 := sixty_mul_sum_Ico_mul_cube_rev N

  have h4 : ∑ a ∈ Finset.Ico 1 N, ((a : ℤ) ^ 2 * ((N : ℤ) - a) ^ 2 - (a : ℤ) * ((N : ℤ) - a))
      = (∑ a ∈ Finset.Ico 1 N, (a : ℤ) ^ 2 * ((N : ℤ) - a) ^ 2)
        - ∑ a ∈ Finset.Ico 1 N, (a : ℤ) * ((N : ℤ) - a) := by
    rw [Finset.sum_sub_distrib]

  have h6 : ∑ i ∈ Finset.Ico 1 N, (i : ℤ) *
        (6 * ∑ a ∈ Finset.Ico 1 (N - i), ((a : ℤ) * (((N - i : ℕ) : ℤ) - a)))
      = ∑ i ∈ Finset.Ico 1 N, ((i : ℤ) * ((N : ℤ) - i) ^ 3 - (i : ℤ) * ((N : ℤ) - i)) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiN : i ≤ N := (Finset.mem_Ico.mp hi).2.le
    rw [six_mul_sum_Ico_mul_rev (N - i), Nat.cast_sub hiN]
    ring

  have h7 : ∑ i ∈ Finset.Ico 1 N, (i : ℤ) *
        (6 * ∑ a ∈ Finset.Ico 1 (N - i), ((a : ℤ) * (((N - i : ℕ) : ℤ) - a)))
      = 6 * ∑ i ∈ Finset.Ico 1 N, (i : ℤ) *
          ∑ a ∈ Finset.Ico 1 (N - i), ((a : ℤ) * (((N - i : ℕ) : ℤ) - a)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

  have h5 : ∑ i ∈ Finset.Ico 1 N, ((i : ℤ) * ((N : ℤ) - i) ^ 3 - (i : ℤ) * ((N : ℤ) - i))
      = (∑ i ∈ Finset.Ico 1 N, (i : ℤ) * ((N : ℤ) - i) ^ 3)
        - ∑ i ∈ Finset.Ico 1 N, (i : ℤ) * ((N : ℤ) - i) := by
    rw [Finset.sum_sub_distrib]
  linear_combination (90 : ℤ) * h4 + 3 * h1 - 5 * h2 + 60 * h7 - 60 * h6 - 60 * h5 - h3

theorem sum_top_line_Sols (N : ℕ) :
    ∑ x ∈ (Sols N).filter (fun x => x.1 + x.2.2.1 = N),
        ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2 - (x.1 : ℤ) * (x.2.2.1 : ℤ))
      = 4 * ∑ i ∈ Finset.Ico 1 N, (i : ℤ) *
          ∑ x ∈ (Sols (N - i)).filter (fun x => x.1 + x.2.2.1 = N - i),
            ((x.1 : ℤ) * (x.2.2.1 : ℤ)) := by

  rw [sum_Sols_filter_add_eq_top N
      (fun x => (x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2 - (x.1 : ℤ) * (x.2.2.1 : ℤ))]
  have hinner : ∀ i ∈ Finset.Ico 1 N,
      (∑ x ∈ (Sols (N - i)).filter (fun x => x.1 + x.2.2.1 = N - i),
          ((x.1 : ℤ) * (x.2.2.1 : ℤ)))
        = ∑ a ∈ Finset.Ico 1 (N - i), ((a : ℤ) * (((N - i : ℕ) : ℤ) - a)) := by
    intro i _
    rw [sum_Sols_filter_add_eq_top (N - i) (fun x => (x.1 : ℤ) * (x.2.2.1 : ℤ))]
    refine Finset.sum_congr rfl fun a ha => ?_
    have haN : a ≤ N - i := ((Finset.mem_Ico.mp ha).2).le
    simp only
    rw [Nat.cast_sub haN]

  have hL : ∑ a ∈ Finset.Ico 1 N,
        ((a : ℤ) ^ 2 * ((N - a : ℕ) : ℤ) ^ 2 - (a : ℤ) * ((N - a : ℕ) : ℤ))
      = ∑ a ∈ Finset.Ico 1 N, ((a : ℤ) ^ 2 * ((N : ℤ) - a) ^ 2 - (a : ℤ) * ((N : ℤ) - a)) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    have haN : a ≤ N := ((Finset.mem_Ico.mp ha).2).le
    rw [Nat.cast_sub haN]
  calc ∑ a ∈ Finset.Ico 1 N,
        ((((a, 1, N - a, 1) : ℕ × ℕ × ℕ × ℕ).1 : ℤ) ^ 2
            * (((a, 1, N - a, 1) : ℕ × ℕ × ℕ × ℕ).2.2.1 : ℤ) ^ 2
          - (((a, 1, N - a, 1) : ℕ × ℕ × ℕ × ℕ).1 : ℤ)
            * (((a, 1, N - a, 1) : ℕ × ℕ × ℕ × ℕ).2.2.1 : ℤ))
      = ∑ a ∈ Finset.Ico 1 N,
          ((a : ℤ) ^ 2 * ((N - a : ℕ) : ℤ) ^ 2 - (a : ℤ) * ((N - a : ℕ) : ℤ)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only
    _ = ∑ a ∈ Finset.Ico 1 N, ((a : ℤ) ^ 2 * ((N : ℤ) - a) ^ 2 - (a : ℤ) * ((N : ℤ) - a)) := hL
    _ = 4 * ∑ i ∈ Finset.Ico 1 N, (i : ℤ) *
          ∑ a ∈ Finset.Ico 1 (N - i), ((a : ℤ) * (((N - i : ℕ) : ℤ) - a)) := sum_top_line N
    _ = 4 * ∑ i ∈ Finset.Ico 1 N, (i : ℤ) *
          ∑ x ∈ (Sols (N - i)).filter (fun x => x.1 + x.2.2.1 = N - i),
            ((x.1 : ℤ) * (x.2.2.1 : ℤ)) := by
        congr 1
        exact (Finset.sum_congr rfl fun i hi => by rw [hinner i hi]).symm

end TopLine

end TateCurve

open Finset

namespace TateCurve

open FLT.DivisorConvolution

section Sols3

def Sols3 (N : ℕ) : Finset ((ℕ × ℕ) × ℕ × ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N) ×ˢ
      (Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 1 N)).filter
    (fun y => y.1.1 * y.1.2 + (y.2.1 * y.2.2.1 + y.2.2.2.1 * y.2.2.2.2) = N)

theorem mem_Sols3 {N : ℕ} {y : (ℕ × ℕ) × ℕ × ℕ × ℕ × ℕ} :
    y ∈ Sols3 N ↔
      0 < y.1.1 ∧ 0 < y.1.2 ∧ 0 < y.2.1 ∧ 0 < y.2.2.1 ∧ 0 < y.2.2.2.1 ∧ 0 < y.2.2.2.2 ∧
        y.1.1 * y.1.2 + (y.2.1 * y.2.2.1 + y.2.2.2.1 * y.2.2.2.2) = N := by
  constructor
  · intro h
    have heq := (Finset.mem_filter.1 h).2
    have hmem := (Finset.mem_filter.1 h).1
    have h1 := Finset.mem_product.1 hmem
    have h11 := Finset.mem_product.1 h1.1
    have h2 := Finset.mem_product.1 h1.2
    have h22 := Finset.mem_product.1 h2.2
    have h222 := Finset.mem_product.1 h22.2
    exact ⟨(Finset.mem_Icc.1 h11.1).1, (Finset.mem_Icc.1 h11.2).1, (Finset.mem_Icc.1 h2.1).1,
      (Finset.mem_Icc.1 h22.1).1, (Finset.mem_Icc.1 h222.1).1, (Finset.mem_Icc.1 h222.2).1, heq⟩
  · rintro ⟨hd, hf, ha, hb, hc, he, heq⟩
    have hdf_pos : 0 < y.1.1 * y.1.2 := Nat.mul_pos hd hf
    have hab_pos : 0 < y.2.1 * y.2.2.1 := Nat.mul_pos ha hb
    have hce_pos : 0 < y.2.2.2.1 * y.2.2.2.2 := Nat.mul_pos hc he
    have hdf_le : y.1.1 * y.1.2 ≤ N := by omega
    have hab_le : y.2.1 * y.2.2.1 ≤ N := by omega
    have hce_le : y.2.2.2.1 * y.2.2.2.2 ≤ N := by omega
    have hdN : y.1.1 ≤ N := le_trans (le_mul_of_one_le_right (Nat.zero_le _) hf) hdf_le
    have hfN : y.1.2 ≤ N := le_trans (le_mul_of_one_le_left (Nat.zero_le _) hd) hdf_le
    have haN : y.2.1 ≤ N := le_trans (le_mul_of_one_le_right (Nat.zero_le _) hb) hab_le
    have hbN : y.2.2.1 ≤ N := le_trans (le_mul_of_one_le_left (Nat.zero_le _) ha) hab_le
    have hcN : y.2.2.2.1 ≤ N := le_trans (le_mul_of_one_le_right (Nat.zero_le _) he) hce_le
    have heN : y.2.2.2.2 ≤ N := le_trans (le_mul_of_one_le_left (Nat.zero_le _) hc) hce_le
    refine Finset.mem_filter.2 ⟨?_, heq⟩
    refine Finset.mem_product.2 ⟨?_, ?_⟩
    · exact Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨hd, hdN⟩, Finset.mem_Icc.2 ⟨hf, hfN⟩⟩
    · refine Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨ha, haN⟩, ?_⟩
      refine Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨hb, hbN⟩, ?_⟩
      exact Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨hc, hcN⟩, Finset.mem_Icc.2 ⟨he, heN⟩⟩

theorem add_add_le_of_mem_Sols3 {N : ℕ} {y : (ℕ × ℕ) × ℕ × ℕ × ℕ × ℕ} (hy : y ∈ Sols3 N) :
    y.1.1 + y.2.1 + y.2.2.2.1 ≤ N := by
  obtain ⟨hd, hf, ha, hb, hc, he, heq⟩ := mem_Sols3.mp hy
  have h1 : y.1.1 ≤ y.1.1 * y.1.2 := Nat.le_mul_of_pos_right y.1.1 hf
  have h2 : y.2.1 ≤ y.2.1 * y.2.2.1 := Nat.le_mul_of_pos_right y.2.1 hb
  have h3 : y.2.2.2.1 ≤ y.2.2.2.1 * y.2.2.2.2 := Nat.le_mul_of_pos_right y.2.2.2.1 he
  omega

theorem mul_fst_mem_Ico_of_mem_Sols3 {N : ℕ} {y : (ℕ × ℕ) × ℕ × ℕ × ℕ × ℕ}
    (hy : y ∈ Sols3 N) : y.1.1 * y.1.2 ∈ Finset.Ico 1 N := by
  obtain ⟨hd, hf, ha, hb, hc, he, heq⟩ := mem_Sols3.mp hy
  have hdf_pos : 0 < y.1.1 * y.1.2 := Nat.mul_pos hd hf
  have hab_pos : 0 < y.2.1 * y.2.2.1 := Nat.mul_pos ha hb
  have hce_pos : 0 < y.2.2.2.1 * y.2.2.2.2 := Nat.mul_pos hc he
  rw [Finset.mem_Ico]
  omega

theorem sols3_filter_mul_fst_eq {N i : ℕ} (hi : i ∈ Finset.Ico 1 N) :
    (Sols3 N).filter (fun y => y.1.1 * y.1.2 = i)
      = i.divisorsAntidiagonal ×ˢ Sols (N - i) := by
  rw [Finset.mem_Ico] at hi
  have hi0 : i ≠ 0 := by omega
  ext y
  rw [Finset.mem_filter, Finset.mem_product, Nat.mem_divisorsAntidiagonal, mem_Sols3, mem_Sols]
  constructor
  · rintro ⟨⟨hd, hf, ha, hb, hc, he, heq⟩, hdf⟩
    exact ⟨⟨hdf, hi0⟩, ha, hb, hc, he, by omega⟩
  · rintro ⟨⟨hdf, -⟩, ha, hb, hc, he, heq⟩
    have hd : 0 < y.1.1 := Nat.pos_of_ne_zero (left_ne_zero_of_mul (hdf ▸ hi0))
    have hf : 0 < y.1.2 := Nat.pos_of_ne_zero (right_ne_zero_of_mul (hdf ▸ hi0))
    exact ⟨⟨hd, hf, ha, hb, hc, he, by omega⟩, hdf⟩

theorem sum_Sols3_eq_sum_fiber {M : Type*} [AddCommMonoid M] (N : ℕ)
    (φ : (ℕ × ℕ) × ℕ × ℕ × ℕ × ℕ → M) :
    ∑ y ∈ Sols3 N, φ y
      = ∑ i ∈ Finset.Ico 1 N, ∑ p ∈ i.divisorsAntidiagonal, ∑ x ∈ Sols (N - i), φ (p, x) := by
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.Ico 1 N)
    (fun y hy => mul_fst_mem_Ico_of_mem_Sols3 hy) φ]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [sols3_filter_mul_fst_eq hi, Finset.sum_product]

theorem sum_Ico_divisorSum_mul_sum_Sols {R : Type*} [CommSemiring R]
    (F : ℕ → R) (G : ℕ × ℕ × ℕ × ℕ → R) (N : ℕ) :
    ∑ i ∈ Finset.Ico 1 N, (∑ d ∈ i.divisors, F d) * ∑ x ∈ Sols (N - i), G x
      = ∑ y ∈ Sols3 N, F y.1.1 * G y.2 := by
  rw [sum_Sols3_eq_sum_fiber N (fun y => F y.1.1 * G y.2)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [show (∑ d ∈ i.divisors, F d) = ∑ p ∈ i.divisorsAntidiagonal, F p.1 from
      (Nat.sum_divisorsAntidiagonal (fun a _ => F a)).symm, Finset.sum_mul]
  exact Finset.sum_congr rfl fun p _ => Finset.mul_sum _ _ _

end Sols3

section TateTriple

variable {K : Type*} [NontriviallyNormedField K]

theorem triple_term_eq_sum_Sols3 (u : K) (N : ℕ) :
    ∑ i ∈ Finset.Ico 1 N, xCoeff u i * ∑ x ∈ Sols (N - i), xDivTerm u x.1 * xDivTerm u x.2.2.1
      = ∑ y ∈ Sols3 N, xDivTerm u y.1.1 * (xDivTerm u y.2.1 * xDivTerm u y.2.2.2.1) := by
  rw [← sum_Ico_divisorSum_mul_sum_Sols (xDivTerm u)
    (fun x => xDivTerm u x.1 * xDivTerm u x.2.2.1) N]
  exact Finset.sum_congr rfl fun i _ => by rw [xCoeff]

theorem cauchyMulInt3_x_eq_sum_Sols3 [IsUltrametricDist K] (u : K) (N : ℕ) :
    cauchyMulInt3 (xCoeffFull u) N
      = ∑ y ∈ Sols3 N, xDivTerm u y.1.1 * (xDivTerm u y.2.1 * xDivTerm u y.2.2.2.1) := by
  rw [cauchyMulInt3_x_eq_sum, triple_term_eq_sum_Sols3]

end TateTriple

section NormalForm

variable {K : Type*} [NontriviallyNormedField K] {u : K}

theorem defectCoeff_eq_sols3_normal_form [CharZero K]
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) {N : ℕ} (hN : 0 < N) :
    defectCoeff u N
      = -(∑ d ∈ N.divisors, ∑ j ∈ Finset.Ico 1 d, ((boundaryWeight d j : ℕ) : K) * Fz u (j : ℤ))
        + (∑ x ∈ Sols N, yDivTerm u x.1 * yDivTerm u x.2.2.1)
        + (∑ x ∈ Sols N, xDivTerm u x.1 * yDivTerm u x.2.2.1)
        - 3 * (∑ x ∈ Sols N, (x.1 : K) * (x.2.2.1 : K) *
            (tent u (x.1 + x.2.2.1) + tent u ((x.1 : ℤ) - x.2.2.1).natAbs
              - 2 * tent u x.1 - 2 * tent u x.2.2.1))
        + (∑ x ∈ Sols N, ((5 * x.1 ^ 3 : ℕ) : K) * xDivTerm u x.2.2.1)
        - (∑ y ∈ Sols3 N, xDivTerm u y.1.1 * (xDivTerm u y.2.1 * xDivTerm u y.2.2.2.1)) := by
  rw [defectCoeff_eq_interior_normal_form hu0 hu1 hN, triple_term_eq_sum_Sols3]

end NormalForm

end TateCurve

open Finset

namespace TateCurve

open FLT.DivisorConvolution

section LineDefs

def boundaryLine (N k : ℕ) : ℤ :=
  ∑ d ∈ N.divisors.filter (fun d => k < d), (boundaryWeight d k : ℤ)

def mixedLine (N k : ℕ) : ℤ :=
  (∑ x ∈ (Sols N).filter (fun x => x.1 + x.2.2.1 = k),
      ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2 - (x.1 : ℤ) * (x.2.2.1 : ℤ)))
    - (∑ x ∈ (Sols N).filter (fun x => ((x.1 : ℤ) - (x.2.2.1 : ℤ)).natAbs = k),
        ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2 + (x.1 : ℤ) * (x.2.2.1 : ℤ)))
    + (∑ x ∈ (Sols N).filter (fun x => x.1 = k), 2 * ((x.1 : ℤ) * (x.2.2.1 : ℤ)))
    + (∑ x ∈ (Sols N).filter (fun x => x.2.2.1 = k), 2 * ((x.1 : ℤ) * (x.2.2.1 : ℤ)))

def tentWeight (a c k : ℕ) : ℤ :=
  (a : ℤ) * (c : ℤ) *
    (((a + c - k : ℕ) : ℤ) + ((((a : ℤ) - (c : ℤ)).natAbs - k : ℕ) : ℤ)
      - 2 * ((a - k : ℕ) : ℤ) - 2 * ((c - k : ℕ) : ℤ))

def tentLine (N k : ℕ) : ℤ := ∑ x ∈ Sols N, tentWeight x.1 x.2.2.1 k

def sFiveLine (N k : ℕ) : ℤ :=
  ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 = k), 5 * (x.1 : ℤ) ^ 3 * (x.2.2.1 : ℤ)

def tripleLine (N k : ℕ) : ℤ :=
  (∑ y ∈ (Sols3 N).filter
      (fun y => ((y.1.1 : ℤ) + ((y.2.1 : ℤ) + (y.2.2.2.1 : ℤ))).natAbs = k),
      ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))
    + (∑ y ∈ (Sols3 N).filter
        (fun y => ((y.1.1 : ℤ) - ((y.2.1 : ℤ) + (y.2.2.2.1 : ℤ))).natAbs = k),
        ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))
    + (∑ y ∈ (Sols3 N).filter
        (fun y => ((y.1.1 : ℤ) + ((y.2.1 : ℤ) - (y.2.2.2.1 : ℤ))).natAbs = k),
        ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))
    + (∑ y ∈ (Sols3 N).filter
        (fun y => ((y.1.1 : ℤ) - ((y.2.1 : ℤ) - (y.2.2.2.1 : ℤ))).natAbs = k),
        ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))
    - (∑ y ∈ (Sols3 N).filter
        (fun y => ((y.2.1 : ℤ) + (y.2.2.2.1 : ℤ)).natAbs = k),
        2 * ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))
    - (∑ y ∈ (Sols3 N).filter
        (fun y => ((y.2.1 : ℤ) - (y.2.2.2.1 : ℤ)).natAbs = k),
        2 * ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))
    - (∑ y ∈ (Sols3 N).filter
        (fun y => ((y.1.1 : ℤ) + (y.2.1 : ℤ)).natAbs = k),
        2 * ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))
    - (∑ y ∈ (Sols3 N).filter
        (fun y => ((y.1.1 : ℤ) - (y.2.1 : ℤ)).natAbs = k),
        2 * ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))
    - (∑ y ∈ (Sols3 N).filter
        (fun y => ((y.1.1 : ℤ) + (y.2.2.2.1 : ℤ)).natAbs = k),
        2 * ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))
    - (∑ y ∈ (Sols3 N).filter
        (fun y => ((y.1.1 : ℤ) - (y.2.2.2.1 : ℤ)).natAbs = k),
        2 * ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))
    + (∑ y ∈ (Sols3 N).filter (fun y => ((y.1.1 : ℤ)).natAbs = k),
        4 * ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))
    + (∑ y ∈ (Sols3 N).filter (fun y => ((y.2.1 : ℤ)).natAbs = k),
        4 * ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))
    + (∑ y ∈ (Sols3 N).filter (fun y => ((y.2.2.2.1 : ℤ)).natAbs = k),
        4 * ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))

def lineCoeff (N k : ℕ) : ℤ :=
  -4 * boundaryLine N k + mixedLine N k - 12 * tentLine N k + 4 * sFiveLine N k
    - 4 * tripleLine N k

end LineDefs

section Collapse

variable {K : Type*} [NontriviallyNormedField K] {u : K}

theorem sum_mul_Fz_eq_sum_lines_nat {α : Type*} (S : Finset α) (w : α → K) (g : α → ℕ) {N : ℕ}
    (hg : ∀ x ∈ S, g x ≤ N) :
    ∑ x ∈ S, w x * Fz u (g x : ℤ)
      = ∑ k ∈ Finset.Icc 1 N, (∑ x ∈ S.filter (fun x => g x = k), w x) * Fz u (k : ℤ) := by
  have hmaps : ∀ x ∈ S, g x ∈ Finset.range (N + 1) := fun x hx =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hg x hx))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => w x * Fz u (g x : ℤ))]
  have hsplit : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext m
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have h0 : ∑ x ∈ S.filter (fun x => g x = 0), w x * Fz u (g x : ℤ) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [(Finset.mem_filter.mp hx).2]
    simp
  rw [h0, zero_add]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.mp hx).2]

theorem sum_mul_Fz_eq_sum_lines_int {α : Type*} (S : Finset α) (w : α → K) (g : α → ℤ) {N : ℕ}
    (hg : ∀ x ∈ S, (g x).natAbs ≤ N) :
    ∑ x ∈ S, w x * Fz u (g x)
      = ∑ k ∈ Finset.Icc 1 N,
          (∑ x ∈ S.filter (fun x => (g x).natAbs = k), w x) * Fz u (k : ℤ) := by
  have h : ∀ x ∈ S, w x * Fz u (g x) = w x * Fz u ((g x).natAbs : ℤ) := fun x _ => by
    rw [Fz_natAbs]
  rw [Finset.sum_congr rfl h]
  exact sum_mul_Fz_eq_sum_lines_nat S w (fun x => (g x).natAbs) hg

end Collapse

section BoundarySource

variable {K : Type*} [NontriviallyNormedField K] {u : K}

theorem boundary_eq_sum_lines {N : ℕ} (hN : 0 < N) :
    (∑ d ∈ N.divisors, ∑ j ∈ Finset.Ico 1 d, ((boundaryWeight d j : ℕ) : K) * Fz u (j : ℤ))
      = ∑ k ∈ Finset.Icc 1 N, ((boundaryLine N k : ℤ) : K) * Fz u (k : ℤ) := by
  have hd_le : ∀ d ∈ N.divisors, d ≤ N := fun d hd =>
    Nat.le_of_dvd hN (Nat.mem_divisors.mp hd).1
  have hext : ∀ d ∈ N.divisors,
      (∑ j ∈ Finset.Ico 1 d, ((boundaryWeight d j : ℕ) : K) * Fz u (j : ℤ))
        = ∑ k ∈ Finset.Icc 1 N,
            (if k < d then ((boundaryWeight d k : ℕ) : K) * Fz u (k : ℤ) else 0) := by
    intro d hd
    have h1 : Finset.Ico 1 d = (Finset.Icc 1 N).filter (fun k => k < d) := by
      ext j
      simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_Icc]
      have := hd_le d hd
      omega
    rw [h1, Finset.sum_filter]
  rw [Finset.sum_congr rfl hext, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← Finset.sum_filter, ← Finset.sum_mul]
  congr 1
  rw [boundaryLine]
  push_cast
  rfl

end BoundarySource

section MixedSource

variable {K : Type*} [NontriviallyNormedField K] {u : K}

theorem mixed_eq_sum_lines (N : ℕ) :
    (∑ x ∈ Sols N,
        (((x.1 : K) ^ 2 * (x.2.2.1 : K) ^ 2 - (x.1 : K) * (x.2.2.1 : K))
            * Fz u ((x.1 : ℤ) + (x.2.2.1 : ℤ))
          - ((x.1 : K) ^ 2 * (x.2.2.1 : K) ^ 2 + (x.1 : K) * (x.2.2.1 : K))
            * Fz u ((x.1 : ℤ) - (x.2.2.1 : ℤ))
          + 2 * ((x.1 : K) * (x.2.2.1 : K)) * Fz u (x.1 : ℤ)
          + 2 * ((x.1 : K) * (x.2.2.1 : K)) * Fz u (x.2.2.1 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 N, ((mixedLine N k : ℤ) : K) * Fz u (k : ℤ) := by

  have hconv : ∀ x ∈ Sols N,
      (((x.1 : K) ^ 2 * (x.2.2.1 : K) ^ 2 - (x.1 : K) * (x.2.2.1 : K))
            * Fz u ((x.1 : ℤ) + (x.2.2.1 : ℤ))
          - ((x.1 : K) ^ 2 * (x.2.2.1 : K) ^ 2 + (x.1 : K) * (x.2.2.1 : K))
            * Fz u ((x.1 : ℤ) - (x.2.2.1 : ℤ))
          + 2 * ((x.1 : K) * (x.2.2.1 : K)) * Fz u (x.1 : ℤ)
          + 2 * ((x.1 : K) * (x.2.2.1 : K)) * Fz u (x.2.2.1 : ℤ))
        = (((x.1 : K) ^ 2 * (x.2.2.1 : K) ^ 2 - (x.1 : K) * (x.2.2.1 : K))
            * Fz u ((x.1 + x.2.2.1 : ℕ) : ℤ)
          - ((x.1 : K) ^ 2 * (x.2.2.1 : K) ^ 2 + (x.1 : K) * (x.2.2.1 : K))
            * Fz u ((x.1 : ℤ) - (x.2.2.1 : ℤ))
          + 2 * ((x.1 : K) * (x.2.2.1 : K)) * Fz u (x.1 : ℤ)
          + 2 * ((x.1 : K) * (x.2.2.1 : K)) * Fz u (x.2.2.1 : ℤ)) := by
    intro x _
    have : ((x.1 + x.2.2.1 : ℕ) : ℤ) = (x.1 : ℤ) + (x.2.2.1 : ℤ) := by push_cast; ring
    rw [this]
  rw [Finset.sum_congr rfl hconv]

  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

  have hb : ∀ x ∈ Sols N, x.1 + x.2.2.1 ≤ N := fun x hx => add_le_of_mem_Sols hx
  have hf1 : (∑ x ∈ Sols N,
        ((x.1 : K) ^ 2 * (x.2.2.1 : K) ^ 2 - (x.1 : K) * (x.2.2.1 : K))
          * Fz u ((x.1 + x.2.2.1 : ℕ) : ℤ))
      = ∑ k ∈ Finset.Icc 1 N,
          (∑ x ∈ (Sols N).filter (fun x => x.1 + x.2.2.1 = k),
            ((x.1 : K) ^ 2 * (x.2.2.1 : K) ^ 2 - (x.1 : K) * (x.2.2.1 : K))) * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_nat (Sols N) _ (fun x => x.1 + x.2.2.1) hb
  have hf2 : (∑ x ∈ Sols N,
        ((x.1 : K) ^ 2 * (x.2.2.1 : K) ^ 2 + (x.1 : K) * (x.2.2.1 : K))
          * Fz u ((x.1 : ℤ) - (x.2.2.1 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 N,
          (∑ x ∈ (Sols N).filter (fun x => ((x.1 : ℤ) - (x.2.2.1 : ℤ)).natAbs = k),
            ((x.1 : K) ^ 2 * (x.2.2.1 : K) ^ 2 + (x.1 : K) * (x.2.2.1 : K))) * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int (Sols N) _ (fun x => (x.1 : ℤ) - (x.2.2.1 : ℤ))
      (fun x hx => by have := add_le_of_mem_Sols hx; omega)
  have hf3 : (∑ x ∈ Sols N, 2 * ((x.1 : K) * (x.2.2.1 : K)) * Fz u (x.1 : ℤ))
      = ∑ k ∈ Finset.Icc 1 N,
          (∑ x ∈ (Sols N).filter (fun x => x.1 = k),
            2 * ((x.1 : K) * (x.2.2.1 : K))) * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_nat (Sols N) _ (fun x => x.1)
      (fun x hx => by have := add_le_of_mem_Sols hx; omega)
  have hf4 : (∑ x ∈ Sols N, 2 * ((x.1 : K) * (x.2.2.1 : K)) * Fz u (x.2.2.1 : ℤ))
      = ∑ k ∈ Finset.Icc 1 N,
          (∑ x ∈ (Sols N).filter (fun x => x.2.2.1 = k),
            2 * ((x.1 : K) * (x.2.2.1 : K))) * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_nat (Sols N) _ (fun x => x.2.2.1)
      (fun x hx => by have := add_le_of_mem_Sols hx; omega)
  rw [hf1, hf2, hf3, hf4]

  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [mixedLine]
  push_cast
  ring

end MixedSource

section TentSource

variable {K : Type*} [NontriviallyNormedField K] {u : K}

theorem tent_eq_sq_add_sum_Icc [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) {m N : ℕ} (hm : m ≤ N) :
    tent u m = (m : K) ^ 2 + ∑ k ∈ Finset.Icc 1 N, ((m - k : ℕ) : K) * Fz u (k : ℤ) := by
  rw [tent_eq_sq_add_sum_Ico hu0 hu1 m]
  congr 1
  refine Finset.sum_subset ?_ ?_
  · intro j hj
    rw [Finset.mem_Ico] at hj
    rw [Finset.mem_Icc]
    omega
  · intro j hj hj'
    rw [Finset.mem_Icc] at hj
    rw [Finset.mem_Ico] at hj'
    have hmj : m - j = 0 := by omega
    rw [hmj]
    simp

theorem sum_sub_mul_Fz_eq_tent [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) {m N : ℕ} (hm : m ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, ((m - k : ℕ) : K) * Fz u (k : ℤ) = tent u m - (m : K) ^ 2 := by
  rw [tent_eq_sq_add_sum_Icc hu0 hu1 hm]
  ring

theorem tent_point_eq_sum_lines [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) {a c N : ℕ}
    (hac : a + c ≤ N) :
    (a : K) * (c : K) *
        (tent u (a + c) + tent u ((a : ℤ) - (c : ℤ)).natAbs - 2 * tent u a - 2 * tent u c)
      = ∑ k ∈ Finset.Icc 1 N, ((tentWeight a c k : ℤ) : K) * Fz u (k : ℤ) := by
  have h1 : a ≤ N := by omega
  have h2 : c ≤ N := by omega
  have h3 : ((a : ℤ) - (c : ℤ)).natAbs ≤ N := by omega

  have habs : ((((a : ℤ) - (c : ℤ)).natAbs : ℕ) : K) ^ 2 = ((a : K) - (c : K)) ^ 2 := by
    have hZ : ((((a : ℤ) - (c : ℤ)).natAbs : ℕ) : ℤ) ^ 2 = ((a : ℤ) - (c : ℤ)) ^ 2 := by
      rcases Int.natAbs_eq ((a : ℤ) - (c : ℤ)) with h | h
      · nth_rewrite 2 [h]
        ring
      · nth_rewrite 2 [h]
        ring
    have h1 : ((((a : ℤ) - (c : ℤ)).natAbs : ℕ) : K)
        = (((((a : ℤ) - (c : ℤ)).natAbs : ℕ) : ℤ) : K) := (Int.cast_natCast _).symm
    rw [h1, ← Int.cast_pow, hZ, Int.cast_pow, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]

  have hpt : ∀ k ∈ Finset.Icc 1 N, ((tentWeight a c k : ℤ) : K) * Fz u (k : ℤ)
      = ((a : K) * (c : K)) * (((a + c - k : ℕ) : K) * Fz u (k : ℤ))
        + ((a : K) * (c : K)) * (((((a : ℤ) - (c : ℤ)).natAbs - k : ℕ) : K) * Fz u (k : ℤ))
        - 2 * ((a : K) * (c : K)) * (((a - k : ℕ) : K) * Fz u (k : ℤ))
        - 2 * ((a : K) * (c : K)) * (((c - k : ℕ) : K) * Fz u (k : ℤ)) := by
    intro k _
    rw [tentWeight]
    push_cast
    ring
  rw [Finset.sum_congr rfl hpt]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_sub_mul_Fz_eq_tent hu0 hu1 hac, sum_sub_mul_Fz_eq_tent hu0 hu1 h3,
    sum_sub_mul_Fz_eq_tent hu0 hu1 h1, sum_sub_mul_Fz_eq_tent hu0 hu1 h2]
  push_cast
  linear_combination ((a : K) * (c : K)) * habs

theorem tent_eq_sum_lines [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (N : ℕ) :
    (∑ x ∈ Sols N, (x.1 : K) * (x.2.2.1 : K) *
        (tent u (x.1 + x.2.2.1) + tent u ((x.1 : ℤ) - x.2.2.1).natAbs
          - 2 * tent u x.1 - 2 * tent u x.2.2.1))
      = ∑ k ∈ Finset.Icc 1 N, ((tentLine N k : ℤ) : K) * Fz u (k : ℤ) := by
  have hpt : ∀ x ∈ Sols N, (x.1 : K) * (x.2.2.1 : K) *
        (tent u (x.1 + x.2.2.1) + tent u ((x.1 : ℤ) - x.2.2.1).natAbs
          - 2 * tent u x.1 - 2 * tent u x.2.2.1)
      = ∑ k ∈ Finset.Icc 1 N, ((tentWeight x.1 x.2.2.1 k : ℤ) : K) * Fz u (k : ℤ) :=
    fun x hx => tent_point_eq_sum_lines hu0 hu1 (add_le_of_mem_Sols hx)
  rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← Finset.sum_mul]
  congr 1
  rw [tentLine]
  push_cast
  rfl

end TentSource

section SFiveSource

variable {K : Type*} [NontriviallyNormedField K] {u : K}

theorem sfive_eq_sum_lines (N : ℕ) :
    (∑ x ∈ Sols N, ((5 * x.1 ^ 3 : ℕ) : K) * xDivTerm u x.2.2.1)
      = ∑ k ∈ Finset.Icc 1 N, ((sFiveLine N k : ℤ) : K) * Fz u (k : ℤ) := by
  have hconv : ∀ x ∈ Sols N, ((5 * x.1 ^ 3 : ℕ) : K) * xDivTerm u x.2.2.1
      = (((5 * x.1 ^ 3 : ℕ) : K) * (x.2.2.1 : K)) * Fz u (x.2.2.1 : ℤ) := fun x _ => by
    rw [xDivTerm_eq_mul_Fz]
    ring
  rw [Finset.sum_congr rfl hconv,
    sum_mul_Fz_eq_sum_lines_nat (N := N) (Sols N) _ (fun x => x.2.2.1)
      (fun x hx => by have := add_le_of_mem_Sols hx; omega)]
  refine Finset.sum_congr rfl fun k hk => ?_
  congr 1
  rw [sFiveLine]
  push_cast
  exact Finset.sum_congr rfl fun x _ => by ring

end SFiveSource

section TripleSource

variable {K : Type*} [NontriviallyNormedField K] {u : K}

theorem xDivTerm_triple_expand (hu0 : u ≠ 0) (d a c : ℕ) :
    xDivTerm u d * (xDivTerm u a * xDivTerm u c)
      = (d : K) * (a : K) * (c : K) * Fz u ((d : ℤ) + ((a : ℤ) + (c : ℤ)))
        + (d : K) * (a : K) * (c : K) * Fz u ((d : ℤ) - ((a : ℤ) + (c : ℤ)))
        + (d : K) * (a : K) * (c : K) * Fz u ((d : ℤ) + ((a : ℤ) - (c : ℤ)))
        + (d : K) * (a : K) * (c : K) * Fz u ((d : ℤ) - ((a : ℤ) - (c : ℤ)))
        - 2 * ((d : K) * (a : K) * (c : K)) * Fz u ((a : ℤ) + (c : ℤ))
        - 2 * ((d : K) * (a : K) * (c : K)) * Fz u ((a : ℤ) - (c : ℤ))
        - 2 * ((d : K) * (a : K) * (c : K)) * Fz u ((d : ℤ) + (a : ℤ))
        - 2 * ((d : K) * (a : K) * (c : K)) * Fz u ((d : ℤ) - (a : ℤ))
        - 2 * ((d : K) * (a : K) * (c : K)) * Fz u ((d : ℤ) + (c : ℤ))
        - 2 * ((d : K) * (a : K) * (c : K)) * Fz u ((d : ℤ) - (c : ℤ))
        + 4 * ((d : K) * (a : K) * (c : K)) * Fz u (d : ℤ)
        + 4 * ((d : K) * (a : K) * (c : K)) * Fz u (a : ℤ)
        + 4 * ((d : K) * (a : K) * (c : K)) * Fz u (c : ℤ) := by
  rw [xDivTerm_eq_mul_Fz, xDivTerm_eq_mul_Fz, xDivTerm_eq_mul_Fz]
  linear_combination
    ((d : K) * Fz u (d : ℤ) * ((a : K) * (c : K))) * Fz_mul_Fz hu0 (a : ℤ) (c : ℤ)
      + ((d : K) * (a : K) * (c : K)) * Fz_mul_Fz hu0 (d : ℤ) ((a : ℤ) + (c : ℤ))
      + ((d : K) * (a : K) * (c : K)) * Fz_mul_Fz hu0 (d : ℤ) ((a : ℤ) - (c : ℤ))
      - 2 * ((d : K) * (a : K) * (c : K)) * Fz_mul_Fz hu0 (d : ℤ) (a : ℤ)
      - 2 * ((d : K) * (a : K) * (c : K)) * Fz_mul_Fz hu0 (d : ℤ) (c : ℤ)

theorem triple_eq_sum_lines (hu0 : u ≠ 0) (N : ℕ) :
    (∑ y ∈ Sols3 N, xDivTerm u y.1.1 * (xDivTerm u y.2.1 * xDivTerm u y.2.2.2.1))
      = ∑ k ∈ Finset.Icc 1 N, ((tripleLine N k : ℤ) : K) * Fz u (k : ℤ) := by

  rw [Finset.sum_congr rfl fun y (_ : y ∈ Sols3 N) =>
    xDivTerm_triple_expand hu0 y.1.1 y.2.1 y.2.2.2.1]

  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

  have hb : ∀ y ∈ Sols3 N, y.1.1 + y.2.1 + y.2.2.2.1 ≤ N := fun y hy =>
    add_add_le_of_mem_Sols3 hy

  have hw1 : (∑ y ∈ Sols3 N,
        (y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K)
          * Fz u ((y.1.1 : ℤ) + ((y.2.1 : ℤ) + (y.2.2.2.1 : ℤ))))
      = ∑ k ∈ Finset.Icc 1 N,
          (∑ y ∈ (Sols3 N).filter
              (fun y => ((y.1.1 : ℤ) + ((y.2.1 : ℤ) + (y.2.2.2.1 : ℤ))).natAbs = k),
            (y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K)) * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int (Sols3 N) _
      (fun y => (y.1.1 : ℤ) + ((y.2.1 : ℤ) + (y.2.2.2.1 : ℤ)))
      (fun y hy => by have := hb y hy; omega)
  have hw2 : (∑ y ∈ Sols3 N,
        (y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K)
          * Fz u ((y.1.1 : ℤ) - ((y.2.1 : ℤ) + (y.2.2.2.1 : ℤ))))
      = ∑ k ∈ Finset.Icc 1 N,
          (∑ y ∈ (Sols3 N).filter
              (fun y => ((y.1.1 : ℤ) - ((y.2.1 : ℤ) + (y.2.2.2.1 : ℤ))).natAbs = k),
            (y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K)) * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int (Sols3 N) _
      (fun y => (y.1.1 : ℤ) - ((y.2.1 : ℤ) + (y.2.2.2.1 : ℤ)))
      (fun y hy => by have := hb y hy; omega)
  have hw3 : (∑ y ∈ Sols3 N,
        (y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K)
          * Fz u ((y.1.1 : ℤ) + ((y.2.1 : ℤ) - (y.2.2.2.1 : ℤ))))
      = ∑ k ∈ Finset.Icc 1 N,
          (∑ y ∈ (Sols3 N).filter
              (fun y => ((y.1.1 : ℤ) + ((y.2.1 : ℤ) - (y.2.2.2.1 : ℤ))).natAbs = k),
            (y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K)) * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int (Sols3 N) _
      (fun y => (y.1.1 : ℤ) + ((y.2.1 : ℤ) - (y.2.2.2.1 : ℤ)))
      (fun y hy => by have := hb y hy; omega)
  have hw4 : (∑ y ∈ Sols3 N,
        (y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K)
          * Fz u ((y.1.1 : ℤ) - ((y.2.1 : ℤ) - (y.2.2.2.1 : ℤ))))
      = ∑ k ∈ Finset.Icc 1 N,
          (∑ y ∈ (Sols3 N).filter
              (fun y => ((y.1.1 : ℤ) - ((y.2.1 : ℤ) - (y.2.2.2.1 : ℤ))).natAbs = k),
            (y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K)) * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int (Sols3 N) _
      (fun y => (y.1.1 : ℤ) - ((y.2.1 : ℤ) - (y.2.2.2.1 : ℤ)))
      (fun y hy => by have := hb y hy; omega)
  have hw5 : (∑ y ∈ Sols3 N,
        2 * ((y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K))
          * Fz u ((y.2.1 : ℤ) + (y.2.2.2.1 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 N,
          (∑ y ∈ (Sols3 N).filter
              (fun y => ((y.2.1 : ℤ) + (y.2.2.2.1 : ℤ)).natAbs = k),
            2 * ((y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K))) * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int (Sols3 N) _
      (fun y => (y.2.1 : ℤ) + (y.2.2.2.1 : ℤ))
      (fun y hy => by have := hb y hy; omega)
  have hw6 : (∑ y ∈ Sols3 N,
        2 * ((y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K))
          * Fz u ((y.2.1 : ℤ) - (y.2.2.2.1 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 N,
          (∑ y ∈ (Sols3 N).filter
              (fun y => ((y.2.1 : ℤ) - (y.2.2.2.1 : ℤ)).natAbs = k),
            2 * ((y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K))) * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int (Sols3 N) _
      (fun y => (y.2.1 : ℤ) - (y.2.2.2.1 : ℤ))
      (fun y hy => by have := hb y hy; omega)
  have hw7 : (∑ y ∈ Sols3 N,
        2 * ((y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K))
          * Fz u ((y.1.1 : ℤ) + (y.2.1 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 N,
          (∑ y ∈ (Sols3 N).filter
              (fun y => ((y.1.1 : ℤ) + (y.2.1 : ℤ)).natAbs = k),
            2 * ((y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K))) * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int (Sols3 N) _
      (fun y => (y.1.1 : ℤ) + (y.2.1 : ℤ))
      (fun y hy => by have := hb y hy; omega)
  have hw8 : (∑ y ∈ Sols3 N,
        2 * ((y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K))
          * Fz u ((y.1.1 : ℤ) - (y.2.1 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 N,
          (∑ y ∈ (Sols3 N).filter
              (fun y => ((y.1.1 : ℤ) - (y.2.1 : ℤ)).natAbs = k),
            2 * ((y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K))) * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int (Sols3 N) _
      (fun y => (y.1.1 : ℤ) - (y.2.1 : ℤ))
      (fun y hy => by have := hb y hy; omega)
  have hw9 : (∑ y ∈ Sols3 N,
        2 * ((y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K))
          * Fz u ((y.1.1 : ℤ) + (y.2.2.2.1 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 N,
          (∑ y ∈ (Sols3 N).filter
              (fun y => ((y.1.1 : ℤ) + (y.2.2.2.1 : ℤ)).natAbs = k),
            2 * ((y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K))) * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int (Sols3 N) _
      (fun y => (y.1.1 : ℤ) + (y.2.2.2.1 : ℤ))
      (fun y hy => by have := hb y hy; omega)
  have hw10 : (∑ y ∈ Sols3 N,
        2 * ((y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K))
          * Fz u ((y.1.1 : ℤ) - (y.2.2.2.1 : ℤ)))
      = ∑ k ∈ Finset.Icc 1 N,
          (∑ y ∈ (Sols3 N).filter
              (fun y => ((y.1.1 : ℤ) - (y.2.2.2.1 : ℤ)).natAbs = k),
            2 * ((y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K))) * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int (Sols3 N) _
      (fun y => (y.1.1 : ℤ) - (y.2.2.2.1 : ℤ))
      (fun y hy => by have := hb y hy; omega)
  have hw11 : (∑ y ∈ Sols3 N,
        4 * ((y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K)) * Fz u (y.1.1 : ℤ))
      = ∑ k ∈ Finset.Icc 1 N,
          (∑ y ∈ (Sols3 N).filter (fun y => ((y.1.1 : ℤ)).natAbs = k),
            4 * ((y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K))) * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int (Sols3 N) _ (fun y => (y.1.1 : ℤ))
      (fun y hy => by have := hb y hy; omega)
  have hw12 : (∑ y ∈ Sols3 N,
        4 * ((y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K)) * Fz u (y.2.1 : ℤ))
      = ∑ k ∈ Finset.Icc 1 N,
          (∑ y ∈ (Sols3 N).filter (fun y => ((y.2.1 : ℤ)).natAbs = k),
            4 * ((y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K))) * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int (Sols3 N) _ (fun y => (y.2.1 : ℤ))
      (fun y hy => by have := hb y hy; omega)
  have hw13 : (∑ y ∈ Sols3 N,
        4 * ((y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K)) * Fz u (y.2.2.2.1 : ℤ))
      = ∑ k ∈ Finset.Icc 1 N,
          (∑ y ∈ (Sols3 N).filter (fun y => ((y.2.2.2.1 : ℤ)).natAbs = k),
            4 * ((y.1.1 : K) * (y.2.1 : K) * (y.2.2.2.1 : K))) * Fz u (k : ℤ) :=
    sum_mul_Fz_eq_sum_lines_int (Sols3 N) _ (fun y => (y.2.2.2.1 : ℤ))
      (fun y hy => by have := hb y hy; omega)
  rw [hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13]

  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [tripleLine]
  push_cast
  ring

end TripleSource

section Master

variable {K : Type*} [NontriviallyNormedField K] {u : K}

theorem four_mul_defectCoeff_eq_sum_lines [CharZero K]
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) {N : ℕ} (hN : 0 < N) :
    4 * defectCoeff u N
      = ∑ k ∈ Finset.Icc 1 N, ((lineCoeff N k : ℤ) : K) * Fz u (k : ℤ) := by
  rw [defectCoeff_eq_sols3_normal_form hu0 hu1 hN]
  have hGK := four_mul_sum_Sols_yy_add_xy (u := u) hu0 N
  have h1 := boundary_eq_sum_lines (K := K) (u := u) hN
  have h2 := mixed_eq_sum_lines (u := u) N
  have h3 := tent_eq_sum_lines (u := u) hu0 hu1 N
  have h4 := sfive_eq_sum_lines (K := K) (u := u) N
  have h5 := triple_eq_sum_lines (u := u) hu0 N
  have hMERGE : (∑ k ∈ Finset.Icc 1 N, ((lineCoeff N k : ℤ) : K) * Fz u (k : ℤ))
      = -4 * (∑ k ∈ Finset.Icc 1 N, ((boundaryLine N k : ℤ) : K) * Fz u (k : ℤ))
        + (∑ k ∈ Finset.Icc 1 N, ((mixedLine N k : ℤ) : K) * Fz u (k : ℤ))
        - 12 * (∑ k ∈ Finset.Icc 1 N, ((tentLine N k : ℤ) : K) * Fz u (k : ℤ))
        + 4 * (∑ k ∈ Finset.Icc 1 N, ((sFiveLine N k : ℤ) : K) * Fz u (k : ℤ))
        - 4 * (∑ k ∈ Finset.Icc 1 N, ((tripleLine N k : ℤ) : K) * Fz u (k : ℤ)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [lineCoeff]
    push_cast
    ring
  linear_combination hGK - 4 * h1 + h2 - 12 * h3 + 4 * h4 - 4 * h5 - hMERGE

theorem defectCoeff_eq_zero_of_lineCoeff_eq_zero [CharZero K]
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) {N : ℕ} (hN : 0 < N)
    (h : ∀ k ∈ Finset.Icc 1 N, lineCoeff N k = 0) :
    defectCoeff u N = 0 := by
  have h4 : (4 : K) * defectCoeff u N = 0 := by
    rw [four_mul_defectCoeff_eq_sum_lines hu0 hu1 hN]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [h k hk]
    simp
  have h40 : (4 : K) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h4).resolve_left h40

end Master

end TateCurve


