-- Prove2me | Definitions.Def_RPLib_S4_PicDescentB1
-- name    : RPLib_S4_PicDescentB1
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:04:12.822763+00:00
-- url     : https://prove2.me/theorems/0a839e81-991e-451c-ae5a-561382344f48
-- title:
--   Coordinates for the constant field extension $L(x)/\mathbb{F}_q(x)$
-- statement:
--   Let $L/\mathbb{F}_q$ be a finite extension with an $\mathbb{F}_q$-basis $(c_j)$. Every $P \in L[X]$ is $\sum_j P_j c_j$ with $P_j \in \mathbb{F}_q[X]$ of degree at most $\deg P$; every nonzero element of $L[X]$ divides a nonzero element of $\mathbb{F}_q[X]$; the inclusion $\mathbb{F}_q(x) \to L(x)$ maps the valuation ring $\mathcal{O}_\infty$ at infinity into that of $L(x)$, and $$\mathcal{O}_\infty(L) = \Big\{\sum_j g_j c_j : g_j \in \mathcal{O}_\infty(\mathbb{F}_q)\Big\} = L \otimes_{\mathbb{F}_q} \mathcal{O}_\infty(\mathbb{F}_q).$$
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Rosen, Number Theory in Function Fields, GTM 210, Springer (2002), Chapter 8; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009), Section 3.6

import Definitions.Def_RPLib_S4_PicDescentA

/-!
# S4-PicDescent, part B1: coordinates for the constant field extension `L(x) / Fq(x)`

`L / Fq` a finite field extension with an `Fq`-basis `c`.
* `polyCoord c P j ∈ Fq[X]`: the coordinate polynomials of `P ∈ L[X]`, `Σ_j P_j c_j = P`, `deg P_j ≤ deg P`.
* `exists_map_dvd`: every nonzero `q ∈ L[X]` divides a nonzero `d ∈ Fq[X]` (`L[X]` is integral over `Fq[X]`).
* `ratMap : Fq(x) →+* L(x)`, `ratMap_mem_Oinf` (it maps `O_∞(Fq)` into `O_∞(L)`).
* `exists_Oinf_coord`: every `a ∈ O_∞(L)` is `Σ_j g_j c_j` with `g_j ∈ O_∞(Fq)`, i.e. `O_∞(L) = L ⊗ O_∞(Fq)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.PicDescent

open Places Polynomial

section Coord

theorem alg_ne_zero {K : Type*} [Field K] {p : K[X]} (hp : p ≠ 0) :
    algebraMap K[X] (RatFunc K) p ≠ 0 := by
  rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))]

theorem intDegree_div_poly {K : Type*} [Field K] {p d : K[X]} (hp : p ≠ 0) (hd : d ≠ 0) :
    (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) d).intDegree =
      (p.natDegree : ℤ) - d.natDegree := by
  rw [RatFunc.intDegree_div (alg_ne_zero hp) (alg_ne_zero hd), RatFunc.intDegree_polynomial,
    RatFunc.intDegree_polynomial]

theorem mem_Oinf_div {K : Type*} [Field K] [DecidableEq (RatFunc K)] {p d : K[X]} (hd : d ≠ 0)
    (h : p.natDegree ≤ d.natDegree) :
    algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) d ∈ Oinf K := by
  by_cases hp : p = 0
  · rw [hp, map_zero, zero_div]; exact zero_mem _
  rw [mem_Oinf_iff' K (div_ne_zero (alg_ne_zero hp) (alg_ne_zero hd)), intDegree_div_poly hp hd]
  omega

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {ι : Type*} [Fintype ι]

/-- The `j`-th coordinate polynomial of `P ∈ L[X]` for an `Fq`-basis `c` of `L`. -/
noncomputable def polyCoord (c : Module.Basis ι Fq L) (P : L[X]) (j : ι) : Fq[X] :=
  P.sum fun i a => monomial i (c.repr a j)

theorem coeff_polyCoord (c : Module.Basis ι Fq L) (P : L[X]) (j : ι) (i : ℕ) :
    (polyCoord c P j).coeff i = c.repr (P.coeff i) j := by
  simp only [polyCoord, Polynomial.sum_def, finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq',
    mem_support_iff]
  split_ifs with h
  · rfl
  · have h0 : P.coeff i = 0 := by simpa using h
    rw [h0, map_zero, Finsupp.zero_apply]

theorem natDegree_polyCoord_le (c : Module.Basis ι Fq L) (P : L[X]) (j : ι) :
    (polyCoord c P j).natDegree ≤ P.natDegree :=
  natDegree_le_iff_coeff_eq_zero.mpr fun i hi => by
    rw [coeff_polyCoord, coeff_eq_zero_of_natDegree_lt hi, map_zero, Finsupp.zero_apply]

theorem sum_polyCoord (c : Module.Basis ι Fq L) (P : L[X]) :
    ∑ j, (polyCoord c P j).map (algebraMap Fq L) * C (c j) = P := by
  ext i
  simp only [finsetSum_coeff, coeff_mul_C, coeff_map, coeff_polyCoord]
  simp_rw [← Algebra.smul_def]
  exact c.sum_repr (P.coeff i)

/-- Every nonzero `q ∈ L[X]` divides some nonzero `d ∈ Fq[X]`. -/
theorem exists_map_dvd {q : L[X]} (hq : q ≠ 0) :
    ∃ d : Fq[X], d ≠ 0 ∧ q ∣ d.map (algebraMap Fq L) := by
  let _ : Algebra Fq[X] L[X] := Polynomial.algebra Fq L
  have : Module.Finite Fq L := Module.Finite.of_finite
  have hint : IsIntegral Fq[X] q :=
    Polynomial.isIntegral_iff_isIntegral_coeff.mpr fun n => Algebra.IsIntegral.isIntegral _
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.comap_ne_bot_of_integral_mem hq (Ideal.mem_span_singleton_self q) hint)
  exact ⟨d, hd0, Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp hd)⟩

variable (Fq L) in
/-- The ring map `Fq(x) → L(x)`. -/
noncomputable def ratMap : RatFunc Fq →+* RatFunc L :=
  RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap Fq L))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ (algebraMap Fq L).injective))

theorem ratMap_div (p d : Fq[X]) :
    ratMap Fq L (algebraMap Fq[X] (RatFunc Fq) p / algebraMap Fq[X] (RatFunc Fq) d) =
      algebraMap L[X] (RatFunc L) (p.map (algebraMap Fq L)) /
        algebraMap L[X] (RatFunc L) (d.map (algebraMap Fq L)) :=
  RatFunc.map_apply_div _ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (Polynomial.map_injective _ (algebraMap Fq L).injective)) p d

theorem ratMap_algebraMap (p : Fq[X]) :
    ratMap Fq L (algebraMap Fq[X] (RatFunc Fq) p) = algebraMap L[X] (RatFunc L) (p.map (algebraMap Fq L)) := by
  have h := ratMap_div (L := L) p 1
  rwa [map_one, div_one, Polynomial.map_one, map_one, div_one] at h

theorem ratMap_mem_Oinf {g : RatFunc Fq} (hg : g ∈ Oinf Fq) : ratMap Fq L g ∈ Oinf L := by
  by_cases h0 : g = 0
  · rw [h0, map_zero]; exact zero_mem _
  have hdeg : g.intDegree ≤ 0 := (mem_Oinf_iff' Fq h0).mp hg
  have e := RatFunc.num_div_denom g
  rw [← e, ratMap_div]
  apply mem_Oinf_div ((Polynomial.map_ne_zero_iff (algebraMap Fq L).injective).mpr (RatFunc.denom_ne_zero g))
  rw [natDegree_map, natDegree_map]
  unfold RatFunc.intDegree at hdeg
  omega

/-- `O_∞(L) = L ⊗ O_∞(Fq)` in coordinates. -/
theorem exists_Oinf_coord (c : Module.Basis ι Fq L) {a : RatFunc L} (ha : a ∈ Oinf L) :
    ∃ g : ι → RatFunc Fq, (∀ j, g j ∈ Oinf Fq) ∧
      a = ∑ j, ratMap Fq L (g j) * algebraMap L (RatFunc L) (c j) := by
  by_cases ha0 : a = 0
  · exact ⟨0, fun j => zero_mem _, by simp [ha0]⟩
  obtain ⟨d, hd0, r, hr⟩ := exists_map_dvd (Fq := Fq) (RatFunc.denom_ne_zero a)
  have hdm : d.map (algebraMap Fq L) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap Fq L).injective).mpr hd0
  have hr0 : r ≠ 0 := by rintro rfl; rw [mul_zero] at hr; exact hdm hr
  have hP0 : a.num * r ≠ 0 := mul_ne_zero (RatFunc.num_ne_zero ha0) hr0
  have haP : a = algebraMap L[X] (RatFunc L) (a.num * r) /
      algebraMap L[X] (RatFunc L) (d.map (algebraMap Fq L)) := by
    rw [hr, map_mul, map_mul, mul_div_mul_right _ _ (alg_ne_zero hr0), RatFunc.num_div_denom]
  have hdeg : (a.num * r).natDegree ≤ d.natDegree := by
    have := (mem_Oinf_iff' L ha0).mp ha
    rw [haP, intDegree_div_poly hP0 hdm, natDegree_map] at this
    omega
  refine ⟨fun j => algebraMap Fq[X] (RatFunc Fq) (polyCoord c (a.num * r) j) /
      algebraMap Fq[X] (RatFunc Fq) d,
    fun j => mem_Oinf_div hd0 ((natDegree_polyCoord_le c _ j).trans hdeg), ?_⟩
  conv_lhs => rw [haP, ← sum_polyCoord c (a.num * r)]
  rw [map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ratMap_div, map_mul, div_mul_eq_mul_div, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]

end Coord

end RamanujanPetersson.PicDescent


