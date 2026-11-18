-- Prove2me | solution 1 for APSCounting893.Main.Supplement.homogeneous_puiseux_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T02:58:54.126658+00:00
-- url     : https://prove2.me/submissions/56be23e8-0768-416f-8774-9a45a7d4caad

import Definitions.Def_APSCounting893_Main_Geometry
import Theorems.Thm_HahnSeries_mem_puiseuxRamSubfield_iff
import Definitions.Def_APSCounting893_Main_Resultant
import Theorems.Thm_APSCounting893_Main_zero_fiber_residues

section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma eval_homogenize_monomial {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (z : Fin (n + 1) → K) (e : Fin n →₀ ℕ) (c : R) (d : ℕ) :
    MvPolynomial.eval₂ f z (MvPolynomial.monomial
      (Finsupp.single 0 (d - e.sum (fun _ k => k)) + e.mapDomain Fin.succ) c) =
    f c * z 0 ^ (d - e.sum (fun _ k => k)) * e.prod (fun i k => z i.succ ^ k) := by
  classical
  rw [MvPolynomial.eval₂_monomial]
  rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  rw [Finsupp.prod_single_index (h := fun i k => z i ^ k) (pow_zero (z 0))]
  rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  ring

lemma finsupp_prod_scaled {K : Type} [Field K] {n : ℕ}
    (e : Fin n →₀ ℕ) (a : K) (x : Fin n → K) :
    e.prod (fun i k => (a * x i) ^ k) =
      a ^ e.sum (fun _ k => k) * e.prod (fun i k => x i ^ k) := by
  classical
  rw [e.prod_fintype _ (fun _ => pow_zero _), e.prod_fintype _ (fun _ => pow_zero _),
    e.sum_fintype _ (fun _ => rfl)]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

lemma eval_homogenize_scaled {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (p : MvPolynomial (Fin n) R) (d : ℕ) (hd : p.totalDegree ≤ d)
    (a : K) (x : Fin n → K) :
    MvPolynomial.eval₂ f (Fin.cases a (fun i => a * x i)) (homogenizeAll d p) =
      a ^ d * MvPolynomial.eval₂ f x p := by
  classical
  rw [homogenizeAll, MvPolynomial.eval₂_sum]
  conv_rhs => rw [MvPolynomial.eval₂_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [eval_homogenize_monomial]
  simp only [Fin.cases_zero, Fin.cases_succ]
  rw [finsupp_prod_scaled]
  have hedeg : e.sum (fun _ k => k) ≤ d := (MvPolynomial.le_totalDegree he).trans hd
  have hpow : a ^ (d - e.sum (fun _ k => k)) * a ^ e.sum (fun _ k => k) = a ^ d := by
    rw [← pow_add, Nat.sub_add_cancel hedeg]
  calc
    f (p.coeff e) * a ^ (d - e.sum (fun _ k => k)) *
        (a ^ e.sum (fun _ k => k) * e.prod (fun i k => x i ^ k)) =
      (a ^ (d - e.sum (fun _ k => k)) * a ^ e.sum (fun _ k => k)) *
        (f (p.coeff e) * e.prod (fun i k => x i ^ k)) := by ring
    _ = _ := by rw [hpow]; rfl

lemma eval_homogenize_dehomogenize {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (p : MvPolynomial (Fin n) R) (d : ℕ) (hd : p.totalDegree ≤ d)
    (z : Fin (n + 1) → K) (hz : z 0 ≠ 0) :
    MvPolynomial.eval₂ f z (homogenizeAll d p) =
      z 0 ^ d * MvPolynomial.eval₂ f (fun i => z i.succ / z 0) p := by
  have heq : Fin.cases (z 0) (fun i => z 0 * (z i.succ / z 0)) = z := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    simp [hz, mul_div_cancel₀, mul_comm]
  simpa only [heq] using eval_homogenize_scaled f p d hd (z 0) (fun i => z i.succ / z 0)

end APSCounting893.Main

end


section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open HahnSeries
namespace APSCounting893.Main

lemma ramBound_mul_right {e f : ℕ} (he : 0 < e) (hf : 0 < f)
    {s : PuiseuxAmbient} (hs : HahnSeries.HasRamBound e s) :
    HahnSeries.HasRamBound (e * f) s := by
  intro q hq
  obtain ⟨k, hk⟩ := hs hq
  refine ⟨k * (f : ℤ), ?_⟩
  rw [← hk]
  have he0 : (e : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  have hf0 : (f : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hf.ne'
  push_cast
  field_simp

lemma isPuiseux_zero : IsPuiseux (0 : PuiseuxAmbient) := by
  exact ⟨1, by decide, (HahnSeries.puiseuxRamSubfield ℂ (by decide : 0 < 1)).zero_mem⟩

lemma isPuiseux_one : IsPuiseux (1 : PuiseuxAmbient) := by
  exact ⟨1, by decide, (HahnSeries.puiseuxRamSubfield ℂ (by decide : 0 < 1)).one_mem⟩

lemma isPuiseux_single (q : ℚ) (c : ℂ) : IsPuiseux (HahnSeries.single q c) := by
  refine ⟨q.den, q.den_pos, (HahnSeries.mem_puiseuxRamSubfield_iff q.den_pos).mpr ?_⟩
  intro r hr
  have hrq : r = q := by
    by_contra h
    exact hr (HahnSeries.coeff_single_of_ne h)
  subst r
  exact ⟨q.num, Rat.num_div_den q⟩

lemma isPuiseux_inv {s : PuiseuxAmbient} (hs : IsPuiseux s) : IsPuiseux s⁻¹ := by
  obtain ⟨e, he, hs⟩ := hs
  exact ⟨e, he, (HahnSeries.puiseuxRamSubfield ℂ he).inv_mem hs⟩

lemma isPuiseux_mul {s t : PuiseuxAmbient} (hs : IsPuiseux s) (ht : IsPuiseux t) :
    IsPuiseux (s * t) := by
  obtain ⟨e, he, hs⟩ := hs
  obtain ⟨f, hf, ht⟩ := ht
  refine ⟨e * f, Nat.mul_pos he hf, ?_⟩
  have hs' := ramBound_mul_right he hf ((HahnSeries.mem_puiseuxRamSubfield_iff he).mp hs)
  have ht' := ramBound_mul_right hf he ((HahnSeries.mem_puiseuxRamSubfield_iff hf).mp ht)
  rw [Nat.mul_comm f e] at ht'
  exact (HahnSeries.puiseuxRamSubfield ℂ (Nat.mul_pos he hf)).mul_mem
    ((HahnSeries.mem_puiseuxRamSubfield_iff (Nat.mul_pos he hf)).mpr hs')
    ((HahnSeries.mem_puiseuxRamSubfield_iff (Nat.mul_pos he hf)).mpr ht')

lemma isPuiseux_div {s t : PuiseuxAmbient} (hs : IsPuiseux s) (ht : IsPuiseux t) :
    IsPuiseux (s / t) := by
  rw [div_eq_mul_inv]
  exact isPuiseux_mul hs (isPuiseux_inv ht)

lemma positive_orderTop_of_integral_residue_zero (s : PuiseuxAmbient)
    (hs : 0 ≤ s.orderTop) (hres : s.coeff 0 = 0) : 0 < s.orderTop := by
  by_cases hzero : s = 0
  · simp [hzero]
  have horder : 0 ≤ s.order := HahnSeries.zero_le_orderTop_iff.mp hs
  have hne : s.order ≠ 0 := by
    intro h
    have hlead := HahnSeries.leadingCoeff_ne_zero.mpr hzero
    rw [HahnSeries.leadingCoeff_eq, h] at hlead
    exact hlead hres
  exact HahnSeries.zero_lt_orderTop_of_order (lt_of_le_of_ne horder (Ne.symm hne))

lemma normalize_puiseux_coordinates {n : ℕ} (w : Fin n → PuiseuxAmbient)
    (hw : ∀ j, IsPuiseux (w j)) (hn : ∃ j, w j ≠ 0) :
    ∃ a : PuiseuxAmbient, a ≠ 0 ∧ IsPuiseux a ∧
      (∀ j, 0 ≤ (a * w j).orderTop) ∧ ∃ j, (a * w j).orderTop = 0 := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun j => w j ≠ 0)
  have hS : S.Nonempty := by
    obtain ⟨j, hj⟩ := hn
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image S (fun i => (w i).order) hS
  have hj0 : w j ≠ 0 := (Finset.mem_filter.mp hj).2
  let a : PuiseuxAmbient := HahnSeries.single (-(w j).order) (1 : ℂ)
  have ha : a ≠ 0 := by simp [a]
  have hao : a.order = -(w j).order := HahnSeries.order_single one_ne_zero
  refine ⟨a, ha, isPuiseux_single _ _, ?_, j, ?_⟩
  · intro i
    by_cases hi : w i = 0
    · simp [hi]
    · have hle : (w j).order ≤ (w i).order :=
        hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
      rw [← HahnSeries.order_eq_orderTop_of_ne_zero (mul_ne_zero ha hi), HahnSeries.order_mul ha hi, hao]
      have hh : 0 ≤ -(w j).order + (w i).order := by linarith
      exact_mod_cast hh
  · rw [← HahnSeries.order_eq_orderTop_of_ne_zero (mul_ne_zero ha hj0), HahnSeries.order_mul ha hj0, hao]
    simp

end APSCounting893.Main

end


section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

noncomputable def tCoefficientHom : Polynomial ℂ →+* PuiseuxAmbient :=
  Polynomial.eval₂RingHom HahnSeries.C (HahnSeries.single (1 : ℚ) (1 : ℂ))

noncomputable def tAuxHom : Aux →+* PuiseuxAmbient :=
  MvPolynomial.eval₂Hom HahnSeries.C
    (fun v : Fin 4 => if v = 2 then HahnSeries.single (1 : ℚ) (1 : ℂ) else 0)

lemma tCoefficient_C (c : ℂ) : tCoefficientHom (Polynomial.C c) = HahnSeries.C c := by
  simp [tCoefficientHom]

lemma tAux_polynomial_coefficients (p : Polynomial ℂ) :
    tAuxHom ((Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (2 : Fin 4))) p) =
      tCoefficientHom p := by
  have heq : tAuxHom.comp (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (2 : Fin 4))) =
      tCoefficientHom := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [tAuxHom, tCoefficientHom]
    · simp [tAuxHom, tCoefficientHom]
  exact RingHom.congr_fun heq p

lemma equationWithAux_specializes (F : RawMap) (c alpha : Affine ℂ F.n)
    (i : Fin (F.n + (F.n + 1))) (x : Affine PuiseuxAmbient (F.n + (F.n + 1))) :
    MvPolynomial.eval₂ tAuxHom x (equationWithAux F c alpha i) =
      MvPolynomial.eval₂ tCoefficientHom x
        (affineLineEquations F c alpha (Fin.cast (Nat.add_comm _ _) i)) := by
  rw [equationWithAux, MvPolynomial.eval₂_map]
  have heq : tAuxHom.comp (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (2 : Fin 4))) =
      tCoefficientHom := by
    exact RingHom.ext tAux_polynomial_coefficients
  rw [heq]

lemma affineLineEquations_iff (F : ReducedMap) (D : LineData F)
    (z : Affine PuiseuxAmbient (F.n + (F.n + 1))) :
    (∀ i, MvPolynomial.eval₂ tCoefficientHom z (affineLineEquations F D.c D.alpha i) = 0) ↔
      (∀ j : Fin (F.n + 1), z (j.natAdd F.n) =
        MvPolynomial.eval₂ HahnSeries.C (fun i => z (i.castAdd (F.n + 1))) (F.F j)) ∧
      (∀ j : Fin F.n, z (j.castSucc.natAdd F.n) - HahnSeries.C (D.c j) * z ((Fin.last F.n).natAdd F.n) =
        HahnSeries.C (D.alpha j) * HahnSeries.single (1 : ℚ) (1 : ℂ)) := by
  have hcomp : tCoefficientHom.comp Polynomial.C = HahnSeries.C := by
    exact RingHom.ext tCoefficient_C
  have hout (j : Fin (F.n + 1)) :
      MvPolynomial.eval₂ tCoefficientHom z
        (affineLineEquations F D.c D.alpha (j.castAdd F.n)) =
      z (j.natAdd F.n) - MvPolynomial.eval₂ HahnSeries.C
        (fun i => z (i.castAdd (F.n + 1))) (F.F j) := by
    simp only [affineLineEquations, Fin.addCases_left, MvPolynomial.eval₂_sub,
      MvPolynomial.eval₂_X, MvPolynomial.eval₂_rename, MvPolynomial.eval₂_map, hcomp]
    rfl
  have hline (j : Fin F.n) :
      MvPolynomial.eval₂ tCoefficientHom z
        (affineLineEquations F D.c D.alpha (j.natAdd (F.n + 1))) =
      z (j.castSucc.natAdd F.n) - HahnSeries.C (D.c j) * z ((Fin.last F.n).natAdd F.n) -
        HahnSeries.C (D.alpha j) * HahnSeries.single (1 : ℚ) (1 : ℂ) := by
    simp [affineLineEquations, tCoefficientHom]
  constructor
  · intro h
    exact ⟨fun j => sub_eq_zero.mp ((hout j).symm.trans (h _)),
      fun j => sub_eq_zero.mp ((hline j).symm.trans (h _))⟩
  · rintro ⟨ho, hl⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [hout, ho, sub_self]
    · rw [hline, hl, sub_self]

end APSCounting893.Main

end


section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

lemma homogeneous_equations_chart_iff (F : ReducedMap) (D : LineData F)
    (degrees : Fin (F.n + (F.n + 1)) → ℕ)
    (hdegrees : HomogenizingDegrees F D.c D.alpha degrees)
    (z : Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient) (hz : z 0 ≠ 0) :
    (∀ i, MvPolynomial.eval₂ tAuxHom z (homogenizedEquation F D.c D.alpha degrees i) = 0) ↔
      ∀ i, MvPolynomial.eval₂ tCoefficientHom (fun j => z j.succ / z 0)
        (affineLineEquations F D.c D.alpha i) = 0 := by
  have heq (i : Fin (F.n + (F.n + 1))) :
      MvPolynomial.eval₂ tAuxHom z (homogenizedEquation F D.c D.alpha degrees i) =
      z 0 ^ degrees i * MvPolynomial.eval₂ tCoefficientHom (fun j => z j.succ / z 0)
        (affineLineEquations F D.c D.alpha (Fin.cast (Nat.add_comm _ _) i)) := by
    rw [homogenizedEquation, eval_homogenize_dehomogenize _ _ _ (hdegrees i).2.2 _ hz,
      equationWithAux_specializes]
  constructor
  · intro h i
    let j : Fin (F.n + (F.n + 1)) := Fin.cast (Nat.add_comm _ _) i
    have hh := h j
    rw [heq, mul_eq_zero] at hh
    exact (hh.resolve_left (pow_ne_zero _ hz))
  · intro h i
    rw [heq, h, mul_zero]

lemma homogeneous_puiseux_equivalence (F : ReducedMap) (D : LineData F)
    (degrees : Fin (F.n + (F.n + 1)) → ℕ)
    (hdegrees : HomogenizingDegrees F D.c D.alpha degrees) :
    hasAPS F.F ↔
      ∃ z : Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient,
        (∀ j, IsPuiseux (z j)) ∧ z 0 ≠ 0 ∧
        (∀ j, 0 ≤ (z j).orderTop) ∧ (∃ j, (z j).orderTop = 0) ∧
        (∀ i, MvPolynomial.eval₂ tAuxHom z (homogenizedEquation F D.c D.alpha degrees i) = 0) ∧
        (∀ i : Fin (F.n + 1), 0 < (z (i.natAdd F.n).succ / z 0).orderTop) := by
  classical
  constructor
  · intro hAPS
    have hy : (0 : Affine ℂ (F.n + 1)) ∈ zeroFiber F D.c := by
      refine ⟨hAPS, ?_⟩
      funext j
      simp [normalization, normalizationPolynomials, evaluate]
    obtain ⟨w, hw, hres⟩ := (zero_fiber_residues F D).2 0 hy
    have hint := (zero_fiber_residues F D).1 w hw
    let u : Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient := Fin.cases 1 w
    have hu (j) : IsPuiseux (u j) := by
      refine Fin.cases ?_ (fun i => ?_) j
      · exact isPuiseux_one
      · exact hw.1 i
    obtain ⟨a, ha, haP, hnonneg, hmin⟩ := normalize_puiseux_coordinates u hu ⟨0, by simp [u]⟩
    let z : Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient := fun j => a * u j
    have hz0 : z 0 = a := by simp [z, u]
    have hzsucc (j : Fin (F.n + (F.n + 1))) : z j.succ = a * w j := by simp [z, u]
    have hdehom (j : Fin (F.n + (F.n + 1))) : z j.succ / z 0 = w j := by
      rw [hz0, hzsucc, mul_div_cancel_left₀ _ ha]
    refine ⟨z, fun j => isPuiseux_mul haP (hu j), by rwa [hz0], hnonneg, hmin, ?_, ?_⟩
    · apply (homogeneous_equations_chart_iff F D degrees hdegrees z (by rwa [hz0])).mpr
      rw [funext hdehom]
      exact (affineLineEquations_iff F D w).mpr hw.2
    · intro i
      rw [hdehom]
      apply positive_orderTop_of_integral_residue_zero _ ((hint.1 i).2)
      exact congrFun hres i
  · rintro ⟨z, hzP, hz0, hnonneg, hmin, heq, hpositive⟩
    let w : Affine PuiseuxAmbient (F.n + (F.n + 1)) := fun j => z j.succ / z 0
    have hw : w ∈ lineSolutions F D := by
      refine ⟨fun j => isPuiseux_div (hzP j.succ) (hzP 0), ?_⟩
      apply (affineLineEquations_iff F D w).mp
      exact (homogeneous_equations_chart_iff F D degrees hdegrees z hz0).mp heq
    have hres : outputResidue F w = 0 := by
      funext i
      exact HahnSeries.coeff_eq_zero_of_lt_orderTop (hpositive i)
    have hmem := (zero_fiber_residues F D).1 w hw
    rw [hres] at hmem
    exact hmem.2.1

end APSCounting893.Main

end


open APSCounting893.Main

theorem solution (F : ReducedMap) (D : LineData F)
    (degrees : Fin (F.n + (F.n + 1)) → ℕ)
    (hdegrees : HomogenizingDegrees F.toRawMap D.c D.alpha degrees) :
    hasAPS F.F ↔
      ∃ z : Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient,
        (∀ j, IsPuiseux (z j)) ∧ z 0 ≠ 0 ∧
        (∀ j, 0 ≤ (z j).orderTop) ∧ (∃ j, (z j).orderTop = 0) ∧
        (∀ i, MvPolynomial.eval₂
          (MvPolynomial.eval₂Hom HahnSeries.C
            (fun v : Fin 4 => if v = 2 then HahnSeries.single (1 : ℚ) (1 : ℂ) else 0))
          z (homogenizedEquation F.toRawMap D.c D.alpha degrees i) = 0) ∧
        (∀ i : Fin (F.n + 1), 0 < (z (i.natAdd F.n).succ / z 0).orderTop) := by
  exact homogeneous_puiseux_equivalence F D degrees hdegrees


