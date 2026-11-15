-- Prove2me | Definitions.Def_RPLib_S3_EllW2G2
-- name    : RPLib_S3_EllW2G2
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:29:43.074803+00:00
-- url     : https://prove2.me/theorems/c7d52aae-9cc8-4216-b04b-e687acbfd7e6
-- title:
--   The Eichler-Selberg trace formula in weight two: `summable_SP`
-- statement:
--   `summable_SP`.
--
--   For `n > 0`, `Σ_{det g = n, IsSP g} N(g)⁻¹ < ∞`. The `c = 0` matrices inject into `(a, b)`; for `c ≠ 0`
--   the map `Psi g = ((t, 0 < c), ((c₁, c₂), e))` (`e = d - a`, `c₁ = gcd(c, R - e)`, `c₂ = |c| / c₁`,
--   `R = √(t² - 4n)`) is injective and `N(g)⁻¹ ≤ 2 ((c₁c₂)² + e²)⁻¹` with `e` in the set of `coset_sum`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2G

/-!
# S3-ES-Wt2 (O6, part G2): **`summable_SP`**

For `n > 0`, `Σ_{det g = n, IsSP g} N(g)⁻¹ < ∞`. The `c = 0` matrices inject into `(a, b)`; for `c ≠ 0`
the map `Psi g = ((t, 0 < c), ((c₁, c₂), e))` (`e = d - a`, `c₁ = gcd(c, R - e)`, `c₂ = |c| / c₁`,
`R = √(t² - 4n)`) is injective and `N(g)⁻¹ ≤ 2 ((c₁c₂)² + e²)⁻¹` with `e` in the set of `coset_sum`.
-/

open Filter Topology

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.HypPar

lemma abs_tr_le {n t r : ℤ} (hn : 0 < n) (h : t ^ 2 - 4 * n = r ^ 2) : |t| ≤ 4 * n := by
  have ht : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  have hr : r ^ 2 = |r| ^ 2 := (sq_abs r).symm
  have h0 : 0 ≤ |r| := abs_nonneg r
  have h1 : 0 ≤ |t| := abs_nonneg t
  have hlt : |r| < |t| := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith [mul_le_mul hc hc h1 h0]
  have hle : |r| + 1 ≤ |t| := Int.lt_iff_add_one_le.1 hlt
  nlinarith [mul_nonneg (sub_nonneg.2 hle) (add_nonneg h1 h0)]

/-! ## The `c = 0` part -/

lemma summable_c0 {n : ℤ} (hn : 0 < n) :
    Summable ({g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ g 1 0 = 0}.indicator (Eg 2)) := by
  rw [← summable_subtype_iff_indicator]
  have hu : Summable (fun a : ℤ => if |a| ≤ n then (1 : ℝ) else 0) := by
    refine summable_of_ne_finset_zero (s := Finset.Icc (-n) n) (fun a ha => ?_)
    rw [Finset.mem_Icc] at ha
    rw [if_neg]
    intro h
    exact ha (abs_le.1 h)
  have hs := hu.mul_of_nonneg RamanujanPetersson.GSA.summable_inv_one_add_sq
    (fun a => by dsimp only; split_ifs <;> norm_num) (fun _ => by positivity)
  have hdet : ∀ g : Matrix (Fin 2) (Fin 2) ℤ, g.det = n → g 1 0 = 0 → g 0 0 * g 1 1 = n := by
    intro g h1 h2
    rw [Matrix.det_fin_two, h2, mul_zero, sub_zero] at h1
    exact h1
  set φ : {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ g 1 0 = 0} → ℤ × ℤ :=
    fun g => (g.1 0 0, g.1 0 1) with hφ
  have hφi : Function.Injective φ := by
    rintro ⟨g, hg⟩ ⟨g', hg'⟩ h
    simp only [hφ, Prod.mk.injEq] at h
    obtain ⟨ha, hb⟩ := h
    have e1 := hdet g hg.1 hg.2
    have e2 := hdet g' hg'.1 hg'.2
    have ha0 : g 0 0 ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at e1
      omega
    have hd : g 1 1 = g' 1 1 := mul_left_cancel₀ ha0 (by rw [e1, ha, e2])
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact ha
    · exact hb
    · exact hg.2.trans hg'.2.symm
    · exact hd
  refine (hs.comp_injective hφi).of_nonneg_of_le (fun g => Eg_nonneg 2 g.1) (fun ⟨g, hg⟩ => ?_)
  have e1 := hdet g hg.1 hg.2
  have ha0 : g 0 0 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at e1
    omega
  have habs : |g 0 0| ≤ n := Int.le_of_dvd hn ((abs_dvd _ _).2 ⟨g 1 1, e1.symm⟩)
  have hsq : (1 : ℤ) ≤ g 0 0 ^ 2 := by
    rcases lt_or_gt_of_ne ha0 with h | h <;> nlinarith
  have hsq' : (1 : ℝ) ≤ (g 0 0 : ℝ) ^ 2 := by exact_mod_cast hsq
  show Eg 2 g ≤ (if |g 0 0| ≤ n then (1 : ℝ) else 0) * (1 + (g 0 1 : ℝ) ^ 2)⁻¹
  rw [if_pos habs, one_mul, Eg_two]
  apply inv_anti₀ (by positivity)
  unfold N
  nlinarith [sq_nonneg (g 1 0 : ℝ), sq_nonneg (g 1 1 : ℝ)]

/-! ## The `c ≠ 0` part -/

/-- `√(t² - 4n)` (exact when the discriminant is a square). -/
def Rt (n t : ℤ) : ℤ := Int.sqrt (t ^ 2 - 4 * n)

lemma Rt_sq {n t r : ℤ} (h : t ^ 2 - 4 * n = r ^ 2) : Rt n t ^ 2 = t ^ 2 - 4 * n := by
  unfold Rt
  rw [h, sq r, Int.sqrt_eq, ← sq, Int.natAbs_pow_two]

/-- `c₁ = gcd(c, R - e)`. -/
def c1f (n : ℤ) (g : Matrix (Fin 2) (Fin 2) ℤ) : ℕ :=
  Int.gcd (g 1 0) (Rt n (g 0 0 + g 1 1) - (g 1 1 - g 0 0))

/-- `c₂ = |c| / c₁`. -/
def c2f (n : ℤ) (g : Matrix (Fin 2) (Fin 2) ℤ) : ℕ := (g 1 0 / (c1f n g : ℤ)).natAbs

/-- The injection `g ↦ ((t, 0 < c), ((c₁, c₂), e))`. -/
def Psi (n : ℤ) (g : Matrix (Fin 2) (Fin 2) ℤ) : (ℤ × Bool) × ((ℕ × ℕ) × ℤ) :=
  ((g 0 0 + g 1 1, decide (0 < g 1 0)), ((c1f n g, c2f n g), g 1 1 - g 0 0))

lemma c1_dvd (n : ℤ) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    ((c1f n g : ℕ) : ℤ) ∣ Rt n (g 0 0 + g 1 1) - (g 1 1 - g 0 0) := by
  unfold c1f
  exact Int.gcd_dvd_right _ _

lemma c1_mul_c2 (n : ℤ) {g : Matrix (Fin 2) (Fin 2) ℤ} :
    c1f n g * c2f n g = (g 1 0).natAbs := by
  have hd : ((c1f n g : ℕ) : ℤ) ∣ g 1 0 := by unfold c1f; exact Int.gcd_dvd_left _ _
  have := congrArg Int.natAbs (Int.ediv_mul_cancel hd)
  rw [Int.natAbs_mul, Int.natAbs_natCast] at this
  rw [c2f, mul_comm]
  exact this

lemma c1_pos (n : ℤ) {g : Matrix (Fin 2) (Fin 2) ℤ} (hc : g 1 0 ≠ 0) : 1 ≤ c1f n g := by
  unfold c1f
  exact Int.gcd_pos_of_ne_zero_left _ hc

lemma c2_pos (n : ℤ) {g : Matrix (Fin 2) (Fin 2) ℤ} (hc : g 1 0 ≠ 0) : 1 ≤ c2f n g := by
  have hm := c1_mul_c2 n (g := g)
  have hp : 0 < (g 1 0).natAbs := Int.natAbs_pos.2 hc
  refine Nat.pos_of_ne_zero fun h => ?_
  rw [h, mul_zero] at hm
  omega

lemma dvd_add_of_gcd {c R e m : ℤ} (hc : c ≠ 0) (h : (R - e) * (R + e) = c * m) :
    c / (Int.gcd c (R - e) : ℤ) ∣ R + e := by
  have hGpos : 0 < Int.gcd c (R - e) := Int.gcd_pos_of_ne_zero_left _ hc
  have hG0 : (Int.gcd c (R - e) : ℤ) ≠ 0 := by exact_mod_cast hGpos.ne'
  have h1 : c / (Int.gcd c (R - e) : ℤ) * (Int.gcd c (R - e) : ℤ) = c :=
    Int.ediv_mul_cancel (Int.gcd_dvd_left _ _)
  have h2 : (R - e) / (Int.gcd c (R - e) : ℤ) * (Int.gcd c (R - e) : ℤ) = R - e :=
    Int.ediv_mul_cancel (Int.gcd_dvd_right _ _)
  have hcop := Int.gcd_ediv_gcd_ediv_gcd hGpos
  refine Int.dvd_of_dvd_mul_left_of_gcd_one ⟨m, ?_⟩ hcop
  apply mul_right_cancel₀ hG0
  linear_combination (R + e) * h2 - m * h1 + h

lemma c2_dvd {n : ℤ} {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : g.det = n) (hsp : IsSP g)
    (hc : g 1 0 ≠ 0) : ((c2f n g : ℕ) : ℤ) ∣ Rt n (g 0 0 + g 1 1) + (g 1 1 - g 0 0) := by
  obtain ⟨r, hr⟩ := hsp
  rw [hdet] at hr
  have hR := Rt_sq hr
  have hdet' : g 0 0 * g 1 1 - g 0 1 * g 1 0 = n := by rw [← Matrix.det_fin_two]; exact hdet
  have hprod : (Rt n (g 0 0 + g 1 1) - (g 1 1 - g 0 0)) * (Rt n (g 0 0 + g 1 1) + (g 1 1 - g 0 0)) =
      g 1 0 * (4 * g 0 1) := by
    linear_combination hR + 4 * hdet'
  unfold c2f c1f
  exact Int.natAbs_dvd.2 (dvd_add_of_gcd hc hprod)

/-! ## The dominating function -/

/-- Fibre weight over `((c₁, c₂), e)`. -/
def Gin (r : ℤ) (y : (ℕ × ℕ) × ℤ) : ℝ :=
  if 1 ≤ y.1.1 ∧ 1 ≤ y.1.2 then
    {e : ℤ | (y.1.1 : ℤ) ∣ r - e ∧ (y.1.2 : ℤ) ∣ r + e}.indicator
      (fun e : ℤ => (((y.1.1 * y.1.2 : ℕ) : ℝ) ^ 2 + (e : ℝ) ^ 2)⁻¹) y.2
  else 0

lemma Gin_nonneg (r : ℤ) (y : (ℕ × ℕ) × ℤ) : 0 ≤ Gin r y := by
  unfold Gin
  split_ifs
  · exact Set.indicator_nonneg (fun _ _ => by positivity) _
  · exact le_rfl

lemma summable_Gin (r : ℤ) : Summable (Gin r) := by
  refine (summable_prod_of_nonneg (fun y => Gin_nonneg r y)).2 ⟨fun p => ?_, ?_⟩
  · by_cases hp : 1 ≤ p.1 ∧ 1 ≤ p.2
    · have : (fun e => Gin r (p, e)) = {e : ℤ | (p.1 : ℤ) ∣ r - e ∧ (p.2 : ℤ) ∣ r + e}.indicator
          (fun e : ℤ => (((p.1 * p.2 : ℕ) : ℝ) ^ 2 + (e : ℝ) ^ 2)⁻¹) := funext fun e => if_pos hp
      rw [this]
      exact (coset_sum r hp.1 hp.2).1
    · have : (fun e => Gin r (p, e)) = fun _ => 0 := funext fun e => if_neg hp
      rw [this]
      exact summable_zero
  · refine (summable_inv_lcm_sq.mul_left (5 * K0)).of_nonneg_of_le
      (fun p => tsum_nonneg fun e => Gin_nonneg r (p, e)) (fun p => ?_)
    by_cases hp : 1 ≤ p.1 ∧ 1 ≤ p.2
    · have : (fun e => Gin r (p, e)) = {e : ℤ | (p.1 : ℤ) ∣ r - e ∧ (p.2 : ℤ) ∣ r + e}.indicator
          (fun e : ℤ => (((p.1 * p.2 : ℕ) : ℝ) ^ 2 + (e : ℝ) ^ 2)⁻¹) := funext fun e => if_pos hp
      rw [this]
      exact (coset_sum r hp.1 hp.2).2
    · have : (fun e => Gin r (p, e)) = fun _ => 0 := funext fun e => if_neg hp
      rw [this, tsum_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) K0_nonneg) (by positivity)

/-- The dominating function on `(ℤ × Bool) × ((ℕ × ℕ) × ℤ)`. -/
def Gfun (n : ℤ) (x : (ℤ × Bool) × ((ℕ × ℕ) × ℤ)) : ℝ :=
  if |x.1.1| ≤ 4 * n then 2 * Gin (Rt n x.1.1) x.2 else 0

lemma summable_Gfun (n : ℤ) : Summable (Gfun n) := by
  have h0 : ∀ x, 0 ≤ Gfun n x := fun x => by
    unfold Gfun
    split_ifs
    · exact mul_nonneg (by norm_num) (Gin_nonneg _ _)
    · exact le_rfl
  refine (summable_prod_of_nonneg h0).2 ⟨fun x => ?_, ?_⟩
  · by_cases hx : |x.1| ≤ 4 * n
    · have : (fun y => Gfun n (x, y)) = fun y => 2 * Gin (Rt n x.1) y := funext fun y => if_pos hx
      rw [this]
      exact (summable_Gin _).mul_left 2
    · have : (fun y => Gfun n (x, y)) = fun _ => 0 := funext fun y => if_neg hx
      rw [this]
      exact summable_zero
  · refine summable_of_ne_finset_zero (s := Finset.Icc (-(4 * n)) (4 * n) ×ˢ Finset.univ)
      (fun x hx => ?_)
    have hx' : ¬ |x.1| ≤ 4 * n := by
      intro h
      apply hx
      rw [Finset.mem_product, Finset.mem_Icc]
      exact ⟨abs_le.1 h, Finset.mem_univ _⟩
    have : (fun y => Gfun n (x, y)) = fun _ => 0 := funext fun y => if_neg hx'
    rw [this, tsum_zero]

/-! ## Summability over split and parabolic matrices -/

lemma summable_SPc {n : ℤ} (hn : 0 < n) :
    Summable ({g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ IsSP g ∧ g 1 0 ≠ 0}.indicator (Eg 2)) := by
  rw [← summable_subtype_iff_indicator]
  set Ψ' : {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ IsSP g ∧ g 1 0 ≠ 0} →
      (ℤ × Bool) × ((ℕ × ℕ) × ℤ) := fun g => Psi n g.1 with hΨ'
  have hinj : Function.Injective Ψ' := by
    rintro ⟨g, hg⟩ ⟨g', hg'⟩ h
    simp only [hΨ', Psi, Prod.mk.injEq, decide_eq_decide] at h
    obtain ⟨⟨ht, hs⟩, ⟨hc1, hc2⟩, he⟩ := h
    have hm := c1_mul_c2 n (g := g)
    have hm' := c1_mul_c2 n (g := g')
    have hca : (g 1 0).natAbs = (g' 1 0).natAbs := by rw [← hm, ← hm', hc1, hc2]
    have hc : g 1 0 = g' 1 0 := by
      rcases Int.natAbs_eq_natAbs_iff.1 hca with h | h
      · exact h
      · have h1 : g 1 0 ≠ 0 := hg.2.2
        rcases lt_or_gt_of_ne h1 with hlt | hgt
        · have : ¬ (0 < g' 1 0) := fun hp => absurd (hs.2 hp) (by omega)
          omega
        · have := hs.1 hgt
          omega
    have ha : g 0 0 = g' 0 0 := by omega
    have hd : g 1 1 = g' 1 1 := by omega
    have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = n := by rw [← Matrix.det_fin_two]; exact hg.1
    have hdet' : g' 0 0 * g' 1 1 - g' 0 1 * g' 1 0 = n := by
      rw [← Matrix.det_fin_two]; exact hg'.1
    rw [← ha, ← hd, ← hc] at hdet'
    have hb : g 0 1 = g' 0 1 := by
      apply mul_right_cancel₀ (show g 1 0 ≠ 0 from hg.2.2)
      linarith
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  refine ((summable_Gfun n).comp_injective hinj).of_nonneg_of_le (fun g => Eg_nonneg 2 g.1)
    (fun ⟨g, hg⟩ => ?_)
  obtain ⟨hdet, hsp, hc⟩ := hg
  have htr : |g 0 0 + g 1 1| ≤ 4 * n := by
    obtain ⟨r, hr⟩ := hsp
    rw [hdet] at hr
    exact abs_tr_le hn hr
  have h1 := c1_pos n hc
  have h2 := c2_pos n hc
  have hmem : (g 1 1 - g 0 0) ∈ {e : ℤ | ((c1f n g : ℕ) : ℤ) ∣ Rt n (g 0 0 + g 1 1) - e ∧
      ((c2f n g : ℕ) : ℤ) ∣ Rt n (g 0 0 + g 1 1) + e} := ⟨c1_dvd n g, c2_dvd hdet hsp hc⟩
  have hG : Gfun n (Psi n g) =
      2 * Gin (Rt n (g 0 0 + g 1 1)) ((c1f n g, c2f n g), g 1 1 - g 0 0) := if_pos htr
  have hGi : Gin (Rt n (g 0 0 + g 1 1)) ((c1f n g, c2f n g), g 1 1 - g 0 0) =
      (((c1f n g * c2f n g : ℕ) : ℝ) ^ 2 + ((g 1 1 - g 0 0 : ℤ) : ℝ) ^ 2)⁻¹ := by
    show (if 1 ≤ c1f n g ∧ 1 ≤ c2f n g then _ else 0) = _
    rw [if_pos (And.intro h1 h2)]
    exact Set.indicator_of_mem hmem _
  show Eg 2 g ≤ Gfun n (Psi n g)
  rw [hG, hGi, c1_mul_c2, Eg_two]
  have hcR : (((g 1 0).natAbs : ℕ) : ℝ) ^ 2 = (g 1 0 : ℝ) ^ 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  rw [hcR]
  push_cast
  have hc' : (g 1 0 : ℝ) ≠ 0 := by exact_mod_cast hc
  have hc2 : 0 < (g 1 0 : ℝ) ^ 2 := by positivity
  have hX : 0 < (g 1 0 : ℝ) ^ 2 + ((g 1 1 : ℝ) - g 0 0) ^ 2 :=
    add_pos_of_pos_of_nonneg hc2 (sq_nonneg _)
  have hle : ((g 1 0 : ℝ) ^ 2 + ((g 1 1 : ℝ) - g 0 0) ^ 2) / 2 ≤ N g := by
    unfold N
    nlinarith [sq_nonneg ((g 1 1 : ℝ) + g 0 0), sq_nonneg (g 0 1 : ℝ), sq_nonneg (g 1 0 : ℝ)]
  calc (N g)⁻¹ ≤ (((g 1 0 : ℝ) ^ 2 + ((g 1 1 : ℝ) - g 0 0) ^ 2) / 2)⁻¹ :=
        inv_anti₀ (div_pos hX two_pos) hle
    _ = 2 * ((g 1 0 : ℝ) ^ 2 + ((g 1 1 : ℝ) - g 0 0) ^ 2)⁻¹ := by rw [inv_div, div_eq_mul_inv]

/-- **SP summability**: `Σ_{det g = n, tr² - 4n = □} N(g)⁻¹ < ∞`. -/
theorem summable_SP {n : ℤ} (hn : 0 < n) :
    Summable ({g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ IsSP g}.indicator (Eg 2)) := by
  refine ((summable_c0 hn).add (summable_SPc hn)).of_nonneg_of_le
    (fun g => Set.indicator_nonneg (fun g _ => Eg_nonneg 2 g) g) (fun g => ?_)
  show _ ≤ _ + _
  have i1 := Set.indicator_nonneg (fun g (_ : g ∈ {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ g 1 0 = 0}) =>
    Eg_nonneg 2 g) g
  have i2 := Set.indicator_nonneg (fun g (_ : g ∈ {g : Matrix (Fin 2) (Fin 2) ℤ |
    g.det = n ∧ IsSP g ∧ g 1 0 ≠ 0}) => Eg_nonneg 2 g) g
  by_cases hA : g.det = n ∧ IsSP g
  · have e0 : {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ IsSP g}.indicator (Eg 2) g = Eg 2 g :=
      Set.indicator_of_mem (show g ∈ {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ IsSP g} from hA) _
    by_cases hc : g 1 0 = 0
    · have e1 : {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ g 1 0 = 0}.indicator (Eg 2) g = Eg 2 g :=
        Set.indicator_of_mem (show g ∈ {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ g 1 0 = 0} from
          ⟨hA.1, hc⟩) _
      linarith
    · have e2 : {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ IsSP g ∧ g 1 0 ≠ 0}.indicator (Eg 2) g =
          Eg 2 g :=
        Set.indicator_of_mem (show g ∈ {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ IsSP g ∧ g 1 0 ≠ 0}
          from ⟨hA.1, hA.2, hc⟩) _
      linarith
  · have e0 : {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ IsSP g}.indicator (Eg 2) g = 0 :=
      Set.indicator_of_notMem (show g ∉ {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ IsSP g} from hA) _
    linarith

end RamanujanPetersson.EllW2


