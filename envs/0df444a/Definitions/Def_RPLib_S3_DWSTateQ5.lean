-- Prove2me | Definitions.Def_RPLib_S3_DWSTateQ5
-- name    : RPLib_S3_DWSTateQ5
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:26:06.814233+00:00
-- url     : https://prove2.me/theorems/92992f9a-f830-4f00-8e57-11940b48d6ba
-- title:
--   Weight-two Ramanujan-Petersson library: units, stabilizers and the ideal-class / form-class bijection (d5)
-- statement:
--   Units, stabilizers and the ideal-class / form-class bijection (d5).
--
--   Pure algebra. `R = QuadraticAlgebra ℤ a b`, `D = b² + 4a < 0`.
--   * `unitsEquivStab`: `Rˣ ≃ Stab_{SL(2,ℤ)}(1, b, -a)` (`u ↦ ` the matrix of multiplication by `u`).
--   * `card_stab_eq_sD`: every primitive positive definite form of discriminant `D` has `#Stab = sD D`
--     (`4` for `D = -4`, `6` for `D = -3`, else `2`); **`card_units_eq`**: `#Rˣ = #Stab f`.
--   * `hw_eq_card`: `h_w(D) = 2 · #Classes D / #Rˣ`.
--   * `PicQ hD`: invertible ideals modulo `IdealRel`; `formClass` (`f ↦ [I_f]`), `formClass_eq_iff` (`[I_f] = [I_g] ⇔ f ~ g`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   D. A. Cox, Primes of the Form x^2 + ny^2, 2nd ed., Wiley 2013, Sections 2, 7 and 11; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateQ4

/-!
# S3-DWS-Tate, part Q5: units, stabilizers and the ideal-class / form-class bijection (d5)

Pure algebra. `R = QuadraticAlgebra ℤ a b`, `D = b² + 4a < 0`.
* `unitsEquivStab`: `Rˣ ≃ Stab_{SL(2,ℤ)}(1, b, -a)` (`u ↦ ` the matrix of multiplication by `u`).
* `card_stab_eq_sD`: every primitive positive definite form of discriminant `D` has `#Stab = sD D`
  (`4` for `D = -4`, `6` for `D = -3`, else `2`); **`card_units_eq`**: `#Rˣ = #Stab f`.
* `hw_eq_card`: `h_w(D) = 2 · #Classes D / #Rˣ`.
* `PicQ hD`: invertible ideals modulo `IdealRel`; `formClass` (`f ↦ [I_f]`), `formClass_eq_iff` (`[I_f] = [I_g] ⇔ f ~ g`).
-/

set_option autoImplicit false

namespace RPLib.DWS.QA

open QuadraticAlgebra RamanujanPetersson.Hurwitz MatrixGroups

variable {a b : ℤ}

/-- The principal form `(1, b, -a)` of discriminant `b² + 4a`. -/
def princF (a b : ℤ) : BQF := ⟨1, b, -a⟩

theorem princF_mem (hD : b ^ 2 + 4 * a < 0) : princF a b ∈ primForms (b ^ 2 + 4 * a) := by
  refine ⟨?_, ⟨one_pos, ?_⟩, ?_⟩
  · show b ^ 2 - 4 * 1 * (-a) = b ^ 2 + 4 * a; ring
  · show b ^ 2 - 4 * 1 * (-a) < 0; linarith
  · show Int.gcd 1 (Int.gcd b (-a)) = 1
    exact Int.gcd_one_left _

theorem norm_eq_one_of_isUnit (hD : b ^ 2 + 4 * a < 0) {u : QuadraticAlgebra ℤ a b} (hu : IsUnit u) :
    u.norm = 1 := by
  rcases Int.isUnit_iff.mp (isUnit_iff_norm_isUnit.mp hu) with h | h
  · exact h
  · have := norm_nonneg hD u; omega

/-- The matrix of multiplication by a norm-one `u` in the basis `(1, ω - b)`. -/
def unitMat (u : QuadraticAlgebra ℤ a b) (h : u.norm = 1) : SL(2, ℤ) :=
  ⟨!![u.re + b * u.im, -a * u.im; -u.im, u.re], by
    rw [Matrix.det_fin_two_of]; rw [norm_def] at h; linear_combination h⟩

theorem unitMat_00 (u : QuadraticAlgebra ℤ a b) (h : u.norm = 1) : unitMat u h 0 0 = u.re + b * u.im := rfl
theorem unitMat_01 (u : QuadraticAlgebra ℤ a b) (h : u.norm = 1) : unitMat u h 0 1 = -a * u.im := rfl
theorem unitMat_10 (u : QuadraticAlgebra ℤ a b) (h : u.norm = 1) : unitMat u h 1 0 = -u.im := rfl
theorem unitMat_11 (u : QuadraticAlgebra ℤ a b) (h : u.norm = 1) : unitMat u h 1 1 = u.re := rfl

theorem act_unitMat (u : QuadraticAlgebra ℤ a b) (h : u.norm = 1) :
    act (unitMat u h) (princF a b) = princF a b := by
  have h' := h
  rw [norm_def] at h'
  apply BQF.ext
  · show 1 * (u.re + b * u.im) ^ 2 + b * (u.re + b * u.im) * (-u.im) + (-a) * (-u.im) ^ 2 = 1
    linear_combination h'
  · show 2 * 1 * (u.re + b * u.im) * (-a * u.im) +
        b * ((u.re + b * u.im) * u.re + (-a * u.im) * (-u.im)) + 2 * (-a) * (-u.im) * u.re = b
    linear_combination b * h'
  · show 1 * (-a * u.im) ^ 2 + b * (-a * u.im) * u.re + (-a) * u.re ^ 2 = -a
    linear_combination (-a) * h'

/-- An element of the stabilizer of `(1, b, -a)` is the matrix of a norm-one element. -/
theorem stab_entries {γ : SL(2, ℤ)} (hγ : act γ (princF a b) = princF a b) :
    γ 0 0 = γ 1 1 - b * γ 1 0 ∧ γ 0 1 = a * γ 1 0 := by
  have h0 : HasForm ((1 : ℤ) : QuadraticAlgebra ℤ a b) ⟨-b, 1⟩ (princF a b) := by
    have h := hasForm_lat (a := a) (b := b) (A := 1) (k := b) (C := -a) (by ring)
    have e : (⟨1, 2 * b - b, -a⟩ : BQF) = princF a b :=
      BQF.ext rfl (by show 2 * b - b = b; ring) rfl
    rwa [e] at h
  have h1 := h0.act γ
  rw [hγ] at h1
  have hd : dt ((1 : ℤ) : QuadraticAlgebra ℤ a b) ⟨-b, 1⟩ = 1 := dt_lat 1 b
  have hd' : dt (lin (γ 0 0) (-γ 1 0) ((1 : ℤ) : QuadraticAlgebra ℤ a b) ⟨-b, 1⟩)
      (lin (-γ 0 1) (γ 1 1) ((1 : ℤ) : QuadraticAlgebra ℤ a b) ⟨-b, 1⟩) = 1 := by
    rw [dt_lin, hd]; linear_combination det_eq γ
  have key := h0.mul_eq h1 (by show (1 : ℤ) ≠ 0; norm_num) (by rw [hd]; norm_num)
    (by rw [hd']; norm_num)
  have kre := congrArg QuadraticAlgebra.re key
  have kim := congrArg QuadraticAlgebra.im key
  simp only [lin, re_mul, im_mul, re_intCast, im_intCast, Int.cast_id] at kre kim
  constructor
  · linear_combination kim
  · linear_combination kre + b * kim

theorem norm_stab {γ : SL(2, ℤ)} (hγ : act γ (princF a b) = princF a b) :
    (⟨γ 1 1, -γ 1 0⟩ : QuadraticAlgebra ℤ a b).norm = 1 := by
  obtain ⟨e1, e2⟩ := stab_entries hγ
  rw [norm_def]
  show γ 1 1 * γ 1 1 + b * γ 1 1 * (-γ 1 0) - a * (-γ 1 0) * (-γ 1 0) = 1
  have hdet := det_eq γ
  rw [e1, e2] at hdet
  linear_combination hdet

/-- **Units are the stabilizer of the principal form.** -/
noncomputable def unitsEquivStab (hD : b ^ 2 + 4 * a < 0) :
    (QuadraticAlgebra ℤ a b)ˣ ≃ MulAction.stabilizer SL(2, ℤ) (princF a b) where
  toFun u := ⟨unitMat (u : QuadraticAlgebra ℤ a b) (norm_eq_one_of_isUnit hD u.isUnit),
    (mem_stabilizer_iff_act _ _).mpr (act_unitMat _ _)⟩
  invFun γ := (isUnit_iff_norm_isUnit.mpr (by
    rw [norm_stab ((mem_stabilizer_iff_act _ _).mp γ.2)]; exact isUnit_one)).unit
  left_inv u := by
    apply Units.ext
    rw [IsUnit.unit_spec]
    ext
    · rfl
    · show -(-(u : QuadraticAlgebra ℤ a b).im) = (u : QuadraticAlgebra ℤ a b).im
      ring
  right_inv γ := by
    obtain ⟨e1, e2⟩ := stab_entries ((mem_stabilizer_iff_act _ _).mp γ.2)
    apply Subtype.ext
    apply ent_injective
    show (_, _, _, _) = ((γ : SL(2, ℤ)) 0 0, (γ : SL(2, ℤ)) 0 1, (γ : SL(2, ℤ)) 1 0, (γ : SL(2, ℤ)) 1 1)
    rw [unitMat_00, unitMat_01, unitMat_10, unitMat_11, IsUnit.unit_spec, e1, e2]
    simp only [Prod.mk.injEq, and_true]
    refine ⟨?_, ?_, ?_⟩
    · show (γ : SL(2, ℤ)) 1 1 + b * -(γ : SL(2, ℤ)) 1 0 = (γ : SL(2, ℤ)) 1 1 - b * (γ : SL(2, ℤ)) 1 0
      ring
    · show -a * -(γ : SL(2, ℤ)) 1 0 = a * (γ : SL(2, ℤ)) 1 0
      ring
    · show -(-(γ : SL(2, ℤ)) 1 0) = (γ : SL(2, ℤ)) 1 0
      ring

/-- The order of the stabilizer of a primitive positive definite form of discriminant `D`. -/
def sD (D : ℤ) : ℕ := if D = -4 then 4 else if D = -3 then 6 else 2

theorem red_m4 {A B C : ℤ} (ha : 0 < A) (h1 : -A < B) (h2 : B ≤ A) (h3 : A ≤ C)
    (hD : B * B - 4 * A * C = -4) : B = 0 ∧ A = C := by
  have hA : A ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left h3 ha.le,
      mul_nonneg (sub_nonneg.mpr h2) (by linarith : (0 : ℤ) ≤ A + B)]
  have hA1 : A = 1 := by omega
  subst hA1
  rcases (show B = 0 ∨ B = 1 by omega) with rfl | rfl <;> omega

theorem red_m3 {A B C : ℤ} (ha : 0 < A) (h1 : -A < B) (h2 : B ≤ A) (h3 : A ≤ C)
    (hD : B * B - 4 * A * C = -3) : A = B ∧ B = C := by
  have hA : A ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left h3 ha.le,
      mul_nonneg (sub_nonneg.mpr h2) (by linarith : (0 : ℤ) ≤ A + B)]
  have hA1 : A = 1 := by omega
  subst hA1
  rcases (show B = 0 ∨ B = 1 by omega) with rfl | rfl <;> omega

theorem a_eq_one_of_dvd {r : BQF} (hp : r.IsPrimitive) (ha : 0 < r.a) (hb : r.a ∣ r.b)
    (hc : r.a ∣ r.c) : r.a = 1 := by
  have e : ((r.a.toNat : ℕ) : ℤ) = r.a := Int.toNat_of_nonneg ha.le
  have h := r.dvd_content (d := r.a.toNat) (by rw [e]) (by rw [e]; exact hb) (by rw [e]; exact hc)
  rw [show r.content = 1 from hp, Nat.dvd_one] at h
  rw [← e, h]; rfl

theorem card_stab_eq_sD {D : ℤ} {f : BQF} (hf : f ∈ primForms D) :
    Nat.card (MulAction.stabilizer SL(2, ℤ) f) = sD D := by
  obtain ⟨γ, hγ⟩ := exists_act_isReduced f hf.2.1
  rw [← card_stabilizer_act γ f, card_stabilizer_of_isReduced hγ]
  have hrd : (act γ f).disc = D := (disc_act γ f).trans hf.1
  have hrp : (act γ f).IsPrimitive := (isPrimitive_act_iff γ f).mpr hf.2.2
  generalize act γ f = r at hγ hrd hrp
  have ha := hγ.a_pos
  obtain ⟨h1, h2, h3, -⟩ := hγ
  have hdisc : r.b * r.b - 4 * r.a * r.c = D := by rw [← hrd]; unfold BQF.disc; ring
  have k4 : (r.b = 0 ∧ r.a = r.c) ↔ D = -4 := by
    constructor
    · intro hb
      have := a_eq_one_of_dvd hrp ha (by rw [hb.1]; exact dvd_zero _) (dvd_of_eq hb.2)
      rw [← hdisc, hb.1, ← hb.2, this]; norm_num
    · intro hd; rw [hd] at hdisc; exact red_m4 ha h1 h2 h3 hdisc
  have k3 : (r.a = r.b ∧ r.b = r.c) ↔ D = -3 := by
    constructor
    · intro hc
      have := a_eq_one_of_dvd hrp ha (dvd_of_eq hc.1) (dvd_of_eq (hc.1.trans hc.2))
      rw [← hdisc, ← hc.2, ← hc.1, this]; norm_num
    · intro hd; rw [hd] at hdisc; exact red_m3 ha h1 h2 h3 hdisc
  unfold sD
  simp only [k4, k3]

theorem card_units_eq_sD (hD : b ^ 2 + 4 * a < 0) :
    Nat.card (QuadraticAlgebra ℤ a b)ˣ = sD (b ^ 2 + 4 * a) := by
  rw [Nat.card_congr (unitsEquivStab hD), card_stab_eq_sD (princF_mem hD)]

/-- **(d5, units)** `#Rˣ = #Stab_{SL(2,ℤ)}(f)` for every primitive positive definite `f` of discriminant `D`. -/
theorem card_units_eq (hD : b ^ 2 + 4 * a < 0) {f : BQF} (hf : f ∈ primForms (b ^ 2 + 4 * a)) :
    Nat.card (QuadraticAlgebra ℤ a b)ˣ = Nat.card (MulAction.stabilizer SL(2, ℤ) f) := by
  rw [card_units_eq_sD hD, card_stab_eq_sD hf]

theorem sD_pos (D : ℤ) : 0 < sD D := by unfold sD; split_ifs <;> norm_num

/-- `h_w(D) = 2 · #Classes D / #Rˣ`. -/
theorem hw_eq_card (hD : b ^ 2 + 4 * a < 0) :
    hw (b ^ 2 + 4 * a) =
      2 * Nat.card (Classes (b ^ 2 + 4 * a)) / Nat.card (QuadraticAlgebra ℤ a b)ˣ := by
  have hc : ∀ C : Classes (b ^ 2 + 4 * a),
      (2 : ℚ) / Nat.card (MulAction.stabilizer SL(2, ℤ) (C.out : BQF)) =
        2 / Nat.card (QuadraticAlgebra ℤ a b)ˣ := fun C => by
    rw [card_units_eq hD C.out.2]
  unfold hw
  simp_rw [hc]
  letI := Fintype.ofFinite (Classes (b ^ 2 + 4 * a))
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card (α := Classes (b ^ 2 + 4 * a))]
  ring

/-! ### Ideal classes -/

/-- Invertible ideals: `I J = (ν)` for some ideal `J` and `ν ≠ 0`. -/
def InvIdeal (a b : ℤ) : Type :=
  {I : Ideal (QuadraticAlgebra ℤ a b) // ∃ J : Ideal (QuadraticAlgebra ℤ a b), ∃ ν, ν ≠ 0 ∧
    I * J = Ideal.span {ν}}

/-- `IdealRel` on invertible ideals. -/
def picSetoid (hD : b ^ 2 + 4 * a < 0) : Setoid (InvIdeal a b) where
  r I J := IdealRel I.1 J.1
  iseqv := ⟨fun I => IdealRel.refl I.1, fun h => h.symm, fun h h' => h.trans hD h'⟩

/-- The ideal class group of `R`, as invertible ideals modulo `(α) I = (β) J`. -/
def PicQ (hD : b ^ 2 + 4 * a < 0) : Type := Quotient (picSetoid hD)

theorem formIdeal_inv {f : BQF} (hf : f ∈ primForms (b ^ 2 + 4 * a)) :
    ∃ J : Ideal (QuadraticAlgebra ℤ a b), ∃ ν, ν ≠ 0 ∧ formIdeal f * J = Ideal.span {ν} :=
  ⟨_, _, intCast_ne_zero' (ne_of_gt hf.2.1.1), formIdeal_mul_conj hf.1 hf.2.2⟩

/-- The class of `I_f`. -/
def formClass (hD : b ^ 2 + 4 * a < 0) (f : primForms (b ^ 2 + 4 * a)) : PicQ hD :=
  Quotient.mk (picSetoid hD) ⟨formIdeal (f : BQF), formIdeal_inv f.2⟩

theorem formClass_eq_iff (hD : b ^ 2 + 4 * a < 0) (f g : primForms (b ^ 2 + 4 * a)) :
    formClass hD f = formClass hD g ↔ ∃ γ : SL(2, ℤ), act γ (f : BQF) = g := by
  constructor
  · intro h
    exact (idealRel_iff hD f.2 g.2).mp (Quotient.exact h)
  · intro h
    exact Quotient.sound ((idealRel_iff hD f.2 g.2).mpr h)

end RPLib.DWS.QA


