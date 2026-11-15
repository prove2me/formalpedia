-- Prove2me | Definitions.Def_RPLib_S3_HurwitzB
-- name    : RPLib_S3_HurwitzB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:20:20.607211+00:00
-- url     : https://prove2.me/theorems/f6f5a67f-96d2-4c9e-8c40-af1f5a2a67f2
-- title:
--   Weight-two Ramanujan-Petersson library: Weighted and Hurwitz class numbers
-- statement:
--   Weighted and Hurwitz class numbers.
--
--   * `primForms D`: primitive positive definite forms of discriminant `D` (a `SubMulAction`), `Classes D` their
--     `SL(2, ℤ)`-classes (finite: `finite_classes`).
--   * `hw D = ∑ᶠ classes, 2 / #Stab` (weighted class number `h_w(D)`); computable `hw6 D = 6 h_w(D)` as a sum over
--     reduced primitive forms, `hw_eq : hw D = hw6 D / 6`.
--   * Hurwitz class number `H N` (`H 0 = -1/12`, `H N = ∑_{f ≥ 1, f² ∣ N} h_w(-N/f²)`), `H_eq : H N = H6 N / 6`,
--     `H_eq_zero` for `N ≡ 1, 2 mod 4`, small values by `decide` on `H6` (no native evaluation).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   D. A. Cox, Primes of the Form x^2 + ny^2, 2nd ed., Wiley 2013, Sections 2, 7 and 11; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211

import Mathlib
import Definitions.Def_RPLib_S3_HurwitzA

/-!
# Weighted and Hurwitz class numbers (RP project, unit S3-Hurwitz, part B)

* `primForms D`: primitive positive definite forms of discriminant `D` (a `SubMulAction`), `Classes D` their
  `SL(2, ℤ)`-classes (finite: `finite_classes`).
* `hw D = ∑ᶠ classes, 2 / #Stab` (weighted class number `h_w(D)`); computable `hw6 D = 6 h_w(D)` as a sum over
  reduced primitive forms, `hw_eq : hw D = hw6 D / 6`.
* Hurwitz class number `H N` (`H 0 = -1/12`, `H N = ∑_{f ≥ 1, f² ∣ N} h_w(-N/f²)`), `H_eq : H N = H6 N / 6`,
  `H_eq_zero` for `N ≡ 1, 2 mod 4`, small values by `decide` on `H6` (no native evaluation).
-/

set_option autoImplicit false

namespace RamanujanPetersson.Hurwitz

open Matrix MatrixGroups BQF

/-- Primitive positive definite forms of discriminant `D`. -/
def primForms (D : ℤ) : SubMulAction SL(2, ℤ) BQF where
  carrier := {f | f.disc = D ∧ f.PosDef ∧ f.IsPrimitive}
  smul_mem' γ f hf := ⟨(disc_smul γ f).trans hf.1, (posDef_smul_iff γ f).2 hf.2.1,
    (isPrimitive_smul_iff γ f).2 hf.2.2⟩

theorem mem_primForms {D : ℤ} {f : BQF} :
    f ∈ primForms D ↔ f.disc = D ∧ f.PosDef ∧ f.IsPrimitive := Iff.rfl

/-- `SL(2, ℤ)`-classes of primitive positive definite forms of discriminant `D`. -/
abbrev Classes (D : ℤ) : Type := MulAction.orbitRel.Quotient SL(2, ℤ) (primForms D)

/-- The weighted class number `h_w(D) = ∑ over classes of 2 / #Stab` (stabilizer in `SL(2, ℤ)`). -/
noncomputable def hw (D : ℤ) : ℚ :=
  ∑ᶠ C : Classes D, (2 : ℚ) / Nat.card (MulAction.stabilizer SL(2, ℤ) (C.out : BQF))

/-- `6 · (2 / #Stab)` for a reduced form. -/
def redWeight6 (f : BQF) : ℕ :=
  if f.b = 0 ∧ f.a = f.c then 3 else if f.a = f.b ∧ f.b = f.c then 2 else 6

/-- Reduced primitive forms of discriminant `D`. -/
def redPrim (D : ℤ) : Finset BQF := (reducedForms D).filter IsPrimitive

/-- `6 h_w(D)`, computably. -/
def hw6 (D : ℤ) : ℕ := ∑ f ∈ redPrim D, redWeight6 f

theorem redWeight6_sanity : redWeight6 ⟨1, 0, 1⟩ = 3 ∧ redWeight6 ⟨1, 1, 1⟩ = 2 ∧
    redWeight6 ⟨2, 1, 3⟩ = 6 := by decide

theorem redPrim_sanity : redPrim (-12) = {⟨1, 0, 3⟩} ∧ redPrim (-28) = {⟨1, 0, 7⟩} := by decide

theorem mem_redPrim {D : ℤ} {f : BQF} :
    f ∈ redPrim D ↔ f.disc = D ∧ f.IsReduced ∧ f.IsPrimitive := by
  simp only [redPrim, Finset.mem_filter, mem_reducedForms, and_assoc]

/-- A reduced primitive form as an element of `primForms D`. -/
def toPrim (D : ℤ) (f : redPrim D) : primForms D :=
  ⟨f.1, by obtain ⟨h1, h2, h3⟩ := mem_redPrim.1 f.2; exact ⟨h1, h2.posDef, h3⟩⟩

/-- The class of a reduced primitive form. -/
def toClass (D : ℤ) (f : redPrim D) : Classes D := Quotient.mk'' (toPrim D f)

/-- Classes are in bijection with reduced primitive forms. -/
theorem toClass_bijective (D : ℤ) : Function.Bijective (toClass D) := by
  constructor
  · rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.1 (Quotient.eq''.1 h)
    have horb : f ∈ MulAction.orbit SL(2, ℤ) g :=
      ⟨γ, by simpa [toPrim, SubMulAction.val_smul] using congrArg Subtype.val hγ⟩
    exact Subtype.ext ((mem_redPrim.1 hg).2.1.eq_of_mem_orbit (mem_redPrim.1 hf).2.1 horb)
  · intro C
    induction C using Quotient.inductionOn' with
    | h x =>
    obtain ⟨hD, hpos, hprim⟩ := x.2
    obtain ⟨γ, hγ⟩ := exists_act_isReduced x.1 hpos
    have hmem : act γ x.1 ∈ redPrim D :=
      mem_redPrim.2 ⟨(disc_act γ _).trans hD, hγ, (isPrimitive_act_iff γ _).2 hprim⟩
    refine ⟨⟨act γ x.1, hmem⟩, Quotient.eq''.2 (MulAction.orbitRel_apply.2 ⟨γ⁻¹, ?_⟩)⟩
    exact Subtype.ext (by rw [SubMulAction.val_smul]; exact (act_eq_smul γ x.1).symm)

instance finite_classes (D : ℤ) : Finite (Classes D) :=
  Finite.of_surjective _ (toClass_bijective D).2

theorem card_stab_out (D : ℤ) (f : redPrim D) :
    Nat.card (MulAction.stabilizer SL(2, ℤ) ((toClass D f).out : BQF)) =
      Nat.card (MulAction.stabilizer SL(2, ℤ) (f : BQF)) := by
  obtain ⟨γ, hγ⟩ := (MulAction.orbitRel_apply (G := SL(2, ℤ)) (α := primForms D)).1
    (Quotient.mk_out' (s₁ := MulAction.orbitRel SL(2, ℤ) (primForms D)) (toPrim D f))
  have hb : ((toClass D f).out : BQF) = γ • (f : BQF) := by
    show ((Quotient.mk'' (toPrim D f) : Classes D).out : BQF) = γ • (f : BQF)
    rw [← hγ]; rfl
  exact (Nat.card_congr (MulAction.stabilizerEquivStabilizer hb).toEquiv).symm

theorem two_div_card_eq {f : BQF} (hf : f.IsReduced) :
    (2 : ℚ) / Nat.card (MulAction.stabilizer SL(2, ℤ) f) = (redWeight6 f : ℚ) / 6 := by
  rw [card_stabilizer_of_isReduced hf]
  unfold redWeight6
  split_ifs <;> norm_num

/-- `h_w(D) = hw6 D / 6`. -/
theorem hw_eq (D : ℤ) : hw D = (hw6 D : ℚ) / 6 := by
  unfold hw
  rw [← finsum_comp_equiv (Equiv.ofBijective _ (toClass_bijective D)), finsum_eq_sum_of_fintype]
  simp only [Equiv.ofBijective_apply, card_stab_out]
  rw [hw6, Nat.cast_sum, Finset.sum_div, ← Finset.sum_coe_sort (redPrim D)]
  exact Finset.sum_congr rfl (fun f _ => two_div_card_eq (mem_redPrim.1 f.2).2.1)

theorem hw6_eq_zero_of_emod {D : ℤ} (hD : D % 4 = 2 ∨ D % 4 = 3) : hw6 D = 0 := by
  apply Finset.sum_eq_zero
  intro f hf
  exfalso
  obtain ⟨h1, -, -⟩ := mem_redPrim.1 hf
  have := f.disc_emod_four
  omega

theorem hw6_eq_zero_of_nonneg {D : ℤ} (hD : 0 ≤ D) : hw6 D = 0 := by
  apply Finset.sum_eq_zero
  intro f hf
  exfalso
  obtain ⟨h1, h2, -⟩ := mem_redPrim.1 hf
  have := h2.disc_neg
  omega

theorem hw_sanity : hw (-3) = 1 / 3 ∧ hw (-4) = 1 / 2 ∧ hw (-23) = 3 ∧ hw (-12) = 1 ∧ hw (-7) = 1 := by
  simp only [hw_eq, show hw6 (-3) = 2 by decide, show hw6 (-4) = 3 by decide,
    show hw6 (-23) = 18 by decide, show hw6 (-12) = 6 by decide, show hw6 (-7) = 6 by decide]
  norm_num

/-- The Hurwitz class number: `H 0 = -1/12`, `H N = ∑_{f ≥ 1, f² ∣ N} h_w(-N/f²)` for `N ≥ 1`. -/
noncomputable def H (N : ℕ) : ℚ :=
  if N = 0 then -1 / 12 else
    ∑ f ∈ (Finset.Icc 1 N).filter (fun f => f ^ 2 ∣ N), hw (-((N / f ^ 2 : ℕ) : ℤ))

/-- `6 H(N)` for `N ≥ 1`, computably. -/
def H6 (N : ℕ) : ℕ :=
  ∑ f ∈ (Finset.Icc 1 N).filter (fun f => f ^ 2 ∣ N), hw6 (-((N / f ^ 2 : ℕ) : ℤ))

theorem H_zero : H 0 = -1 / 12 := by simp [H]

theorem H_eq {N : ℕ} (hN : N ≠ 0) : H N = (H6 N : ℚ) / 6 := by
  simp only [H, hN, if_false, H6, Nat.cast_sum, Finset.sum_div, hw_eq]

theorem H_of_H6 {N m : ℕ} (hN : N ≠ 0) (h : H6 N = m) : H N = (m : ℚ) / 6 := by
  rw [H_eq hN, h]

theorem sq_emod_four (f : ℕ) : f ^ 2 % 4 = 0 ∨ f ^ 2 % 4 = 1 := by
  rcases Nat.even_or_odd f with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · left; ring_nf; omega
  · right; ring_nf; omega

theorem H6_eq_zero {N : ℕ} (hN : N % 4 = 1 ∨ N % 4 = 2) : H6 N = 0 := by
  apply Finset.sum_eq_zero
  intro f hf
  obtain ⟨hf1, hdvd⟩ := Finset.mem_filter.1 hf
  apply hw6_eq_zero_of_emod
  obtain ⟨M, hM⟩ := hdvd
  have hpos : 0 < f ^ 2 := by have := (Finset.mem_Icc.1 hf1).1; positivity
  have hmod : N % 4 = (f ^ 2 % 4) * (M % 4) % 4 := by rw [hM, Nat.mul_mod]
  rw [hM, Nat.mul_div_cancel_left _ hpos]
  rcases sq_emod_four f with h | h <;> rw [h] at hmod <;> omega

/-- `H(N) = 0` unless `N ≡ 0, 3 mod 4`. -/
theorem H_eq_zero {N : ℕ} (hN : N % 4 = 1 ∨ N % 4 = 2) : H N = 0 := by
  rw [H_eq (by omega), H6_eq_zero hN]; simp

theorem H6_values : H6 3 = 2 ∧ H6 4 = 3 ∧ H6 7 = 6 ∧ H6 8 = 6 ∧ H6 11 = 6 ∧ H6 12 = 8 ∧
    H6 15 = 12 ∧ H6 16 = 9 ∧ H6 19 = 6 ∧ H6 20 = 12 ∧ H6 23 = 18 ∧ H6 24 = 12 ∧ H6 27 = 8 ∧
    H6 28 = 12 := by decide

theorem H_three : H 3 = 1 / 3 := by rw [H_of_H6 (by norm_num) H6_values.1]; norm_num
theorem H_four : H 4 = 1 / 2 := by rw [H_of_H6 (by norm_num) H6_values.2.1]; norm_num
theorem H_seven : H 7 = 1 := by rw [H_of_H6 (by norm_num) H6_values.2.2.1]; norm_num
theorem H_eight : H 8 = 1 := by rw [H_of_H6 (by norm_num) H6_values.2.2.2.1]; norm_num
theorem H_eleven : H 11 = 1 := by rw [H_of_H6 (by norm_num) H6_values.2.2.2.2.1]; norm_num
theorem H_twelve : H 12 = 4 / 3 := by rw [H_of_H6 (by norm_num) H6_values.2.2.2.2.2.1]; norm_num
theorem H_fifteen : H 15 = 2 := by rw [H_of_H6 (by norm_num) H6_values.2.2.2.2.2.2.1]; norm_num
theorem H_sixteen : H 16 = 3 / 2 := by rw [H_of_H6 (by norm_num) H6_values.2.2.2.2.2.2.2.1]; norm_num
theorem H_twentythree : H 23 = 3 := by
  rw [H_of_H6 (by norm_num) (show H6 23 = 18 by decide)]; norm_num
theorem H_twentyseven : H 27 = 4 / 3 := by
  rw [H_of_H6 (by norm_num) (show H6 27 = 8 by decide)]; norm_num
theorem H_one : H 1 = 0 := H_eq_zero (by norm_num)
theorem H_two : H 2 = 0 := H_eq_zero (by norm_num)

end RamanujanPetersson.Hurwitz


