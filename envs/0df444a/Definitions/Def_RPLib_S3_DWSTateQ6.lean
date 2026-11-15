-- Prove2me | Definitions.Def_RPLib_S3_DWSTateQ6
-- name    : RPLib_S3_DWSTateQ6
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:28:29.488353+00:00
-- url     : https://prove2.me/theorems/bd49260e-7241-4ab6-a1b6-d07432d72241
-- title:
--   Weight-two Ramanujan-Petersson library: the ideal class group is the form class group (d, packaged)
-- statement:
--   The ideal class group is the form class group (d, packaged).
--
--   `R = QuadraticAlgebra ℤ a b`, `D = b² + 4a < 0`.
--   * `classesToPic hD : Classes D → PicQ hD`, `[f] ↦ [I_f]` (well defined and injective by `formClass_eq_iff`,
--     surjective by `exists_formIdeal_rel`).
--   * **`classesEquivPic hD : Classes D ≃ PicQ hD`**.
--   * `card_picQ_eq`, `hw_eq_card_pic`: `h_w(D) = 2 · #Pic(R) / #Rˣ`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   D. A. Cox, Primes of the Form x^2 + ny^2, 2nd ed., Wiley 2013, Sections 2, 7 and 11; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateQ5

/-!
# S3-DWS-Tate, part Q6: the ideal class group is the form class group (d, packaged)

`R = QuadraticAlgebra ℤ a b`, `D = b² + 4a < 0`.
* `classesToPic hD : Classes D → PicQ hD`, `[f] ↦ [I_f]` (well defined and injective by `formClass_eq_iff`,
  surjective by `exists_formIdeal_rel`).
* **`classesEquivPic hD : Classes D ≃ PicQ hD`**.
* `card_picQ_eq`, `hw_eq_card_pic`: `h_w(D) = 2 · #Pic(R) / #Rˣ`.
-/

set_option autoImplicit false

namespace RPLib.DWS.QA

open QuadraticAlgebra RamanujanPetersson.Hurwitz MatrixGroups

variable {a b : ℤ}

theorem orbitRel_iff_act (f g : primForms (b ^ 2 + 4 * a)) :
    MulAction.orbitRel SL(2, ℤ) (primForms (b ^ 2 + 4 * a)) f g ↔
      ∃ γ : SL(2, ℤ), act γ (f : BQF) = g := by
  rw [MulAction.orbitRel_apply]
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, ?_⟩
    have h1 : act γ⁻¹ (g : BQF) = f := congrArg Subtype.val hγ
    rw [← h1, act_act_inv]
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, Subtype.ext ?_⟩
    show act γ⁻¹ (g : BQF) = f
    rw [← hγ, act_inv_act]

/-- `[f] ↦ [I_f]`. -/
noncomputable def classesToPic (hD : b ^ 2 + 4 * a < 0) : Classes (b ^ 2 + 4 * a) → PicQ hD :=
  Quotient.lift (formClass hD) (fun f g h =>
    (formClass_eq_iff hD f g).mpr ((orbitRel_iff_act f g).mp h))

theorem classesToPic_mk (hD : b ^ 2 + 4 * a < 0) (f : primForms (b ^ 2 + 4 * a)) :
    classesToPic hD (Quotient.mk _ f) = formClass hD f := rfl

theorem classesToPic_injective (hD : b ^ 2 + 4 * a < 0) : Function.Injective (classesToPic hD) := by
  intro x y
  refine Quotient.inductionOn₂ x y (fun f g h => ?_)
  have h' : formClass hD f = formClass hD g := h
  exact Quotient.sound ((orbitRel_iff_act f g).mpr ((formClass_eq_iff hD f g).mp h'))

theorem classesToPic_surjective (hD : b ^ 2 + 4 * a < 0) : Function.Surjective (classesToPic hD) := by
  intro P
  refine Quotient.inductionOn P (fun I => ?_)
  obtain ⟨J, ν, hν, hIJ⟩ := I.2
  obtain ⟨f, hf, hrel⟩ := exists_formIdeal_rel hD hν hIJ
  refine ⟨Quotient.mk _ ⟨f, hf⟩, ?_⟩
  show formClass hD ⟨f, hf⟩ = _
  exact Quotient.sound hrel.symm

/-- **(d) The ideal class group of `R` is the form class group of discriminant `D = disc R`.** -/
noncomputable def classesEquivPic (hD : b ^ 2 + 4 * a < 0) : Classes (b ^ 2 + 4 * a) ≃ PicQ hD :=
  Equiv.ofBijective _ ⟨classesToPic_injective hD, classesToPic_surjective hD⟩

theorem classesEquivPic_mk (hD : b ^ 2 + 4 * a < 0) (f : primForms (b ^ 2 + 4 * a)) :
    classesEquivPic hD (Quotient.mk _ f) = formClass hD f := rfl

theorem card_picQ_eq (hD : b ^ 2 + 4 * a < 0) :
    Nat.card (PicQ hD) = Nat.card (Classes (b ^ 2 + 4 * a)) :=
  (Nat.card_congr (classesEquivPic hD)).symm

/-- `h_w(D) = 2 · #Pic(R) / #Rˣ`. -/
theorem hw_eq_card_pic (hD : b ^ 2 + 4 * a < 0) :
    hw (b ^ 2 + 4 * a) = 2 * Nat.card (PicQ hD) / Nat.card (QuadraticAlgebra ℤ a b)ˣ := by
  rw [card_picQ_eq hD]
  exact hw_eq_card hD

end RPLib.DWS.QA


