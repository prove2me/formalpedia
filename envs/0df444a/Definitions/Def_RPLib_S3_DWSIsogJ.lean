-- Prove2me | Definitions.Def_RPLib_S3_DWSIsogJ
-- name    : RPLib_S3_DWSIsogJ
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:43:34.356505+00:00
-- url     : https://prove2.me/theorems/e0b09415-dc0b-4c9d-bc2e-fcb9b68a8775
-- title:
--   Weight-two Ramanujan-Petersson library: regularity of the addition law on `W'(L(E))`
-- statement:
--   Regularity of the addition law on `W'(L(E))`.
--
--   * `pole_alg` : `addX - x₂ = N / (x₁ - x₂)²` with `N` linear in `x₁, y₁` (uses the equation of `(x₁, y₁)`).
--   * **`ge_add_pole`** : if `x₁` has a double pole, `y₁` at most a triple pole and `x₂, y₂` are regular at `P`,
--     then the coordinates of `(x₁, y₁) + (x₂, y₂)` are regular at `P` (any `P`, also `O`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSIsogI

/-!
# S3-DWS-Isog, part J: regularity of the addition law on `W'(L(E))`

* `pole_alg` : `addX - x₂ = N / (x₁ - x₂)²` with `N` linear in `x₁, y₁` (uses the equation of `(x₁, y₁)`).
* **`ge_add_pole`** : if `x₁` has a double pole, `y₁` at most a triple pole and `x₂, y₂` are regular at `P`,
  then the coordinates of `(x₁, y₁) + (x₂, y₂)` are regular at `P` (any `P`, also `O`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open IsDedekindDomain
open scoped nonZeroDivisors

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

/-- The addition law near a pole of the first point (pure algebra). -/
lemma pole_alg {K : Type*} [Field K] {a₁ a₂ a₃ a₄ a₆ x₁ y₁ x₂ y₂ : K} (hd : x₁ - x₂ ≠ 0)
    (e : y₁ ^ 2 + a₁ * x₁ * y₁ + a₃ * y₁ = x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁ + a₆) :
    ((y₁ - y₂) / (x₁ - x₂)) ^ 2 + a₁ * ((y₁ - y₂) / (x₁ - x₂)) - a₂ - x₁ - x₂ =
      x₂ + (-y₁ * (2 * y₂ + a₁ * x₂ + a₃) + x₁ * (3 * x₂ ^ 2 + 2 * a₂ * x₂ + a₄ - a₁ * y₂) +
        (a₆ + y₂ ^ 2 + a₁ * x₂ * y₂ - 2 * x₂ ^ 3 - a₂ * x₂ ^ 2)) * (x₁ - x₂)⁻¹ ^ 2 := by
  have hid : (x₁ - x₂) * (x₁ - x₂)⁻¹ = 1 := mul_inv_cancel₀ hd
  rw [div_eq_mul_inv]
  linear_combination ((a₂ + x₁ + 2 * x₂) * (1 + (x₁ - x₂) * (x₁ - x₂)⁻¹) -
    a₁ * (y₁ - y₂) * (x₁ - x₂)⁻¹) * hid + (x₁ - x₂)⁻¹ ^ 2 * e

/-- `negAddY` in terms of the second point. -/
lemma negAddY_alg {K : Type*} [Field K] {x₁ y₁ x₂ y₂ X : K} (hd : x₁ - x₂ ≠ 0) :
    (y₁ - y₂) / (x₁ - x₂) * (X - x₁) + y₁ = (y₁ - y₂) * (x₁ - x₂)⁻¹ * (X - x₂) + y₂ := by
  have hid : (x₁ - x₂) * (x₁ - x₂)⁻¹ = 1 := mul_inv_cancel₀ hd
  rw [div_eq_mul_inv]
  linear_combination (-(y₁ - y₂)) * hid

section Pole

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {W' : WeierstrassCurve F}

lemma eqn_FF {x y : FF W L} (h : (W'.baseChange (FF W L)).toAffine.Equation x y) :
    y ^ 2 + algebraMap L (FF W L) (W'.baseChange L).toAffine.a₁ * x * y +
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₃ * y =
    x ^ 3 + algebraMap L (FF W L) (W'.baseChange L).toAffine.a₂ * x ^ 2 +
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₄ * x +
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₆ := by
  have e := (equation_iff _ _).mp h
  rwa [bc_a₁ W' L (FF W L), bc_a₂ W' L (FF W L), bc_a₃ W' L (FF W L), bc_a₄ W' L (FF W L),
    bc_a₆ W' L (FF W L)] at e

lemma Ge.mul0 {f g : FF W L} {P : Pt W L} (hf : Ge 0 f P) (hg : Ge 0 g P) : Ge 0 (f * g) P :=
  (hf.mul hg).mono (by norm_num)

lemma Ge.sq0 {f : FF W L} {P : Pt W L} (hf : Ge 0 f P) : Ge 0 (f ^ 2) P :=
  (hf.pow 2).mono (by norm_num)

/-- **Pole case of the addition law.** -/
theorem ge_add_pole {x₁ y₁ x₂ y₂ : FF W L} (h₁ : (W'.baseChange (FF W L)).toAffine.Equation x₁ y₁)
    {P : Pt W L} (hx₁ : x₁ ≠ 0) (ho : ord W L x₁ P = -2) (hy₁ : Ge (-3) y₁ P)
    (hx₂ : Ge 0 x₂ P) (hy₂ : Ge 0 y₂ P) :
    x₁ ≠ x₂ ∧ Ge 0 ((W'.baseChange (FF W L)).toAffine.addX x₁ x₂ ((y₁ - y₂) / (x₁ - x₂))) P ∧
      Ge 0 ((W'.baseChange (FF W L)).toAffine.addY x₁ x₂ y₁ ((y₁ - y₂) / (x₁ - x₂))) P := by
  obtain ⟨hd0, hdo⟩ : x₁ - x₂ ≠ 0 ∧ ord W L (x₁ - x₂) P = -2 := by
    rw [sub_eq_add_neg]; exact ge_lead hx₁ ho (hx₂.neg.mono (by norm_num))
  have hio : Ge 2 (x₁ - x₂)⁻¹ P := Or.inr (by rw [ord_inv, hdo]; norm_num)
  have hc : ∀ a : L, Ge 0 (algebraMap L (FF W L) a) P := fun a => Ge.const a P
  have hX := pole_alg (y₂ := y₂) hd0 (eqn_FF h₁)
  have hk2 : Ge 0 (2 * y₂ + algebraMap L (FF W L) (W'.baseChange L).toAffine.a₁ * x₂ +
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₃) P :=
    (((Ge.ofNat 2 P).mul0 hy₂).add ((hc _).mul0 hx₂)).add (hc _)
  have hk1 : Ge 0 (3 * x₂ ^ 2 + 2 * algebraMap L (FF W L) (W'.baseChange L).toAffine.a₂ * x₂ +
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₄ -
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₁ * y₂) P :=
    ((((Ge.ofNat 3 P).mul0 hx₂.sq0).add (((Ge.ofNat 2 P).mul0 (hc _)).mul0 hx₂)).add (hc _)).sub
      ((hc _).mul0 hy₂)
  have hk0 : Ge 0 (algebraMap L (FF W L) (W'.baseChange L).toAffine.a₆ + y₂ ^ 2 +
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₁ * x₂ * y₂ - 2 * x₂ ^ 3 -
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₂ * x₂ ^ 2) P :=
    ((((hc _).add hy₂.sq0).add (((hc _).mul0 hx₂).mul0 hy₂)).sub
      ((Ge.ofNat 2 P).mul0 ((hx₂.pow 3).mono (by norm_num)))).sub ((hc _).mul0 hx₂.sq0)
  have hN := (((hy₁.neg.mul hk2).mono (by norm_num : (-3 : ℤ) ≤ -3 + 0)).add
    ((Ge.mul (Or.inr ho.ge) hk1).mono (by norm_num))).add (hk0.mono (by norm_num))
  have hNi := (hN.mul (hio.pow 2)).mono (by norm_num : (1 : ℤ) ≤ -3 + (2 : ℕ) * 2)
  have hX3 : Ge 0 ((W'.baseChange (FF W L)).toAffine.addX x₁ x₂ ((y₁ - y₂) / (x₁ - x₂))) P := by
    rw [addX, bc_a₁ W' L (FF W L), bc_a₂ W' L (FF W L), hX]
    exact hx₂.add (hNi.mono (by norm_num))
  refine ⟨sub_ne_zero.mp hd0, hX3, ?_⟩
  rw [addY, negY, negAddY, negAddY_alg hd0]
  rw [addX, bc_a₁ W' L (FF W L), bc_a₂ W' L (FF W L), hX]
  rw [addX, bc_a₁ W' L (FF W L), bc_a₂ W' L (FF W L), hX] at hX3
  have hu : Ge (-3) (y₁ - y₂) P := hy₁.sub (hy₂.mono (by norm_num))
  rw [add_sub_cancel_left, bc_a₃ W' L (FF W L)]
  exact (((((hu.mul hio).mul hNi).mono (by norm_num)).add hy₂).neg.sub ((hc _).mul0 hX3)).sub (hc _)

end Pole

end RPLib.DWS


