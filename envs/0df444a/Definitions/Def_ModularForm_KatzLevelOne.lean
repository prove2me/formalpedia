-- Prove2me | Definitions.Def_ModularForm_KatzLevelOne
-- name    : ModularForm_KatzLevelOne
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/421b8b3e-7a5f-5458-a379-7fc97db88480
-- title:
--   Katz modular forms of level one via Weierstrass models
-- statement:
--   For a commutative ring $R$ and an integer $k$, the structure [`KatzModularForm R k`](../def/ModularForm_KatzLevelOne.html#L10) packages a rule on Weierstrass models: a field `toFun` assigning to each commutative $R$-algebra $A$ (taken in the same universe as $R$) and each `W : WeierstrassCurve A` whose discriminant `W.Δ` is a unit an element of $A$, subject to two axioms carried as fields. The field `map_toFun` demands compatibility with base change: for every $R$-algebra homomorphism $f : A \to B$, the value on the curve `W.map f` obtained by applying $f$ to the coefficients is $f$ applied to the value on $W$. The field `toFun_variableChange` demands the weight-$k$ homogeneity: for an admissible change of variables `C = ⟨u, r, s, t⟩ : WeierstrassCurve.VariableChange A`, the value on `C • W` equals $(u^{-1})^{k}$ times the value on $W$, the scalar being the $k$-th power of the unit $u^{-1}$ of $A$. Auxiliary lemmas record that invertibility of $\Delta$ is preserved by base change and by variable change, and that a form is determined by its values, whence an extension principle. The type is given the pointwise $R$-module structure (zero, addition, negation, subtraction and scalar multiplication computed on values), and `mul` multiplies a form of weight $k$ by one of weight $l$ to give a form of weight $k + l$. The $q$-expansion `qExpansion F : LaurentSeries R` is the value of $F$ on the Tate model [`ModularCurve.tateLaurent R`](../def/ModularCurve_TateFormal.html#L86) over $R((q))$, the Weierstrass curve with $a_1 = 1$, $a_2 = a_3 = 0$ and $a_4, a_6$ the base change to $R((q))$ of the integral series [`ModularCurve.tateA4`](../def/ModularCurve_TateFormal.html#L29), [`ModularCurve.tateA6`](../def/ModularCurve_TateFormal.html#L32), whose discriminant is a unit. Taking $q$-expansions is additive, $R$-linear and multiplicative. Finally `c₄`, `c₆` and `discr` are the forms of weights $4$, $6$ and $12$ sending $W$ to `W.c₄`, `W.c₆` and `W.Δ`, their $q$-expansions being the corresponding invariants of the Tate model. Holomorphy at infinity is not part of the structure; it is a condition one imposes separately on `qExpansion`.
--
--   **Relation to Mathlib.** Mathlib supplies Weierstrass curves, their invariants $c_4$, $c_6$, $\Delta$, base change `WeierstrassCurve.map` and the group of admissible variable changes with the transformation formulas; the notion of a Katz modular form over a base ring, expressed as a rule on Weierstrass models with invertible discriminant, is the project's own and has no Mathlib counterpart.
--
--   **Where it is used.** This furnishes level-one modular forms over an arbitrary base ring, together with the $q$-expansion map to $R((q))$ obtained by evaluation on the Tate model, which is the form in which modular forms and their reductions are handled on the modularity side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularForm_KatzLevelOne.lean

import Mathlib
import Definitions.Def_ModularCurve_TateFormal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

noncomputable section

open WeierstrassCurve

structure KatzModularForm (R : Type u) [CommRing R] (k : ℤ) : Type (u + 1) where

  toFun : ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (W : WeierstrassCurve A), IsUnit W.Δ → A

  map_toFun : ∀ ⦃A B : Type u⦄ [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (hW' : IsUnit (W.map (f : A →+* B)).Δ), toFun (W.map (f : A →+* B)) hW' = f (toFun W hW)

  toFun_variableChange : ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (C : VariableChange A)
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (hW' : IsUnit (C • W).Δ),
    toFun (C • W) hW' = ((C.u⁻¹ ^ k : Aˣ) : A) * toFun W hW

namespace KatzModularForm

variable {R : Type u} [CommRing R] {k l : ℤ}

theorem isUnit_Δ_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {W : WeierstrassCurve A} (hW : IsUnit W.Δ) : IsUnit (W.map f).Δ := by
  rw [WeierstrassCurve.map_Δ]; exact hW.map f

theorem isUnit_Δ_variableChange {A : Type*} [CommRing A] (C : VariableChange A)
    {W : WeierstrassCurve A} (hW : IsUnit W.Δ) : IsUnit (C • W).Δ := by
  rw [WeierstrassCurve.variableChange_Δ]
  exact ((C.u⁻¹).isUnit.pow 12).mul hW

theorem toFun_injective : Function.Injective (toFun : KatzModularForm R k → _) := by
  rintro ⟨F, _, _⟩ ⟨G, _, _⟩ h
  congr

@[ext]
theorem ext {F G : KatzModularForm R k}
    (h : ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ),
      F.toFun W hW = G.toFun W hW) : F = G :=
  toFun_injective (by funext A _ _ W hW; exact h W hW)

instance : Zero (KatzModularForm R k) :=
  ⟨{ toFun := fun _ _ _ _ _ => 0
     map_toFun := by intros; simp
     toFun_variableChange := by intros; simp }⟩

instance : Add (KatzModularForm R k) :=
  ⟨fun F G =>
    { toFun := fun _ _ _ W hW => F.toFun W hW + G.toFun W hW
      map_toFun := by
        intro A B _ _ _ _ f W hW hW'
        rw [map_add, F.map_toFun f W hW hW', G.map_toFun f W hW hW']
      toFun_variableChange := by
        intro A _ _ C W hW hW'
        rw [F.toFun_variableChange C W hW hW', G.toFun_variableChange C W hW hW', mul_add] }⟩

instance : Neg (KatzModularForm R k) :=
  ⟨fun F =>
    { toFun := fun _ _ _ W hW => -F.toFun W hW
      map_toFun := by
        intro A B _ _ _ _ f W hW hW'
        rw [map_neg, F.map_toFun f W hW hW']
      toFun_variableChange := by
        intro A _ _ C W hW hW'
        rw [F.toFun_variableChange C W hW hW', mul_neg] }⟩

instance : Sub (KatzModularForm R k) :=
  ⟨fun F G =>
    { toFun := fun _ _ _ W hW => F.toFun W hW - G.toFun W hW
      map_toFun := by
        intro A B _ _ _ _ f W hW hW'
        rw [map_sub, F.map_toFun f W hW hW', G.map_toFun f W hW hW']
      toFun_variableChange := by
        intro A _ _ C W hW hW'
        rw [F.toFun_variableChange C W hW hW', G.toFun_variableChange C W hW hW', mul_sub] }⟩

instance : SMul R (KatzModularForm R k) :=
  ⟨fun c F =>
    { toFun := fun _ _ _ W hW => c • F.toFun W hW
      map_toFun := by
        intro A B _ _ _ _ f W hW hW'
        rw [map_smul, F.map_toFun f W hW hW']
      toFun_variableChange := by
        intro A _ _ C W hW hW'
        rw [F.toFun_variableChange C W hW hW', mul_smul_comm] }⟩

@[simp] theorem zero_toFun {A : Type u} [CommRing A] [Algebra R A] (W : WeierstrassCurve A)
    (hW : IsUnit W.Δ) : (0 : KatzModularForm R k).toFun W hW = 0 := rfl

@[simp] theorem add_toFun (F G : KatzModularForm R k) {A : Type u} [CommRing A] [Algebra R A]
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) :
    (F + G).toFun W hW = F.toFun W hW + G.toFun W hW := rfl

@[simp] theorem neg_toFun (F : KatzModularForm R k) {A : Type u} [CommRing A] [Algebra R A]
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) : (-F).toFun W hW = -F.toFun W hW := rfl

@[simp] theorem sub_toFun (F G : KatzModularForm R k) {A : Type u} [CommRing A] [Algebra R A]
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) :
    (F - G).toFun W hW = F.toFun W hW - G.toFun W hW := rfl

@[simp] theorem smul_toFun (c : R) (F : KatzModularForm R k) {A : Type u} [CommRing A]
    [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ) :
    (c • F).toFun W hW = c • F.toFun W hW := rfl

instance : AddCommGroup (KatzModularForm R k) where
  add_assoc F G H := by ext; simp [add_assoc]
  zero_add F := by ext; simp
  add_zero F := by ext; simp
  add_comm F G := by ext; simp [add_comm]
  neg_add_cancel F := by ext; simp
  sub_eq_add_neg F G := by ext; simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module R (KatzModularForm R k) where
  one_smul F := by ext; simp
  mul_smul a b F := by ext; simp [mul_smul]
  smul_zero a := by ext; simp
  smul_add a F G := by ext; simp
  add_smul a b F := by ext; simp [add_smul]
  zero_smul F := by ext; simp

def mul (F : KatzModularForm R k) (G : KatzModularForm R l) : KatzModularForm R (k + l) where
  toFun _ _ _ W hW := F.toFun W hW * G.toFun W hW
  map_toFun := by
    intro A B _ _ _ _ f W hW hW'
    rw [map_mul, F.map_toFun f W hW hW', G.map_toFun f W hW hW']
  toFun_variableChange := by
    intro A _ _ C W hW hW'
    rw [F.toFun_variableChange C W hW hW', G.toFun_variableChange C W hW hW', zpow_add,
      Units.val_mul]
    ring

@[simp] theorem mul_toFun (F : KatzModularForm R k) (G : KatzModularForm R l) {A : Type u}
    [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ) :
    (F.mul G).toFun W hW = F.toFun W hW * G.toFun W hW := rfl

def qExpansion (F : KatzModularForm R k) : LaurentSeries R :=
  F.toFun (ModularCurve.tateLaurent R) (ModularCurve.tateLaurent R).isUnit_Δ

@[simp] theorem qExpansion_zero : (0 : KatzModularForm R k).qExpansion = 0 := rfl

@[simp] theorem qExpansion_add (F G : KatzModularForm R k) :
    (F + G).qExpansion = F.qExpansion + G.qExpansion := rfl

@[simp] theorem qExpansion_neg (F : KatzModularForm R k) : (-F).qExpansion = -F.qExpansion := rfl

@[simp] theorem qExpansion_sub (F G : KatzModularForm R k) :
    (F - G).qExpansion = F.qExpansion - G.qExpansion := rfl

@[simp] theorem qExpansion_smul (c : R) (F : KatzModularForm R k) :
    (c • F).qExpansion = c • F.qExpansion := by
  simp only [qExpansion, smul_toFun, Algebra.smul_def, ← HahnSeries.C_mul_eq_smul]
  congr 1
  rw [RingHom.algebraMap_toAlgebra]
  simp

@[simp] theorem qExpansion_mul (F : KatzModularForm R k) (G : KatzModularForm R l) :
    (F.mul G).qExpansion = F.qExpansion * G.qExpansion := rfl

variable (R)

def c₄ : KatzModularForm R 4 where
  toFun _ _ _ W _ := W.c₄
  map_toFun := by
    intro A B _ _ _ _ f W hW hW'
    exact W.map_c₄ (f : A →+* B)
  toFun_variableChange := by
    intro A _ _ C W hW hW'
    rw [W.variableChange_c₄ C]
    norm_cast

def c₆ : KatzModularForm R 6 where
  toFun _ _ _ W _ := W.c₆
  map_toFun := by
    intro A B _ _ _ _ f W hW hW'
    exact W.map_c₆ (f : A →+* B)
  toFun_variableChange := by
    intro A _ _ C W hW hW'
    rw [W.variableChange_c₆ C]
    norm_cast

def discr : KatzModularForm R 12 where
  toFun _ _ _ W _ := W.Δ
  map_toFun := by
    intro A B _ _ _ _ f W hW hW'
    exact W.map_Δ (f : A →+* B)
  toFun_variableChange := by
    intro A _ _ C W hW hW'
    rw [W.variableChange_Δ C]
    norm_cast

variable {R}

@[simp] theorem c₄_toFun {A : Type u} [CommRing A] [Algebra R A] (W : WeierstrassCurve A)
    (hW : IsUnit W.Δ) : (c₄ R).toFun W hW = W.c₄ := rfl

@[simp] theorem c₆_toFun {A : Type u} [CommRing A] [Algebra R A] (W : WeierstrassCurve A)
    (hW : IsUnit W.Δ) : (c₆ R).toFun W hW = W.c₆ := rfl

@[simp] theorem discr_toFun {A : Type u} [CommRing A] [Algebra R A] (W : WeierstrassCurve A)
    (hW : IsUnit W.Δ) : (discr R).toFun W hW = W.Δ := rfl

theorem qExpansion_c₄ : (c₄ R).qExpansion = (ModularCurve.tateLaurent R).c₄ := rfl

theorem qExpansion_c₆ : (c₆ R).qExpansion = (ModularCurve.tateLaurent R).c₆ := rfl

theorem qExpansion_discr : (discr R).qExpansion = (ModularCurve.tateLaurent R).Δ := rfl

end KatzModularForm

end


