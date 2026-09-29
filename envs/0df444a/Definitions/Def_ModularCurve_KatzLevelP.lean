-- Prove2me | Definitions.Def_ModularCurve_KatzLevelP
-- name    : ModularCurve_KatzLevelP
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/7c1af0bd-abcc-5ecb-99ef-7bbc47bcf7ed
-- title:
--   Katz modular forms with level-p structure on Weierstrass curves
-- statement:
--   Fix a commutative ring $A$ and a Weierstrass curve $W/A$. For $x_0,x\in A$ the element $\mathrm{indepElt}(W,p,x_0,x)=\prod_{a=1}^{(p-1)/2}\bigl(x\,\Psi^{\mathrm{Sq}}_a(x_0)-\Phi_a(x_0)\bigr)$ is formed from Mathlib's univariate division polynomials (the product runs over the integer interval $1\le a\le (p-1)/2$, with natural-number division), and the predicate `InLine` asserts that one factor vanishes, i.e. $x\,\Psi^{\mathrm{Sq}}_a(x_0)=\Phi_a(x_0)$ for some such $a$: the $x$-coordinate $x$ is that of a multiple $[a]$ of a point with abscissa $x_0$. Both are compatible with ring maps, and `InLine` holds for $x=x_0$ as soon as $1\le (p-1)/2$. The structure `LevelPData` is simply a quadruple $(x_P,y_P,x_Q,y_Q)\in A^4$, with the involution exchanging the two pairs, coordinatewise transport along ring homomorphisms, and the substitution attached to a `VariableChange` $(u,r,s,t)$, namely $x\mapsto u^{-2}(x-r)$, $y\mapsto u^{-3}(y-s(x-r)-t)$ applied to each pair. The predicate `IsLevelPStructure W p D` is the conjunction of six conditions carried as fields: both pairs satisfy the affine Weierstrass equation of $W$, $(\mathrm{pre}\Psi_p)(x_P)=(\mathrm{pre}\Psi_p)(x_Q)=0$, and both $\mathrm{indepElt}(W,p,x_P,x_Q)$ and $\mathrm{indepElt}(W,p,x_Q,x_P)$ are units. It is preserved by the swap and by base change; for variable change only the invariance of the two equations is recorded.
--
--   Over a commutative ring $R$ and for $k\in\mathbb Z$, `KatzLevelPForm R p k` is a rule assigning to each $R$-algebra $A$, each $W/A$ with $\Delta(W)$ a unit and each level-$p$ structure $D$ on $W$ an element of $A$, subject to two laws held as fields: compatibility with $R$-algebra maps, and the weight-$k$ rule $F(C\cdot W,\,D^C)=(u^{-1})^{k}F(W,D)$. These form an $R$-module, with a multiplication adding weights, and the involution $F\mapsto F^{\mathrm{sw}}$ given by swapping $D$. Three predicates are defined: dependence of $F$ only on the second abscissa up to `InLine`, dependence only on both abscissae up to `InLine`, and swap-invariance (equivalent to $F^{\mathrm{sw}}=F$); the first implies the second and also that $F^{\mathrm{sw}}-F$ has the second property, and it is stable under the module operations and products. `KatzGamma0Form R p k` is a `KatzLevelPForm` together with a field asserting the first predicate, again an $R$-module with weight-additive product. A level-one Katz form pulls back to both, by ignoring the level data; the pullback is swap-invariant, and the pullback maps respect zero, addition and scalars. Finally, inside $\mathrm{GL}_2(\mathbb Z/p)$ are defined the subgroup of matrices with vanishing $(0,1)$-entry, the subgroup of diagonal matrices (contained in it), and the two elements $\begin{pmatrix}1&1\\0&1\end{pmatrix}$ and $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   **Relation to Mathlib.** Weierstrass curves, their discriminant, admissible variable changes, the affine equation and the division polynomials `preΨ`, `ΨSq`, `Φ` are Mathlib's; the level-$p$ data, the predicate `IsLevelPStructure`, and the functor-of-points notions of Katz form with level-$p$ or $\Gamma_0(p)$-type structure are the project's own, shaped exactly like its level-one [`KatzModularForm`](../def/ModularForm_KatzLevelOne.html#L10).
--
--   **Where it is used.** These definitions provide the algebraic (functor-of-points) description of modular forms of level $p$ and of $\Gamma_0(p)$-type on which the $q$-expansion and Hecke-theoretic input to the modularity arguments is built, the level-$p$ structure playing the role of a basis of the $p$-torsion and the `InLine` relation that of passage to the cyclic subgroup it generates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_KatzLevelP.lean

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

noncomputable section

open WeierstrassCurve Polynomial

namespace ModularCurve

section Elements

variable {A : Type*} [CommRing A]

def indepElt (W : WeierstrassCurve A) (p : ℕ) (x₀ x : A) : A :=
  ∏ a ∈ Finset.Icc 1 ((p - 1) / 2), (x * (W.ΨSq a).eval x₀ - (W.Φ a).eval x₀)

def InLine (W : WeierstrassCurve A) (p : ℕ) (x₀ x : A) : Prop :=
  ∃ a : ℕ, 1 ≤ a ∧ a ≤ (p - 1) / 2 ∧ x * (W.ΨSq a).eval x₀ = (W.Φ a).eval x₀

theorem inLine_self (W : WeierstrassCurve A) {p : ℕ} (hp : 1 ≤ (p - 1) / 2) (x₀ : A) :
    InLine W p x₀ x₀ :=
  ⟨1, le_rfl, hp, by simp [WeierstrassCurve.ΨSq_one, WeierstrassCurve.Φ_one]⟩

theorem indepElt_map {B : Type*} [CommRing B] (W : WeierstrassCurve A) (f : A →+* B) (p : ℕ)
    (x₀ x : A) : indepElt (W.map f) p (f x₀) (f x) = f (indepElt W p x₀ x) := by
  simp only [indepElt, map_prod, map_sub, map_mul, WeierstrassCurve.map_ΨSq,
    WeierstrassCurve.map_Φ, Polynomial.eval_map, Polynomial.eval₂_at_apply]

theorem InLine.map {B : Type*} [CommRing B] {W : WeierstrassCurve A} (f : A →+* B) {p : ℕ}
    {x₀ x : A} (h : InLine W p x₀ x) : InLine (W.map f) p (f x₀) (f x) := by
  obtain ⟨a, ha, ha', hx⟩ := h
  refine ⟨a, ha, ha', ?_⟩
  rw [WeierstrassCurve.map_ΨSq, WeierstrassCurve.map_Φ, Polynomial.eval_map,
    Polynomial.eval_map, Polynomial.eval₂_at_apply, Polynomial.eval₂_at_apply, ← map_mul, hx]

end Elements

@[ext]
structure LevelPData (A : Type u) where

  xP : A

  yP : A

  xQ : A

  yQ : A

namespace LevelPData

variable {A : Type u} {B : Type v}

def swap (D : LevelPData A) : LevelPData A :=
  ⟨D.xQ, D.yQ, D.xP, D.yP⟩

@[simp] theorem swap_xP (D : LevelPData A) : D.swap.xP = D.xQ := rfl
@[simp] theorem swap_yP (D : LevelPData A) : D.swap.yP = D.yQ := rfl
@[simp] theorem swap_xQ (D : LevelPData A) : D.swap.xQ = D.xP := rfl
@[simp] theorem swap_yQ (D : LevelPData A) : D.swap.yQ = D.yP := rfl

@[simp] theorem swap_swap (D : LevelPData A) : D.swap.swap = D := rfl

variable [CommRing A] [CommRing B]

def map (f : A →+* B) (D : LevelPData A) : LevelPData B :=
  ⟨f D.xP, f D.yP, f D.xQ, f D.yQ⟩

@[simp] theorem map_xP (f : A →+* B) (D : LevelPData A) : (D.map f).xP = f D.xP := rfl
@[simp] theorem map_yP (f : A →+* B) (D : LevelPData A) : (D.map f).yP = f D.yP := rfl
@[simp] theorem map_xQ (f : A →+* B) (D : LevelPData A) : (D.map f).xQ = f D.xQ := rfl
@[simp] theorem map_yQ (f : A →+* B) (D : LevelPData A) : (D.map f).yQ = f D.yQ := rfl

theorem map_id (D : LevelPData A) : D.map (RingHom.id A) = D := rfl

theorem map_map {C : Type w} [CommRing C] (f : A →+* B) (g : B →+* C) (D : LevelPData A) :
    (D.map f).map g = D.map (g.comp f) := rfl

theorem map_swap (f : A →+* B) (D : LevelPData A) : D.swap.map f = (D.map f).swap := rfl

def variableChange (C : VariableChange A) (D : LevelPData A) : LevelPData A where
  xP := ((C.u⁻¹ : Aˣ) : A) ^ 2 * (D.xP - C.r)
  yP := ((C.u⁻¹ : Aˣ) : A) ^ 3 * (D.yP - C.s * (D.xP - C.r) - C.t)
  xQ := ((C.u⁻¹ : Aˣ) : A) ^ 2 * (D.xQ - C.r)
  yQ := ((C.u⁻¹ : Aˣ) : A) ^ 3 * (D.yQ - C.s * (D.xQ - C.r) - C.t)

@[simp] theorem variableChange_xP (C : VariableChange A) (D : LevelPData A) :
    (D.variableChange C).xP = ((C.u⁻¹ : Aˣ) : A) ^ 2 * (D.xP - C.r) := rfl
@[simp] theorem variableChange_yP (C : VariableChange A) (D : LevelPData A) :
    (D.variableChange C).yP = ((C.u⁻¹ : Aˣ) : A) ^ 3 * (D.yP - C.s * (D.xP - C.r) - C.t) := rfl
@[simp] theorem variableChange_xQ (C : VariableChange A) (D : LevelPData A) :
    (D.variableChange C).xQ = ((C.u⁻¹ : Aˣ) : A) ^ 2 * (D.xQ - C.r) := rfl
@[simp] theorem variableChange_yQ (C : VariableChange A) (D : LevelPData A) :
    (D.variableChange C).yQ = ((C.u⁻¹ : Aˣ) : A) ^ 3 * (D.yQ - C.s * (D.xQ - C.r) - C.t) := rfl

theorem variableChange_swap (C : VariableChange A) (D : LevelPData A) :
    D.swap.variableChange C = (D.variableChange C).swap := rfl

end LevelPData

structure IsLevelPStructure {A : Type u} [CommRing A] (W : WeierstrassCurve A) (p : ℕ)
    (D : LevelPData A) : Prop where

  equation_P : W.toAffine.Equation D.xP D.yP

  equation_Q : W.toAffine.Equation D.xQ D.yQ

  preΨ_P : (W.preΨ p).eval D.xP = 0

  preΨ_Q : (W.preΨ p).eval D.xQ = 0

  isUnit_indepElt_PQ : IsUnit (indepElt W p D.xP D.xQ)

  isUnit_indepElt_QP : IsUnit (indepElt W p D.xQ D.xP)

namespace IsLevelPStructure

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] {W : WeierstrassCurve A} {p : ℕ}
  {D : LevelPData A}

theorem swap (h : IsLevelPStructure W p D) : IsLevelPStructure W p D.swap :=
  ⟨h.equation_Q, h.equation_P, h.preΨ_Q, h.preΨ_P, h.isUnit_indepElt_QP, h.isUnit_indepElt_PQ⟩

theorem map (h : IsLevelPStructure W p D) (f : A →+* B) :
    IsLevelPStructure (W.map f) p (D.map f) where
  equation_P := h.equation_P.map f
  equation_Q := h.equation_Q.map f
  preΨ_P := by
    rw [LevelPData.map_xP, WeierstrassCurve.map_preΨ, Polynomial.eval_map,
      Polynomial.eval₂_at_apply, h.preΨ_P, map_zero]
  preΨ_Q := by
    rw [LevelPData.map_xQ, WeierstrassCurve.map_preΨ, Polynomial.eval_map,
      Polynomial.eval₂_at_apply, h.preΨ_Q, map_zero]
  isUnit_indepElt_PQ := by
    rw [LevelPData.map_xP, LevelPData.map_xQ, indepElt_map]
    exact h.isUnit_indepElt_PQ.map f
  isUnit_indepElt_QP := by
    rw [LevelPData.map_xP, LevelPData.map_xQ, indepElt_map]
    exact h.isUnit_indepElt_QP.map f

theorem equation_variableChange_aux (C : VariableChange A) {x y : A}
    (h : W.toAffine.Equation x y) :
    (C • W).toAffine.Equation (((C.u⁻¹ : Aˣ) : A) ^ 2 * (x - C.r))
      (((C.u⁻¹ : Aˣ) : A) ^ 3 * (y - C.s * (x - C.r) - C.t)) := by
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆]
  linear_combination ((C.u⁻¹ : Aˣ) : A) ^ 6 * h

theorem equation_P_variableChange (h : IsLevelPStructure W p D) (C : VariableChange A) :
    (C • W).toAffine.Equation (D.variableChange C).xP (D.variableChange C).yP :=
  equation_variableChange_aux C h.equation_P

theorem equation_Q_variableChange (h : IsLevelPStructure W p D) (C : VariableChange A) :
    (C • W).toAffine.Equation (D.variableChange C).xQ (D.variableChange C).yQ :=
  equation_variableChange_aux C h.equation_Q

end IsLevelPStructure

structure KatzLevelPForm (R : Type u) [CommRing R] (p : ℕ) (k : ℤ) : Type (u + 1) where

  toFun : ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (W : WeierstrassCurve A), IsUnit W.Δ →
    ∀ D : LevelPData A, IsLevelPStructure W p D → A

  map_toFun : ∀ ⦃A B : Type u⦄ [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (hW' : IsUnit (W.map (f : A →+* B)).Δ) (D : LevelPData A) (hD : IsLevelPStructure W p D)
    (hD' : IsLevelPStructure (W.map (f : A →+* B)) p (D.map (f : A →+* B))),
    toFun (W.map (f : A →+* B)) hW' (D.map (f : A →+* B)) hD' = f (toFun W hW D hD)

  toFun_variableChange : ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (C : VariableChange A)
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (hW' : IsUnit (C • W).Δ) (D : LevelPData A)
    (hD : IsLevelPStructure W p D) (hD' : IsLevelPStructure (C • W) p (D.variableChange C)),
    toFun (C • W) hW' (D.variableChange C) hD' = ((C.u⁻¹ ^ k : Aˣ) : A) * toFun W hW D hD

namespace KatzLevelPForm

variable {R : Type u} [CommRing R] {p : ℕ} {k l : ℤ}

theorem toFun_injective : Function.Injective (toFun : KatzLevelPForm R p k → _) := by
  rintro ⟨F, _, _⟩ ⟨G, _, _⟩ h
  congr

@[ext]
theorem ext {F G : KatzLevelPForm R p k}
    (h : ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
      (D : LevelPData A) (hD : IsLevelPStructure W p D), F.toFun W hW D hD = G.toFun W hW D hD) :
    F = G :=
  toFun_injective (by funext A _ _ W hW D hD; exact h W hW D hD)

instance : Zero (KatzLevelPForm R p k) :=
  ⟨{ toFun := fun _ _ _ _ _ _ _ => 0
     map_toFun := by intros; simp
     toFun_variableChange := by intros; simp }⟩

instance : Add (KatzLevelPForm R p k) :=
  ⟨fun F G =>
    { toFun := fun _ _ _ W hW D hD => F.toFun W hW D hD + G.toFun W hW D hD
      map_toFun := by
        intro A B _ _ _ _ f W hW hW' D hD hD'
        rw [map_add, F.map_toFun f W hW hW' D hD hD', G.map_toFun f W hW hW' D hD hD']
      toFun_variableChange := by
        intro A _ _ C W hW hW' D hD hD'
        rw [F.toFun_variableChange C W hW hW' D hD hD',
          G.toFun_variableChange C W hW hW' D hD hD', mul_add] }⟩

instance : Neg (KatzLevelPForm R p k) :=
  ⟨fun F =>
    { toFun := fun _ _ _ W hW D hD => -F.toFun W hW D hD
      map_toFun := by
        intro A B _ _ _ _ f W hW hW' D hD hD'
        rw [map_neg, F.map_toFun f W hW hW' D hD hD']
      toFun_variableChange := by
        intro A _ _ C W hW hW' D hD hD'
        rw [F.toFun_variableChange C W hW hW' D hD hD', mul_neg] }⟩

instance : Sub (KatzLevelPForm R p k) :=
  ⟨fun F G =>
    { toFun := fun _ _ _ W hW D hD => F.toFun W hW D hD - G.toFun W hW D hD
      map_toFun := by
        intro A B _ _ _ _ f W hW hW' D hD hD'
        rw [map_sub, F.map_toFun f W hW hW' D hD hD', G.map_toFun f W hW hW' D hD hD']
      toFun_variableChange := by
        intro A _ _ C W hW hW' D hD hD'
        rw [F.toFun_variableChange C W hW hW' D hD hD',
          G.toFun_variableChange C W hW hW' D hD hD', mul_sub] }⟩

instance : SMul R (KatzLevelPForm R p k) :=
  ⟨fun c F =>
    { toFun := fun _ _ _ W hW D hD => c • F.toFun W hW D hD
      map_toFun := by
        intro A B _ _ _ _ f W hW hW' D hD hD'
        rw [map_smul, F.map_toFun f W hW hW' D hD hD']
      toFun_variableChange := by
        intro A _ _ C W hW hW' D hD hD'
        rw [F.toFun_variableChange C W hW hW' D hD hD', mul_smul_comm] }⟩

section simp_lemmas

variable {A : Type u} [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
  (D : LevelPData A) (hD : IsLevelPStructure W p D)

@[simp] theorem zero_toFun : (0 : KatzLevelPForm R p k).toFun W hW D hD = 0 := rfl

@[simp] theorem add_toFun (F G : KatzLevelPForm R p k) :
    (F + G).toFun W hW D hD = F.toFun W hW D hD + G.toFun W hW D hD := rfl

@[simp] theorem neg_toFun (F : KatzLevelPForm R p k) :
    (-F).toFun W hW D hD = -F.toFun W hW D hD := rfl

@[simp] theorem sub_toFun (F G : KatzLevelPForm R p k) :
    (F - G).toFun W hW D hD = F.toFun W hW D hD - G.toFun W hW D hD := rfl

@[simp] theorem smul_toFun (c : R) (F : KatzLevelPForm R p k) :
    (c • F).toFun W hW D hD = c • F.toFun W hW D hD := rfl

end simp_lemmas

instance : AddCommGroup (KatzLevelPForm R p k) where
  add_assoc F G H := by ext; simp [add_assoc]
  zero_add F := by ext; simp
  add_zero F := by ext; simp
  add_comm F G := by ext; simp [add_comm]
  neg_add_cancel F := by ext; simp
  sub_eq_add_neg F G := by ext; simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module R (KatzLevelPForm R p k) where
  one_smul F := by ext; simp
  mul_smul a b F := by ext; simp [mul_smul]
  smul_zero a := by ext; simp
  smul_add a F G := by ext; simp
  add_smul a b F := by ext; simp [add_smul]
  zero_smul F := by ext; simp

def mul (F : KatzLevelPForm R p k) (G : KatzLevelPForm R p l) : KatzLevelPForm R p (k + l) where
  toFun _ _ _ W hW D hD := F.toFun W hW D hD * G.toFun W hW D hD
  map_toFun := by
    intro A B _ _ _ _ f W hW hW' D hD hD'
    rw [map_mul, F.map_toFun f W hW hW' D hD hD', G.map_toFun f W hW hW' D hD hD']
  toFun_variableChange := by
    intro A _ _ C W hW hW' D hD hD'
    rw [F.toFun_variableChange C W hW hW' D hD hD', G.toFun_variableChange C W hW hW' D hD hD',
      zpow_add, Units.val_mul]
    ring

@[simp] theorem mul_toFun (F : KatzLevelPForm R p k) (G : KatzLevelPForm R p l) {A : Type u}
    [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (D : LevelPData A)
    (hD : IsLevelPStructure W p D) :
    (F.mul G).toFun W hW D hD = F.toFun W hW D hD * G.toFun W hW D hD := rfl

def swap (F : KatzLevelPForm R p k) : KatzLevelPForm R p k where
  toFun _ _ _ W hW D hD := F.toFun W hW D.swap hD.swap
  map_toFun := by
    intro A B _ _ _ _ f W hW hW' D hD hD'
    exact F.map_toFun f W hW hW' D.swap hD.swap hD'.swap
  toFun_variableChange := by
    intro A _ _ C W hW hW' D hD hD'
    exact F.toFun_variableChange C W hW hW' D.swap hD.swap hD'.swap

@[simp] theorem swap_toFun (F : KatzLevelPForm R p k) {A : Type u} [CommRing A] [Algebra R A]
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (D : LevelPData A)
    (hD : IsLevelPStructure W p D) :
    F.swap.toFun W hW D hD = F.toFun W hW D.swap hD.swap := rfl

@[simp] theorem swap_swap (F : KatzLevelPForm R p k) : F.swap.swap = F := rfl

@[simp] theorem swap_zero : (0 : KatzLevelPForm R p k).swap = 0 := rfl

@[simp] theorem swap_add (F G : KatzLevelPForm R p k) : (F + G).swap = F.swap + G.swap := rfl

@[simp] theorem swap_neg (F : KatzLevelPForm R p k) : (-F).swap = -F.swap := rfl

@[simp] theorem swap_sub (F G : KatzLevelPForm R p k) : (F - G).swap = F.swap - G.swap := rfl

@[simp] theorem swap_smul (c : R) (F : KatzLevelPForm R p k) : (c • F).swap = c • F.swap := rfl

def DependsOnlyOnSndLine (F : KatzLevelPForm R p k) : Prop :=
  ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (D D' : LevelPData A) (hD : IsLevelPStructure W p D) (hD' : IsLevelPStructure W p D'),
    InLine W p D.xQ D'.xQ → F.toFun W hW D' hD' = F.toFun W hW D hD

def DependsOnlyOnLines (F : KatzLevelPForm R p k) : Prop :=
  ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (D D' : LevelPData A) (hD : IsLevelPStructure W p D) (hD' : IsLevelPStructure W p D'),
    InLine W p D.xP D'.xP → InLine W p D.xQ D'.xQ → F.toFun W hW D' hD' = F.toFun W hW D hD

def SwapInvariant (F : KatzLevelPForm R p k) : Prop :=
  ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (D : LevelPData A) (hD : IsLevelPStructure W p D),
    F.toFun W hW D.swap hD.swap = F.toFun W hW D hD

theorem swapInvariant_iff_swap_eq (F : KatzLevelPForm R p k) : F.SwapInvariant ↔ F.swap = F :=
  ⟨fun h => ext fun _ _ _ W hW D hD => h W hW D hD,
    fun h A _ _ W hW D hD => by rw [← swap_toFun, h]⟩

theorem DependsOnlyOnSndLine.dependsOnlyOnLines {F : KatzLevelPForm R p k}
    (h : F.DependsOnlyOnSndLine) : F.DependsOnlyOnLines :=
  fun _ _ _ W hW D D' hD hD' _ hQ => h W hW D D' hD hD' hQ

theorem DependsOnlyOnSndLine.dependsOnlyOnLines_swap_sub {F : KatzLevelPForm R p k}
    (h : F.DependsOnlyOnSndLine) : (F.swap - F).DependsOnlyOnLines := by
  intro A _ _ W hW D D' hD hD' hP hQ
  simp only [sub_toFun, swap_toFun]
  rw [h W hW D D' hD hD' hQ, h W hW D.swap D'.swap hD.swap hD'.swap hP]

theorem DependsOnlyOnSndLine.zero : (0 : KatzLevelPForm R p k).DependsOnlyOnSndLine :=
  fun _ _ _ _ _ _ _ _ _ _ => rfl

theorem DependsOnlyOnSndLine.add {F G : KatzLevelPForm R p k} (hF : F.DependsOnlyOnSndLine)
    (hG : G.DependsOnlyOnSndLine) : (F + G).DependsOnlyOnSndLine := by
  intro A _ _ W hW D D' hD hD' hQ
  simp only [add_toFun, hF W hW D D' hD hD' hQ, hG W hW D D' hD hD' hQ]

theorem DependsOnlyOnSndLine.neg {F : KatzLevelPForm R p k} (hF : F.DependsOnlyOnSndLine) :
    (-F).DependsOnlyOnSndLine := by
  intro A _ _ W hW D D' hD hD' hQ
  simp only [neg_toFun, hF W hW D D' hD hD' hQ]

theorem DependsOnlyOnSndLine.smul (c : R) {F : KatzLevelPForm R p k}
    (hF : F.DependsOnlyOnSndLine) : (c • F).DependsOnlyOnSndLine := by
  intro A _ _ W hW D D' hD hD' hQ
  simp only [smul_toFun, hF W hW D D' hD hD' hQ]

theorem DependsOnlyOnSndLine.mul {F : KatzLevelPForm R p k} {G : KatzLevelPForm R p l}
    (hF : F.DependsOnlyOnSndLine) (hG : G.DependsOnlyOnSndLine) :
    (F.mul G).DependsOnlyOnSndLine := by
  intro A _ _ W hW D D' hD hD' hQ
  simp only [mul_toFun, hF W hW D D' hD hD' hQ, hG W hW D D' hD hD' hQ]

end KatzLevelPForm

structure KatzGamma0Form (R : Type u) [CommRing R] (p : ℕ) (k : ℤ) : Type (u + 1)
    extends KatzLevelPForm R p k where

  dependsOnlyOnSndLine : toKatzLevelPForm.DependsOnlyOnSndLine

namespace KatzGamma0Form

variable {R : Type u} [CommRing R] {p : ℕ} {k l : ℤ}

theorem toKatzLevelPForm_injective :
    Function.Injective (toKatzLevelPForm : KatzGamma0Form R p k → KatzLevelPForm R p k) := by
  rintro ⟨F, _⟩ ⟨G, _⟩ h
  congr

@[ext]
theorem ext {F G : KatzGamma0Form R p k} (h : F.toKatzLevelPForm = G.toKatzLevelPForm) : F = G :=
  toKatzLevelPForm_injective h

instance : Zero (KatzGamma0Form R p k) := ⟨⟨0, KatzLevelPForm.DependsOnlyOnSndLine.zero⟩⟩

instance : Add (KatzGamma0Form R p k) :=
  ⟨fun F G => ⟨F.toKatzLevelPForm + G.toKatzLevelPForm,
    F.dependsOnlyOnSndLine.add G.dependsOnlyOnSndLine⟩⟩

instance : Neg (KatzGamma0Form R p k) :=
  ⟨fun F => ⟨-F.toKatzLevelPForm, F.dependsOnlyOnSndLine.neg⟩⟩

instance : Sub (KatzGamma0Form R p k) :=
  ⟨fun F G => ⟨F.toKatzLevelPForm - G.toKatzLevelPForm, by
    rw [sub_eq_add_neg]; exact F.dependsOnlyOnSndLine.add G.dependsOnlyOnSndLine.neg⟩⟩

instance : SMul R (KatzGamma0Form R p k) :=
  ⟨fun c F => ⟨c • F.toKatzLevelPForm, F.dependsOnlyOnSndLine.smul c⟩⟩

@[simp] theorem toKatzLevelPForm_zero : (0 : KatzGamma0Form R p k).toKatzLevelPForm = 0 := rfl
@[simp] theorem toKatzLevelPForm_add (F G : KatzGamma0Form R p k) :
    (F + G).toKatzLevelPForm = F.toKatzLevelPForm + G.toKatzLevelPForm := rfl
@[simp] theorem toKatzLevelPForm_neg (F : KatzGamma0Form R p k) :
    (-F).toKatzLevelPForm = -F.toKatzLevelPForm := rfl
@[simp] theorem toKatzLevelPForm_sub (F G : KatzGamma0Form R p k) :
    (F - G).toKatzLevelPForm = F.toKatzLevelPForm - G.toKatzLevelPForm := rfl
@[simp] theorem toKatzLevelPForm_smul (c : R) (F : KatzGamma0Form R p k) :
    (c • F).toKatzLevelPForm = c • F.toKatzLevelPForm := rfl

instance : AddCommGroup (KatzGamma0Form R p k) where
  add_assoc F G H := by ext1; simp [add_assoc]
  zero_add F := by ext1; simp
  add_zero F := by ext1; simp
  add_comm F G := by ext1; simp [add_comm]
  neg_add_cancel F := by ext1; simp
  sub_eq_add_neg F G := by ext1; simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module R (KatzGamma0Form R p k) where
  one_smul F := by ext1; simp
  mul_smul a b F := by ext1; simp [mul_smul]
  smul_zero a := by ext1; simp
  smul_add a F G := by ext1; simp
  add_smul a b F := by ext1; simp [add_smul]
  zero_smul F := by ext1; simp

def mul (F : KatzGamma0Form R p k) (G : KatzGamma0Form R p l) : KatzGamma0Form R p (k + l) :=
  ⟨F.toKatzLevelPForm.mul G.toKatzLevelPForm, F.dependsOnlyOnSndLine.mul G.dependsOnlyOnSndLine⟩

@[simp] theorem toKatzLevelPForm_mul (F : KatzGamma0Form R p k) (G : KatzGamma0Form R p l) :
    (F.mul G).toKatzLevelPForm = F.toKatzLevelPForm.mul G.toKatzLevelPForm := rfl

end KatzGamma0Form

end ModularCurve

namespace KatzModularForm

variable {R : Type u} [CommRing R] {k : ℤ}

def pullbackLevelP (g : KatzModularForm R k) (p : ℕ) : ModularCurve.KatzLevelPForm R p k where
  toFun _ _ _ W hW _ _ := g.toFun W hW
  map_toFun := by
    intro A B _ _ _ _ f W hW hW' D hD hD'
    exact g.map_toFun f W hW hW'
  toFun_variableChange := by
    intro A _ _ C W hW hW' D hD hD'
    exact g.toFun_variableChange C W hW hW'

@[simp] theorem pullbackLevelP_toFun (g : KatzModularForm R k) (p : ℕ) {A : Type u} [CommRing A]
    [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (D : ModularCurve.LevelPData A)
    (hD : ModularCurve.IsLevelPStructure W p D) :
    (g.pullbackLevelP p).toFun W hW D hD = g.toFun W hW := rfl

theorem dependsOnlyOnSndLine_pullbackLevelP (g : KatzModularForm R k) (p : ℕ) :
    (g.pullbackLevelP p).DependsOnlyOnSndLine :=
  fun _ _ _ _ _ _ _ _ _ _ => rfl

theorem swapInvariant_pullbackLevelP (g : KatzModularForm R k) (p : ℕ) :
    (g.pullbackLevelP p).SwapInvariant :=
  fun _ _ _ _ _ _ _ => rfl

@[simp] theorem swap_pullbackLevelP (g : KatzModularForm R k) (p : ℕ) :
    (g.pullbackLevelP p).swap = g.pullbackLevelP p := rfl

def pullbackGamma0 (g : KatzModularForm R k) (p : ℕ) : ModularCurve.KatzGamma0Form R p k :=
  ⟨g.pullbackLevelP p, g.dependsOnlyOnSndLine_pullbackLevelP p⟩

@[simp] theorem pullbackGamma0_toKatzLevelPForm (g : KatzModularForm R k) (p : ℕ) :
    (g.pullbackGamma0 p).toKatzLevelPForm = g.pullbackLevelP p := rfl

@[simp] theorem pullbackLevelP_zero (p : ℕ) : (0 : KatzModularForm R k).pullbackLevelP p = 0 :=
  rfl

@[simp] theorem pullbackLevelP_add (g h : KatzModularForm R k) (p : ℕ) :
    (g + h).pullbackLevelP p = g.pullbackLevelP p + h.pullbackLevelP p := rfl

@[simp] theorem pullbackLevelP_smul (c : R) (g : KatzModularForm R k) (p : ℕ) :
    (c • g).pullbackLevelP p = c • g.pullbackLevelP p := rfl

end KatzModularForm

namespace ModularCurve.LevelP

variable (p : ℕ)

def borel : Subgroup (GL (Fin 2) (ZMod p)) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 = 0}
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hg, hh, zero_mul, mul_zero, add_zero]
  one_mem' := by simp
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_two]
    simp [hg]

def splitTorus : Subgroup (GL (Fin 2) (ZMod p)) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 = 0 ∧
    (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0}
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hg.1, hh.1, hg.2, hh.2]
    simp
  one_mem' := by simp
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, Matrix.smul_apply,
      Matrix.adjugate_fin_two]
    simp [hg.1, hg.2]

def unipotentU : GL (Fin 2) (ZMod p) :=
  ⟨!![1, 1; 0, 1], !![1, -1; 0, 1],
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; norm_num,
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; norm_num⟩

def swapW : GL (Fin 2) (ZMod p) :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; norm_num,
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; norm_num⟩

@[simp] theorem coe_unipotentU :
    (unipotentU p : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 1; 0, 1] := rfl

@[simp] theorem coe_swapW : (swapW p : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![0, 1; 1, 0] := rfl

theorem mem_borel_iff (g : GL (Fin 2) (ZMod p)) :
    g ∈ borel p ↔ (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 = 0 := Iff.rfl

theorem mem_splitTorus_iff (g : GL (Fin 2) (ZMod p)) :
    g ∈ splitTorus p ↔ (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 = 0 ∧
      (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 := Iff.rfl

theorem splitTorus_le_borel : splitTorus p ≤ borel p := fun _ hg => hg.1

end ModularCurve.LevelP

end


