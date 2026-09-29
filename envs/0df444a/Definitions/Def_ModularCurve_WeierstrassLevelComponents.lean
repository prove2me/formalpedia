-- Prove2me | Definitions.Def_ModularCurve_WeierstrassLevelComponents
-- name    : ModularCurve_WeierstrassLevelComponents
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/eb01a5c8-b50d-56c5-b805-97fac9b3b7f0
-- title:
--   Level components and rigid Weierstrass level data
-- statement:
--   Over a commutative ring $A$, a `LevelComponent A` packages level data on Weierstrass models: a type `obj T` for every $A$-algebra $T$, a predicate `IsLevel W x` for $W$ a Weierstrass model over $T$ and $x \in \mathrm{obj}(T)$, base change `map f` along $A$-algebra maps $f : T \to T'$, and a transport `act C` along a change of Weierstrass coordinates $C \in$ `WeierstrassCurve.VariableChange T`; the fields require `map` to be functorial, `act` to be a monoid action of the variable-change group, the two to commute via $\mathrm{map}_f \circ \mathrm{act}_C = \mathrm{act}_{C.\mathrm{map} f} \circ \mathrm{map}_f$, and `IsLevel` to be preserved by base change (for $W.\mathrm{map} f$) and by coordinate change (for $C \bullet W$), so the compatibility theorems are fields of the structure. The trivial component ($\mathrm{obj} = \mathrm{PUnit}$, `IsLevel` always true) and componentwise products are given. For a component $L$, `L.Raw T` consists of a Weierstrass model $W$ over $T$, a proof that $\Delta_W$ is a unit, a level datum $x$, and a proof of `IsLevel W x`: the curve and datum sit side by side with the condition as a propositional field, and two raw data agreeing in curve and datum are equal. `L.toRigid` assembles these into a `RigidWeierstrassData A`, whence the quotient by the variable-change relation and the $j$-invariant map.
--
--   Two concrete components are constructed. `kernelVariableChangeDeg` $C\,d\,h = u^{-2d}\,h(u^2X + r)$ refines Mathlib-style kernel transport by fixing the degree $d$ rather than reading $h.\mathrm{natDegree}$; with $d$ fixed it is an action and commutes with base change. The $\Gamma_0(N)$ component takes $\mathrm{obj}(T) = T[X]$, `IsLevel W h` the predicate `W.IsCyclicKernel N h` (degree at most $(N-1)/2$ with leading coefficient $1$ there, $h \mid W.\mathrm{pre}\Psi N$, and $h$ dividing the relevant `smulNumerator`s), `map` polynomial base change and `act` the above with $d = (N-1)/2$. The level-$\ell$ component takes $\mathrm{obj}(T) =$ `LevelPData T` (four coordinates $x_P,y_P,x_Q,y_Q$), `IsLevel W D = IsLevelPStructure W ℓ D`, `map` coordinatewise and `act` the usual $x \mapsto u^{-2}(x-r)$, $y \mapsto u^{-3}(y - s(x-r) - t)$; the action and base-change identities for `LevelPData.variableChange` are proved here. In both cases preservation of the level condition under coordinate change is taken as an explicit hypothesis. Finally `weierstrassLevelRigidData` is the rigid Weierstrass data of the triple product of the $\Gamma_0(N)$ component, the level-$\ell$ component and an arbitrary further component $D_q$.
--
--   **Relation to Mathlib.** Weierstrass models, their variable changes, discriminants and division polynomials are Mathlib's; `LevelComponent`, `RigidWeierstrassData`, `IsCyclicKernel`, `LevelPData` and `IsLevelPStructure` are the project's own, Mathlib having no moduli problems for elliptic curves with level structure. `kernelVariableChangeDeg` is a degree-parametrised variant of the project's [`WeierstrassCurve.kernelVariableChange`](../def/ModularCurve_WeierstrassLevelCarrier.html#L48), agreeing with it when the degree parameter is the polynomial's natural degree.
--
--   **Where it is used.** These constructions supply inhabitants of the level-moduli carrier used for the modular curves with $\Gamma_0(N)$ and level-$\ell$ structure occurring in the modularity argument: supplying a Drinfeld-basis component for $D_q$ and the transformation statements for kernel polynomials and level-$p$ data produces the moduli problem whose points and supersingular behaviour are studied downstream.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_WeierstrassLevelComponents.lean

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_KatzLevelP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

noncomputable section

open Polynomial

namespace ModularCurve

structure LevelComponent (A : Type u) [CommRing A] where

  obj : (T : Type u) → [CommRing T] → [Algebra A T] → Type u

  IsLevel : {T : Type u} → [CommRing T] → [Algebra A T] → WeierstrassCurve T → obj T → Prop

  map : {T T' : Type u} → [CommRing T] → [Algebra A T] → [CommRing T'] → [Algebra A T'] →
    (T →ₐ[A] T') → obj T → obj T'

  act : {T : Type u} → [CommRing T] → [Algebra A T] → WeierstrassCurve.VariableChange T → obj T → obj T
  map_id : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : obj T), map (AlgHom.id A T) x = x
  map_comp : ∀ {T T' T'' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] [CommRing T'']
    [Algebra A T''] (f : T →ₐ[A] T') (g : T' →ₐ[A] T'') (x : obj T), map (g.comp f) x = map g (map f x)
  act_one : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : obj T), act (1 : WeierstrassCurve.VariableChange T) x = x
  act_mul : ∀ {T : Type u} [CommRing T] [Algebra A T] (C C' : WeierstrassCurve.VariableChange T) (x : obj T),
    act (C * C') x = act C (act C' x)
  map_act : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (C : WeierstrassCurve.VariableChange T) (x : obj T), map f (act C x) = act (C.map f.toRingHom) (map f x)
  isLevel_map : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (W : WeierstrassCurve T) (x : obj T), IsLevel W x → IsLevel (W.map f.toRingHom) (map f x)
  isLevel_act : ∀ {T : Type u} [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T)
    (W : WeierstrassCurve T) (x : obj T), IsLevel W x → IsLevel (C • W) (act C x)

namespace LevelComponent

variable {A : Type u} [CommRing A]

def trivial : LevelComponent A where
  obj _ _ _ := PUnit
  IsLevel _ _ := True
  map _ x := x
  act _ x := x
  map_id _ := rfl
  map_comp _ _ _ := rfl
  act_one _ := rfl
  act_mul _ _ _ := rfl
  map_act _ _ _ := rfl
  isLevel_map _ _ _ h := h
  isLevel_act _ _ _ h := h

def prod (L₁ L₂ : LevelComponent A) : LevelComponent A where
  obj T _ _ := L₁.obj T × L₂.obj T
  IsLevel W x := L₁.IsLevel W x.1 ∧ L₂.IsLevel W x.2
  map f x := (L₁.map f x.1, L₂.map f x.2)
  act C x := (L₁.act C x.1, L₂.act C x.2)
  map_id x := Prod.ext (L₁.map_id x.1) (L₂.map_id x.2)
  map_comp f g x := Prod.ext (L₁.map_comp f g x.1) (L₂.map_comp f g x.2)
  act_one x := Prod.ext (L₁.act_one x.1) (L₂.act_one x.2)
  act_mul C C' x := Prod.ext (L₁.act_mul C C' x.1) (L₂.act_mul C C' x.2)
  map_act f C x := Prod.ext (L₁.map_act f C x.1) (L₂.map_act f C x.2)
  isLevel_map f W x h := ⟨L₁.isLevel_map f W x.1 h.1, L₂.isLevel_map f W x.2 h.2⟩
  isLevel_act C W x h := ⟨L₁.isLevel_act C W x.1 h.1, L₂.isLevel_act C W x.2 h.2⟩

structure Raw (L : LevelComponent A) (T : Type u) [CommRing T] [Algebra A T] : Type u where

  curve : WeierstrassCurve T

  isUnit_Δ : IsUnit curve.Δ

  level : L.obj T

  isLevel : L.IsLevel curve level

theorem Raw.ext' {L : LevelComponent A} {T : Type u} [CommRing T] [Algebra A T] {x y : L.Raw T}
    (h₁ : x.curve = y.curve) (h₂ : x.level = y.level) : x = y := by
  cases x; cases y; cases h₁; cases h₂; rfl

def toRigid (L : LevelComponent A) : RigidWeierstrassData.{u} A where
  Raw T _ _ := L.Raw T
  curve x := x.curve
  isUnit_Δ x := x.isUnit_Δ
  mapRing f x := ⟨x.curve.map f.toRingHom, x.curve.isUnit_Δ_map f.toRingHom x.isUnit_Δ, L.map f x.level,
    L.isLevel_map f _ _ x.isLevel⟩
  curve_mapRing _ _ := rfl
  mapRing_id x := Raw.ext' (x.curve.map_id) (L.map_id x.level)
  mapRing_comp f g x := Raw.ext' (x.curve.map_map f.toRingHom g.toRingHom).symm (L.map_comp f g x.level)
  act C x := ⟨C • x.curve, x.curve.isUnit_Δ_variableChange C x.isUnit_Δ, L.act C x.level,
    L.isLevel_act C _ _ x.isLevel⟩
  act_one x := Raw.ext' (one_smul _ _) (L.act_one x.level)
  act_mul C C' x := Raw.ext' (mul_smul C C' _) (L.act_mul C C' x.level)
  curve_act _ _ := rfl
  mapRing_act f C x := Raw.ext' (x.curve.map_variableChange C f.toRingHom).symm (L.map_act f C x.level)

end LevelComponent

section Gamma0

variable {T : Type u} [CommRing T]

def kernelVariableChangeDeg (C : WeierstrassCurve.VariableChange T) (d : ℕ) (h : T[X]) : T[X] :=
  Polynomial.C (((C.u⁻¹ : Tˣ) : T) ^ (2 * d)) *
    h.comp (Polynomial.C ((C.u : Tˣ) : T) ^ 2 * X + Polynomial.C C.r)

theorem kernelVariableChangeDeg_eq_kernelVariableChange (C : WeierstrassCurve.VariableChange T) (h : T[X]) :
    kernelVariableChangeDeg C h.natDegree h = WeierstrassCurve.kernelVariableChange C h := rfl

theorem kernelVariableChangeDeg_one (d : ℕ) (h : T[X]) :
    kernelVariableChangeDeg (1 : WeierstrassCurve.VariableChange T) d h = h := by
  simp [kernelVariableChangeDeg, WeierstrassCurve.VariableChange.one_def]

theorem kernelVariableChangeDeg_mul (C C' : WeierstrassCurve.VariableChange T) (d : ℕ) (h : T[X]) :
    kernelVariableChangeDeg (C * C') d h = kernelVariableChangeDeg C d (kernelVariableChangeDeg C' d h) := by
  simp only [kernelVariableChangeDeg, WeierstrassCurve.VariableChange.mul_def, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.pow_comp, Polynomial.X_comp,
    mul_inv, Units.val_mul, mul_pow, map_mul, map_pow, map_add]
  have hin : (Polynomial.C ((C'.u : Tˣ) : T) ^ 2 * (Polynomial.C ((C.u : Tˣ) : T) ^ 2 * X + Polynomial.C C.r) +
      Polynomial.C C'.r : T[X]) = Polynomial.C ((C.u : Tˣ) : T) ^ 2 * Polynomial.C ((C'.u : Tˣ) : T) ^ 2 * X +
      (Polynomial.C C.r * Polynomial.C ((C'.u : Tˣ) : T) ^ 2 + Polynomial.C C'.r) := by ring
  rw [hin]; ring

theorem kernelVariableChangeDeg_map {T' : Type u} [CommRing T'] (f : T →+* T')
    (C : WeierstrassCurve.VariableChange T) (d : ℕ) (h : T[X]) :
    (kernelVariableChangeDeg C d h).map f = kernelVariableChangeDeg (C.map f) d (h.map f) := by
  simp only [kernelVariableChangeDeg, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_comp,
    Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, WeierstrassCurve.VariableChange.map,
    map_pow, Units.coe_map_inv, Units.coe_map, MonoidHom.coe_coe]

end Gamma0

def gamma0Component (A : Type u) [CommRing A] (N : ℕ)
    (hN : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (h : T[X]), W.IsCyclicKernel N h → (C • W).IsCyclicKernel N (kernelVariableChangeDeg C ((N - 1) / 2) h)) :
    LevelComponent A where
  obj T _ _ := T[X]
  IsLevel W h := W.IsCyclicKernel N h
  map f h := h.map f.toRingHom
  act C h := kernelVariableChangeDeg C ((N - 1) / 2) h
  map_id _ := Polynomial.map_id
  map_comp f g h := (Polynomial.map_map f.toRingHom g.toRingHom h).symm
  act_one h := kernelVariableChangeDeg_one _ h
  act_mul C C' h := kernelVariableChangeDeg_mul C C' _ h
  map_act f C h := kernelVariableChangeDeg_map f.toRingHom C _ h
  isLevel_map f W _ hh := WeierstrassCurve.IsCyclicKernel.map W f.toRingHom hh
  isLevel_act C W h hh := hN _ W C h hh

section LevelP

variable {T : Type u} [CommRing T]

theorem LevelPData.variableChange_one (D : LevelPData T) :
    D.variableChange (1 : WeierstrassCurve.VariableChange T) = D := by
  ext <;> simp [LevelPData.variableChange, WeierstrassCurve.VariableChange.one_def]

theorem LevelPData.variableChange_mul (C C' : WeierstrassCurve.VariableChange T) (D : LevelPData T) :
    D.variableChange (C * C') = (D.variableChange C').variableChange C := by
  set v : T := ((C.u⁻¹ : Tˣ) : T) with hv
  set v' : T := ((C'.u⁻¹ : Tˣ) : T) with hv'
  set u' : T := ((C'.u : Tˣ) : T) with hu'
  have h1 : v' * u' = 1 := by rw [hv', hu', Units.inv_mul]
  have h2 : v' ^ 2 * u' ^ 2 = 1 := by rw [← mul_pow, h1, one_pow]
  have h3 : v' ^ 3 * u' ^ 3 = 1 := by rw [← mul_pow, h1, one_pow]
  ext <;> simp only [LevelPData.variableChange, WeierstrassCurve.VariableChange.mul_def, mul_inv, Units.val_mul,
      mul_pow, ← hv, ← hv', ← hu']
  · linear_combination (-(v ^ 2) * C.r) * h2
  · linear_combination (-(v ^ 3) * C.s * (D.xP - C'.r) * v' ^ 2) * h1 + (v ^ 3 * (C.s * C.r - C.t)) * h3
  · linear_combination (-(v ^ 2) * C.r) * h2
  · linear_combination (-(v ^ 3) * C.s * (D.xQ - C'.r) * v' ^ 2) * h1 + (v ^ 3 * (C.s * C.r - C.t)) * h3

theorem LevelPData.map_variableChange {T' : Type u} [CommRing T'] (f : T →+* T')
    (C : WeierstrassCurve.VariableChange T) (D : LevelPData T) :
    (D.variableChange C).map f = (D.map f).variableChange (C.map f) := by
  ext <;> simp [LevelPData.variableChange, LevelPData.map, WeierstrassCurve.VariableChange.map, map_mul, map_sub,
    map_pow]

end LevelP

def levelPComponent (A : Type u) [CommRing A] (ℓ : ℕ)
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : LevelPData T), IsLevelPStructure W ℓ D → IsLevelPStructure (C • W) ℓ (D.variableChange C)) :
    LevelComponent A where
  obj T _ _ := LevelPData T
  IsLevel W D := IsLevelPStructure W ℓ D
  map f D := D.map f.toRingHom
  act C D := D.variableChange C
  map_id _ := rfl
  map_comp _ _ _ := rfl
  act_one D := LevelPData.variableChange_one D
  act_mul C C' D := LevelPData.variableChange_mul C C' D
  map_act f C D := LevelPData.map_variableChange f.toRingHom C D
  isLevel_map f _ _ hD := hD.map f.toRingHom
  isLevel_act C W D hD := hℓ _ W C D hD

def weierstrassLevelRigidData (A : Type u) [CommRing A] (ℓ N : ℕ)
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : LevelPData T), IsLevelPStructure W ℓ D → IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hN : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (h : T[X]), W.IsCyclicKernel N h → (C • W).IsCyclicKernel N (kernelVariableChangeDeg C ((N - 1) / 2) h))
    (Dq : LevelComponent A) : RigidWeierstrassData.{u} A :=
  ((gamma0Component A N hN).prod ((levelPComponent A ℓ hℓ).prod Dq)).toRigid

end ModularCurve

end


