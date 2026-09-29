-- Prove2me | Definitions.Def_ModularCurve_WeierstrassGamma1Pow
-- name    : ModularCurve_WeierstrassGamma1Pow
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/4b377590-6ec1-5339-9dee-93863c2e6eb6
-- title:
--   Weierstrass Γ₁(ℓ)-point level component and associated rigid data
-- statement:
--   For a commutative ring $A$, a natural number $\ell$ and an $A$-algebra $T$, the carrier used here is [`ModularCurve.LevelPData T`](../def/ModularCurve_KatzLevelP.html#L43), the datum of two affine points recorded by their coordinates $x_P,y_P,x_Q,y_Q \in T$, with its base-change operation `map` along a ring homomorphism and its `variableChange` action of `WeierstrassCurve.VariableChange T`. The predicate [`ModularCurve.IsGamma1Point W ℓ D`](../def/ModularCurve_WeierstrassGamma1Pow.html#L10), for a Weierstrass curve $W$ over $T$, is a structure with four fields: $(x_P,y_P)$ satisfies the affine Weierstrass equation of $W$; the $\ell$-th pre-division polynomial of $W$ vanishes at $x_P$, i.e. $(W.\mathrm{preΨ}\ \ell)(x_P)=0$; and $x_Q=x_P$, $y_Q=y_P$, so that the second point is a duplicate of the first and the transport laws already available for `LevelPData` can be reused. Thus the condition is a condition on the chosen Weierstrass model: it asserts only that $x_P$ is a root of the $\ell$-division polynomial, with no exact-order, primitivity, or compatibility-with-other-slots requirement. [`ModularCurve.IsGamma1Point.map`](../def/ModularCurve_WeierstrassGamma1Pow.html#L24) records that the predicate is preserved by a ring homomorphism $f : A \to B$, applied to $W$ and to the coordinates of $D$.
--
--   [`ModularCurve.gamma1Component A ℓ hℓ`](../def/ModularCurve_WeierstrassGamma1Pow.html#L33) packages this as a `LevelComponent A`: objects `LevelPData T`, level condition `IsGamma1Point W ℓ`, functoriality by coordinatewise base change, and the action of variable changes by `LevelPData.variableChange`; the compatibility of the level condition with variable changes is not proved here but taken as the hypothesis `hℓ`. Finally [`WeierstrassCurve.DrinfeldGlobal.rigidDataGamma1Pow A ℓ M' q hℓ hM 𝒢 𝒯`](../def/ModularCurve_WeierstrassGamma1Pow.html#L53) is the `RigidWeierstrassData A` obtained from the triple product of the $\Gamma_0(M')$ prime-power kernel-polynomial component, this $\Gamma_1(\ell)$-point component, and the Drinfeld basis component of level $q$ attached to $𝒢$ and $𝒯$; its points over $T$ are equivalence classes, for the variable-change relation, of quadruples consisting of a Weierstrass curve with invertible discriminant together with the three level data.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient notions used: `WeierstrassCurve`, its pre-division polynomials `preΨ`, affine equations, and variable changes. The level carriers and bookkeeping structures (`LevelPData`, `LevelComponent`, `RigidWeierstrassData`) are the project's own; Mathlib has no notion of level structure on a Weierstrass model.
--
--   **Where it is used.** These data feed the project's Weierstrass-model description of modular curves with auxiliary level structure, in the form used to compare Drinfeld-basis level data with the $\Gamma_0$- and $\Gamma_1$-type conditions appearing in the modularity-lifting argument. The $\Gamma_1(\ell)$ slot replaces a full level-$\ell$ basis by a single point whose $x$-coordinate kills the $\ell$-division polynomial; conditions relating this point to the $\Gamma_0(M')$ kernel polynomial are not part of the predicate and must be supplied separately by users of the datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_WeierstrassGamma1Pow.lean

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

namespace ModularCurve

structure IsGamma1Point {A : Type u} [CommRing A] (W : WeierstrassCurve A) (ℓ : ℕ) (D : LevelPData A) : Prop where

  equation_P : W.toAffine.Equation D.xP D.yP

  preΨ_P : (W.preΨ ℓ).eval D.xP = 0

  xQ_eq : D.xQ = D.xP

  yQ_eq : D.yQ = D.yP

namespace IsGamma1Point

variable {A : Type u} {B : Type u} [CommRing A] [CommRing B] {W : WeierstrassCurve A} {ℓ : ℕ} {D : LevelPData A}

theorem map (h : IsGamma1Point W ℓ D) (f : A →+* B) : IsGamma1Point (W.map f) ℓ (D.map f) where
  equation_P := h.equation_P.map f
  preΨ_P := by
    rw [LevelPData.map_xP, WeierstrassCurve.map_preΨ, Polynomial.eval_map, Polynomial.eval₂_at_apply, h.preΨ_P, map_zero]
  xQ_eq := by rw [LevelPData.map_xQ, LevelPData.map_xP, h.xQ_eq]
  yQ_eq := by rw [LevelPData.map_yQ, LevelPData.map_yP, h.yQ_eq]

end IsGamma1Point

noncomputable def gamma1Component (A : Type u) [CommRing A] (ℓ : ℕ)
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : LevelPData T), IsGamma1Point W ℓ D → IsGamma1Point (C • W) ℓ (D.variableChange C)) :
    LevelComponent A where
  obj T _ _ := LevelPData T
  IsLevel W D := IsGamma1Point W ℓ D
  map f D := D.map f.toRingHom
  act C D := D.variableChange C
  map_id _ := rfl
  map_comp _ _ _ := rfl
  act_one D := LevelPData.variableChange_one D
  act_mul C C' D := LevelPData.variableChange_mul C C' D
  map_act f C D := LevelPData.map_variableChange f.toRingHom C D
  isLevel_map f _ _ hD := hD.map f.toRingHom
  isLevel_act C W D hD := hℓ _ W C D hD

end ModularCurve

namespace WeierstrassCurve.DrinfeldGlobal

noncomputable def rigidDataGamma1Pow (A : Type u) [CommRing A] (ℓ M' q : ℕ)
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓ D →
        ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q) : ModularCurve.RigidWeierstrassData.{u} A :=
  ((ModularCurve.gamma0PowComponent A M' hM).prod
    ((ModularCurve.gamma1Component A ℓ hℓ).prod (levelComponent A 𝒢 q 𝒯))).toRigid

end WeierstrassCurve.DrinfeldGlobal


