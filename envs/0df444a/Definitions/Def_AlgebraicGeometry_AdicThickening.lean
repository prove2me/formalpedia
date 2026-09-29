-- Prove2me | Definitions.Def_AlgebraicGeometry_AdicThickening
-- name    : AlgebraicGeometry_AdicThickening
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/dfaf9f89-b63c-58ef-b0ed-ae237a33ff98
-- title:
--   Adic thickenings of a scheme over an affine base
-- statement:
--   Fix a commutative ring $R$, an ideal $I \subseteq R$, a scheme $X$ and a morphism $f \colon X \to \operatorname{Spec} R$. For each natural number $n$, `adicThickeningBase I n` is the morphism $\operatorname{Spec}(R/I^{n+1}) \to \operatorname{Spec} R$ obtained by applying $\operatorname{Spec}$ to the quotient map $R \to R/I^{n+1}$ (note the index shift: the $n$-th stage uses the $(n+1)$-st power of $I$). The scheme `adicThickening f I n` is defined as Mathlib's chosen fibre product $X \times_{\operatorname{Spec} R} \operatorname{Spec}(R/I^{n+1})$, written $X_n$ below, with `adicThickeningι f I n` the first projection $\iota_n \colon X_n \to X$ and `adicThickeningToBase f I n` the second projection $X_n \to \operatorname{Spec}(R/I^{n+1})$; `adicThickeningι_comp` records the pullback square, namely that $\iota_n$ followed by $f$ equals the second projection followed by `adicThickeningBase I n`. Since $R \to R/I^{n+1}$ is surjective, `adicThickeningBase I n` is a closed immersion, and `isClosedImmersion_adicThickeningι` registers as an instance that $\iota_n$ is a closed immersion, being a pullback of one.
--
--   The comparison between consecutive stages comes from the surjection $R/I^{n+2} \to R/I^{n+1}$ induced by $I^{n+2} \subseteq I^{n+1}$: `adicThickeningBase_succ_comp` says that $\operatorname{Spec}$ of this surjection followed by `adicThickeningBase I (n+1)` is `adicThickeningBase I n`, and `adicThickeningTransition f I n` is the resulting morphism $\tau_n \colon X_n \to X_{n+1}$ determined by the universal property, characterised by the two triangles `adicThickeningTransition_ι` ($\tau_n$ followed by $\iota_{n+1}$ is $\iota_n$) and `adicThickeningTransition_toBase` ($\tau_n$ followed by the projection to $\operatorname{Spec}(R/I^{n+2})$ is the projection of $X_n$ followed by $\operatorname{Spec}$ of the quotient map). Three further lemmas, `adicThickening_def`, `adicThickeningι_def` and `adicThickeningToBase_def`, restate the definitions in terms of `pullback`, `pullback.fst` and `pullback.snd`. The module introduces vocabulary only: the tower $X_0 \hookrightarrow X_1 \hookrightarrow \cdots \hookrightarrow X$ of closed subschemes cut out by the powers of $I\mathcal{O}_X$.
--
--   **Relation to Mathlib.** Built directly on Mathlib's fibre products of schemes and on `IsClosedImmersion`; Mathlib has no packaged notion of the $I$-adic thickening tower of a scheme over $\operatorname{Spec} R$, and this module supplies it together with the transition morphisms.
--
--   **Where it is used.** These thickenings provide the standard setting in which coherent sheaves, line bundles and sections on a scheme over an $I$-adically complete base are compared with compatible systems on the closed subschemes $X_n$, as in the theorem on formal functions and Grothendieck's existence theorem; the tower is used throughout the algebraic-geometry layer of the formalisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_AdicThickening.lean

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (I : Ideal R)

abbrev adicThickeningBase (n : ℕ) : Spec (.of (R ⧸ I ^ (n + 1))) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))

def adicThickening (n : ℕ) : Scheme.{u} := pullback f (adicThickeningBase I n)

def adicThickeningι (n : ℕ) : adicThickening f I n ⟶ X := pullback.fst f (adicThickeningBase I n)

def adicThickeningToBase (n : ℕ) : adicThickening f I n ⟶ Spec (.of (R ⧸ I ^ (n + 1))) :=
  pullback.snd f (adicThickeningBase I n)

theorem adicThickeningι_comp (n : ℕ) :
    adicThickeningι f I n ≫ f = adicThickeningToBase f I n ≫ adicThickeningBase I n :=
  pullback.condition

theorem adicThickeningBase_succ_comp (n : ℕ) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1)))) ≫
      adicThickeningBase I (n + 1) = adicThickeningBase I n := by
  rw [adicThickeningBase, adicThickeningBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Ideal.Quotient.factor_comp_mk]

def adicThickeningTransition (n : ℕ) : adicThickening f I n ⟶ adicThickening f I (n + 1) :=
  pullback.lift (adicThickeningι f I n)
    (adicThickeningToBase f I n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1)))))
    (by rw [adicThickeningι_comp, Category.assoc, adicThickeningBase_succ_comp])

@[simp] theorem adicThickeningTransition_ι (n : ℕ) :
    adicThickeningTransition f I n ≫ adicThickeningι f I (n + 1) = adicThickeningι f I n := by
  rw [adicThickeningTransition]; exact pullback.lift_fst _ _ _

theorem adicThickeningTransition_toBase (n : ℕ) :
    adicThickeningTransition f I n ≫ adicThickeningToBase f I (n + 1) =
      adicThickeningToBase f I n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1)))) := by
  rw [adicThickeningTransition]; exact pullback.lift_snd _ _ _

instance isClosedImmersion_adicThickeningι (n : ℕ) : IsClosedImmersion (adicThickeningι f I n) := by
  have : IsClosedImmersion (adicThickeningBase I n) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact MorphismProperty.pullback_fst _ _ this

theorem adicThickening_def (n : ℕ) : adicThickening f I n = pullback f (adicThickeningBase I n) := rfl
theorem adicThickeningι_def (n : ℕ) : adicThickeningι f I n = pullback.fst f (adicThickeningBase I n) := rfl
theorem adicThickeningToBase_def (n : ℕ) :
    adicThickeningToBase f I n = pullback.snd f (adicThickeningBase I n) := rfl

end AlgebraicGeometry

end


