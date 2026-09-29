-- Prove2me | Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
-- name    : AlgebraicGeometry_RelEffCartierDivTwist2
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/edf8d759-fffb-59d0-89a6-5cbc279ffaae
-- title:
--   Rigidified twist of a relative effective Cartier divisor
-- statement:
--   Throughout, $R$ is a commutative ring, $c \colon C \to \operatorname{Spec} R$ a scheme over $R$, and $\varepsilon$ an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c`, i.e. a morphism $\varepsilon_1 \colon \operatorname{Spec} R \to C$ with $\varepsilon_1$ followed by $c$ the identity, so a section of $c$; and $t \colon T \to \operatorname{Spec} R$ is a further $R$-scheme. The first result, `RelPicard.rigSection_eq_graphOver`, identifies two descriptions of the induced section $T \to C \times_{\operatorname{Spec} R} T$: the morphism `RelPicard.rigSection c t ε`, defined as the pullback lift of the pair $(t$ followed by $\varepsilon_1, \mathrm{id}_T)$, equals `graphOver c (t ≫ ε.1) _`, the graph of $t$ followed by $\varepsilon_1$ as a morphism over $\operatorname{Spec} R$; the two agree on the nose.
--
--   The main definition, `RelEffCartierDiv.twistModule`, attaches to a relative effective Cartier divisor $D$ of degree $r$ on $C \times_{\operatorname{Spec} R} T$ over $T$ — a structure consisting of an ideal sheaf datum $\mathcal I_D$ whose closed subscheme maps to $T$ finitely, flatly, locally of finite presentation and with fibre rank $r$ at every point of $T$ — the sheaf of modules on $C \times_{\operatorname{Spec} R} T$ obtained by rigidifying $M := \mathcal I_D^{\vee} \otimes \mathcal I_{\varepsilon_T}^{\,r}$ along the section $\varepsilon_T =$ `rigSection c t ε` and the projection $\mathrm{pr}_2$. Here $\mathcal I_D^{\vee}$ is `D.lineBundle`, the internal dual of the module of $\mathcal I_D$ (the kernel of $\mathcal O \to \iota_*\mathcal O$ for the associated closed subscheme), $\mathcal I_{\varepsilon_T}$ is `RelPicard.sectionIdeal c ε t`, the kernel ideal sheaf datum of $\varepsilon_T$, and rigidification means $M \otimes \mathrm{pr}_2^{*}\bigl((\varepsilon_T^{*}M)^{\vee}\bigr)$. Thus the twist is a canonically rigidified model of $\mathcal O(D - r\varepsilon_T)$. It is defined for every such $D$, with no further hypotheses on $c$. The companion `twistModule_def` records this formula.
--
--   **Relation to Mathlib.** Mathlib supplies ideal sheaf data on a scheme with their powers and associated closed subschemes, and the symmetric monoidal closed category of sheaves of modules in which the duals and tensor products are taken; the notion of relative effective Cartier divisor used here, the module attached to an ideal sheaf datum, and the rigidification operation are the project's own.
--
--   **Where it is used.** The twist provides the line bundle underlying a rigidified line bundle attached to a family of divisors, and so feeds the relative Picard functor together with the Picard and theta bundles built from it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelEffCartierDivTwist2.lean

import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra

noncomputable section

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {C : Scheme.{u}}

theorem RelPicard.rigSection_eq_graphOver (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    RelPicard.rigSection c t ε =
      graphOver c (t ≫ ε.1) (by rw [Category.assoc, ε.2, Category.comp_id]) := rfl

def RelEffCartierDiv.twistModule (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {r : ℕ} {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (D : RelEffCartierDiv c r t) : (pullback c t).Modules :=
  Scheme.Modules.rigidify (RelPicard.rigSection c t ε) (pullback.snd c t)
    (D.lineBundle ⊗ ((RelPicard.sectionIdeal c ε t) ^ r).module)

theorem RelEffCartierDiv.twistModule_def (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {r : ℕ} {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (D : RelEffCartierDiv c r t) :
    D.twistModule c ε = Scheme.Modules.rigidify (RelPicard.rigSection c t ε) (pullback.snd c t)
      (D.lineBundle ⊗ ((RelPicard.sectionIdeal c ε t) ^ r).module) := rfl

end AlgebraicGeometry

end


