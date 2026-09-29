-- Prove2me | Definitions.Def_NeronModelInfra_SmoothnessDefect
-- name    : NeronModelInfra_SmoothnessDefect
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/ac8354dd-1748-512b-91bd-70b7c5fbde55
-- title:
--   Néron's measure for the defect of smoothness
-- statement:
--   Fix a commutative ring $R$, a scheme $X$ with a morphism $f\colon X \to \operatorname{Spec} R$, a local ring $R'$ and a morphism $a\colon \operatorname{Spec} R' \to X$, that is an $R'$-valued point of $X$. Write $x = a(\mathfrak m_{R'})$ for the image of the closed point of $\operatorname{Spec} R'$ and $B = \mathcal O_{X,x}$ for the stalk at $x$. The module provides the two algebra structures needed to speak of differentials at such a point. `stalkAlgebraMap` is the ring homomorphism $R \to B$ obtained by composing the inverse of the canonical identification $R \cong \Gamma(\operatorname{Spec} R, \mathcal O)$ with the map on global sections induced by $f$ and then with the germ map $\Gamma(X, \mathcal O_X) \to \mathcal O_{X,x}$; `stalkAlgebra` is the resulting $R$-algebra structure on $B$, and `stalkAlgebraMap_apply` records its value on an element $r \in R$. Dually, `pointAlgebra` is the $B$-algebra structure on $R'$ given by the local homomorphism $\mathcal O_{X,x} \to R'$ induced by $a$ on stalks at closed points.
--
--   With these in place, `smoothnessDefect f a` is defined to be
--   $$\delta(a) = \operatorname{length}_{R'}\bigl(\,\mathrm{tors}_{R'}\,(R' \otimes_B \Omega_{B/R})\,\bigr) \in \mathbb N \cup \{\infty\},$$
--   the length, as an $R'$-module, of the torsion submodule of the base change along $B \to R'$ of the module of Kähler differentials of $B$ over $R$; the value is taken in $\mathbb N_\infty$, so no finiteness is presupposed. The companion `smoothnessDefect_def` restates this unfolding. Finally, `stalkAlgebraMap_id` identifies the $R$-algebra structure on the stalk of $\operatorname{Spec} R$ at a prime $\mathfrak p$ arising from the identity morphism with the canonical map $R \to \mathcal O_{\mathfrak p}$ into the structure-sheaf stalk, and `smoothnessDefect_id` deduces that $\delta(a) = 0$ for every local-ring-valued point $a$ of $\operatorname{Spec} R$ over the identity: the stalk is a localisation of $R$, hence formally unramified over $R$, so $\Omega_{B/R}$ and its base change vanish.
--
--   **Relation to Mathlib.** Mathlib supplies the ingredients — `Module.length`, `Submodule.torsion`, Kähler differentials `Ω[B⁄R]`, and `Scheme.stalkClosedPointTo` — but not the invariant itself, which is the project's own. The $R$-algebra structure on a stalk of an arbitrary $R$-scheme given here extends Mathlib's `StructureSheaf.stalkAlgebra` for $\operatorname{Spec} R$ itself, with which it is shown to agree.
--
--   **Where it is used.** The invariant $\delta$ is the quantity along which Néron's smoothening process is organised: it vanishes exactly when the point lands in the smooth locus, is bounded when the generic fibre is smooth, and drops under dilatation of a permissible centre. It underlies the construction of Néron models of elliptic curves used in the study of the Frey curve and its Galois representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NeronModelInfra_SmoothnessDefect.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace NeronModelInfra

def stalkAlgebraMap {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (x : X) : R →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x trivial).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem stalkAlgebraMap_apply {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (x : X) (r : R) :
    stalkAlgebraMap f x r =
      (X.presheaf.germ ⊤ x trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) :=
  rfl

abbrev stalkAlgebra {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (x : X) : Algebra R (X.presheaf.stalk x) :=
  (stalkAlgebraMap f x).toAlgebra

abbrev pointAlgebra {X : Scheme.{u}} {R' : Type u} [CommRing R'] [IsLocalRing R']
    (a : Spec (CommRingCat.of R') ⟶ X) :
    Algebra (X.presheaf.stalk (a (IsLocalRing.closedPoint R'))) R' :=
  (Scheme.stalkClosedPointTo a).hom.toAlgebra

def smoothnessDefect {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    {R' : Type u} [CommRing R'] [IsLocalRing R'] (a : Spec (CommRingCat.of R') ⟶ X) : ℕ∞ :=
  letI : Algebra R (X.presheaf.stalk (a (IsLocalRing.closedPoint R'))) :=
    stalkAlgebra f (a (IsLocalRing.closedPoint R'))
  letI : Algebra (X.presheaf.stalk (a (IsLocalRing.closedPoint R'))) R' := pointAlgebra a
  Module.length R'
    (Submodule.torsion R'
      (R' ⊗[X.presheaf.stalk (a (IsLocalRing.closedPoint R'))]
        Ω[X.presheaf.stalk (a (IsLocalRing.closedPoint R'))⁄R]))

theorem smoothnessDefect_def {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    {R' : Type u} [CommRing R'] [IsLocalRing R'] (a : Spec (CommRingCat.of R') ⟶ X) :
    smoothnessDefect f a =
      (letI : Algebra R (X.presheaf.stalk (a (IsLocalRing.closedPoint R'))) :=
        stalkAlgebra f (a (IsLocalRing.closedPoint R'))
      letI : Algebra (X.presheaf.stalk (a (IsLocalRing.closedPoint R'))) R' := pointAlgebra a
      Module.length R'
        (Submodule.torsion R'
          (R' ⊗[X.presheaf.stalk (a (IsLocalRing.closedPoint R'))]
            Ω[X.presheaf.stalk (a (IsLocalRing.closedPoint R'))⁄R]))) :=
  rfl

section Gate

variable (R : Type u) [CommRing R]

theorem stalkAlgebraMap_id (p : PrimeSpectrum R) :
    stalkAlgebraMap (𝟙 (Spec (CommRingCat.of R))) p = (StructureSheaf.toStalk R p).hom := by
  apply RingHom.ext
  intro r
  simp only [stalkAlgebraMap, Scheme.Hom.id_appTop, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_id, RingHom.id_apply, StructureSheaf.toStalk, CommRingCat.hom_comp,
    Scheme.ΓSpecIso_inv, CommRingCat.hom_ofHom]
  rfl

theorem smoothnessDefect_id {R' : Type u} [CommRing R'] [IsLocalRing R']
    (a : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) :
    smoothnessDefect (𝟙 (Spec (CommRingCat.of R))) a = 0 := by
  rw [smoothnessDefect_def]
  set p : PrimeSpectrum R := a (IsLocalRing.closedPoint R') with hp
  letI iRB : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk p) :=
    stalkAlgebra (𝟙 (Spec (CommRingCat.of R))) p
  letI : Algebra ((Spec (CommRingCat.of R)).presheaf.stalk p) R' := pointAlgebra a
  have hAlg : iRB = StructureSheaf.stalkAlgebra R p := by
    refine Algebra.algebra_ext _ _ fun r => ?_
    change stalkAlgebraMap (𝟙 (Spec (CommRingCat.of R))) p r = _
    rw [stalkAlgebraMap_id]
    rfl
  have hunr : @Algebra.FormallyUnramified R ((Spec (CommRingCat.of R)).presheaf.stalk p) _ _ iRB := by
    rw [hAlg]
    exact @Algebra.FormallyUnramified.of_isLocalization _ _ _ _ p.asIdeal.primeCompl _
      (StructureSheaf.IsLocalization.to_stalk R p)
  haveI : Subsingleton Ω[(Spec (CommRingCat.of R)).presheaf.stalk p⁄R] :=
    Algebra.FormallyUnramified.subsingleton_kaehlerDifferential
  haveI : Subsingleton
      (R' ⊗[(Spec (CommRingCat.of R)).presheaf.stalk p] Ω[(Spec (CommRingCat.of R)).presheaf.stalk p⁄R]) :=
    inferInstance
  exact Module.length_eq_zero

end Gate

end NeronModelInfra

end

/--
info: 'NeronModelInfra.smoothnessDefect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.smoothnessDefect

/--
info: 'NeronModelInfra.smoothnessDefect_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.smoothnessDefect_id


