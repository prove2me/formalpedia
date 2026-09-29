-- Prove2me | Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
-- name    : ModularCurve_ReductionOfPointsAgreesModL
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/70fad494-f7f0-50df-b91c-32a450d5f53b
-- title:
--   Agreement of point reduction with divisor-class reduction mod ℓ
-- statement:
--   For a level $p \ge 1$, a valuation subring $A \subseteq \overline{\mathbb{Q}}$ with residue field $\kappa_A =$ `IsLocalRing.ResidueField ↥A`, a commutative ring $R$, a scheme morphism $f \colon J \to \operatorname{Spec} R$ and a morphism $\sigma \colon \operatorname{Spec} A \to \operatorname{Spec} R$, the predicate `ReductionOfPointsAgreesModL` expresses a compatibility between two reduction processes on the points of $J$. Here `SchemeHomOver g f` denotes the type of pairs consisting of a morphism $\varphi$ into $J$ together with a proof that $\varphi$ followed by $f$ equals $g$, so that its elements are points of $J$ over the base morphism $g$; and `schemeHomOverComp ψ` sends such a point to its precomposition with $\psi$. Two bijections are taken as parameters: `ptsGen`, identifying `JZero p`, the group $\mathrm{Pic}^0$ of the degree-zero divisor classes of the modular function field of level $p$ over $\overline{\mathbb{Q}}$, with the points of $J$ over $\operatorname{Spec} \overline{\mathbb{Q}} \to \operatorname{Spec} A \xrightarrow{\sigma} \operatorname{Spec} R$ (the structural map of the generic test object, built from the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$); and `ptsSp`, identifying `JZeroC (IsLocalRing.ResidueField ↥A) p`, the degree-zero divisor class group of the level-$p$ modular function field over $\kappa_A$, with the points of $J$ over $\operatorname{Spec} \kappa_A \to \operatorname{Spec} A \xrightarrow{\sigma} \operatorname{Spec} R$ (built from the residue map). The assertion is then: for every $x$ in `JZero p` there exists a point $\tilde x$ of $J$ over $\sigma$ whose restriction along $\operatorname{Spec} \overline{\mathbb{Q}} \to \operatorname{Spec} A$ is $\mathrm{ptsGen}(x)$ and whose restriction along $\operatorname{Spec} \kappa_A \to \operatorname{Spec} A$ is $\mathrm{ptsSp}(\mathrm{red}_A(x))$, where $\mathrm{red}_A =$ `reductionModL A p` is the additive map on divisor classes induced by a reduction of places along the residue map of $A$ (the zero map when no such reduction datum exists). Only existence of $\tilde x$ is required; no uniqueness is asserted, and the predicate is a condition on the chosen model $f$, $\sigma$ and on the chosen point parametrisations. The accompanying lemma `reductionOfPointsAgreesModL_iff` records the predicate's unfolding.
--
--   **Relation to Mathlib.** Mathlib has no notion of reduction of divisor classes on modular curves, nor of this compatibility; both are the project's own. The type `SchemeHomOver g f` of points over a base morphism is a project abbreviation for a subtype of scheme morphisms; it is in bijection with the hom sets of Mathlib's `Over` category via `schemeHomOverEquivOverHom`.
--
--   **Where it is used.** The predicate is imposed as a hypothesis on integral models of the Jacobian $J_0(p)$: it says that extending a $\overline{\mathbb{Q}}$-point across the valuation ring $A$ and specialising to the residue field computes the same thing as Deuring-style reduction of the corresponding degree-zero divisor class. It is used by the statements about good reduction of $J_0(p)$ and about its torsion, which feed the Galois-representation side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_ReductionOfPointsAgreesModL.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ReductionModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace ModularCurve

def ReductionOfPointsAgreesModL (p : ℕ) [NeZero p]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    {R : Type} [CommRing R] {J : Scheme.{0}} (f : J ⟶ Spec (CommRingCat.of R))
    (σ : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of R))
    (ptsGen : JZero p ≃
      SchemeHomOver (Spec.map (CommRingCat.ofHom A.subtype) ≫ σ) f)
    (ptsSp : JZeroC (IsLocalRing.ResidueField ↥A) p ≃
      SchemeHomOver (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ σ) f) : Prop :=
  ∀ x : JZero p, ∃ xA : SchemeHomOver σ f,
    schemeHomOverComp (Spec.map (CommRingCat.ofHom A.subtype)) rfl xA = ptsGen x ∧
    schemeHomOverComp (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) rfl xA
      = ptsSp (reductionModL A p x)

theorem reductionOfPointsAgreesModL_iff (p : ℕ) [NeZero p]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    {R : Type} [CommRing R] {J : Scheme.{0}} (f : J ⟶ Spec (CommRingCat.of R))
    (σ : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of R))
    (ptsGen : JZero p ≃
      SchemeHomOver (Spec.map (CommRingCat.ofHom A.subtype) ≫ σ) f)
    (ptsSp : JZeroC (IsLocalRing.ResidueField ↥A) p ≃
      SchemeHomOver (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ σ) f) :
    ReductionOfPointsAgreesModL p A f σ ptsGen ptsSp ↔
      ∀ x : JZero p, ∃ xA : SchemeHomOver σ f,
        schemeHomOverComp (Spec.map (CommRingCat.ofHom A.subtype)) rfl xA = ptsGen x ∧
        schemeHomOverComp (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) rfl xA
          = ptsSp (reductionModL A p x) :=
  Iff.rfl

end ModularCurve

end


