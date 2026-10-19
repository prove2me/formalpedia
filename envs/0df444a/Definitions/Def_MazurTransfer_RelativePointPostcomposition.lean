-- Prove2me | Definitions.Def_MazurTransfer_RelativePointPostcomposition
-- name    : MazurTransfer_RelativePointPostcomposition
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T02:21:40.756023+00:00
-- url     : https://prove2.me/theorems/214b7f1b-b09a-4c10-bae7-9ec2fb83ebf4
-- title:
--   Postcomposition of relative scheme points along a morphism over the base
-- statement:
--   Let $X$ and $Y$ be schemes over $\operatorname{Spec}R$, and let $a:X\to Y$ be a morphism over that base. For a scheme $T$ with fixed map $t:T\to\operatorname{Spec}R$, postcomposition defines
--   $$X(T)\longrightarrow Y(T),\qquad p\longmapsto a\circ p,$$
--   where both point sets consist of morphisms lying over $t$.
--
--   This file supplies only that constructor and its base-compatibility proof. It is used to state injectivity of the actual integral order-thirteen Abel–Jacobi morphism; specialization naturality and injectivity are separate theorems.
-- source:
--   Exact structural constructor from MazurTheorem, ProperPointSpecializationNaturality.lean, postcomp. The declaration body and complete original type are preserved; unrelated specialization proofs and the unused namespace opening are removed from this interface. Apache-2.0.

/- Design boundary: postcompose relative scheme points with a morphism over the base.
Named downstream consumer: the integral order13 Abel-Jacobi injection.
The original source header below is retained verbatim; specialization proofs are not part of this constructor interface. -/
/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: specialization of actual proper scheme points commutes
with any morphism over the base, by uniqueness of valuation-ring extension.
Named downstream consumer: transfer injectivity of rational Picard
specialization to curve specialization through an integral Abel-Jacobi map.
-/
import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_JacJ1Iface


noncomputable section
namespace MazurTransfer.ProperPointSpecializationNaturality
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u
variable {R B K k : Type u} [CommRing R] [CommRing B] [IsDomain B] [ValuationRing B]
  [Field K] [Algebra B K] [IsFractionRing B K] [CommRing k]
  {X Y : Scheme.{u}} (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of R))
  (a : X ⟶ Y) (ha : a ≫ g = f)

def postcomp {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) (p : SchemeHomOver t f) :
    SchemeHomOver t g :=
  ⟨p.val ≫ a, (Category.assoc _ _ _).trans
    ((congrArg (fun b => p.val ≫ b) ha).trans p.property)⟩

variable [IsProper f] [IsProper g] (t : Spec (.of B) ⟶ Spec (.of R))









end MazurTransfer.ProperPointSpecializationNaturality




#print axioms MazurTransfer.ProperPointSpecializationNaturality.postcomp


