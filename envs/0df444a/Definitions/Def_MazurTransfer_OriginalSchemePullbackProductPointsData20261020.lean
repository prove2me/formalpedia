-- Prove2me | Definitions.Def_MazurTransfer_OriginalSchemePullbackProductPointsData20261020
-- name    : MazurTransfer_OriginalSchemePullbackProductPointsData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T01:15:38.732645+00:00
-- url     : https://prove2.me/theorems/18499096-e5c0-45a0-a5ef-2292c8f274a7
-- title:
--   Original scheme pullback product point equivalence
-- statement:
--   Retain the original pullback product structure morphism, forward and backward point maps and their exact point equivalence over the same fixed base. All four complete original types and four whole values, together with all generated structural certificates, are independently checked. Naturality is a separate theorem interface. Named downstream consumer: the principal-action scheme isomorphism of the actual integral nineteen norm-preimage torsor.
-- source:
--   MazurTheorem SchemePullbackProductPoints by Vas and contributors; complete original constructor types and whole values, preserving Apache-2.0 attribution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: pullback product points over a FIXED base, with EVERY
precomposition map. No change of the given structure morphisms.
Named downstream consumer: the actual integral norm-preimage torsor's
principal-action scheme isomorphism.
-/
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

noncomputable section
namespace MazurTransfer.SchemePullbackProductPoints
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
universe u
variable {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)

abbrev productStr : pullback f g ⟶ B := pullback.snd f g ≫ g

variable {T : Scheme.{u}} (t : T ⟶ B)

def toPair (b : SchemeHomOver t (productStr f g)) : SchemeHomOver t f × SchemeHomOver t g :=
  (⟨b.val ≫ pullback.fst f g, by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact b.property⟩,
   ⟨b.val ≫ pullback.snd f g, by
    rw [Category.assoc]
    exact b.property⟩)

def fromPair (p : SchemeHomOver t f × SchemeHomOver t g) : SchemeHomOver t (productStr f g) :=
  ⟨pullback.lift p.1.val p.2.val (p.1.property.trans p.2.property.symm), by
    rw [productStr, ← Category.assoc, pullback.lift_snd, p.2.property]⟩

def pointsEquiv : SchemeHomOver t (productStr f g) ≃ SchemeHomOver t f × SchemeHomOver t g where
  toFun := toPair f g t
  invFun := fromPair f g t
  left_inv b := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact pullback.lift_snd _ _ _
  right_inv p := Prod.ext (Subtype.ext (pullback.lift_fst _ _ _))
    (Subtype.ext (pullback.lift_snd _ _ _))

variable {T' : Scheme.{u}} (t' : T' ⟶ B) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')



end MazurTransfer.SchemePullbackProductPoints
#print axioms MazurTransfer.SchemePullbackProductPoints.productStr
#print axioms MazurTransfer.SchemePullbackProductPoints.toPair
#print axioms MazurTransfer.SchemePullbackProductPoints.fromPair
#print axioms MazurTransfer.SchemePullbackProductPoints.pointsEquiv


