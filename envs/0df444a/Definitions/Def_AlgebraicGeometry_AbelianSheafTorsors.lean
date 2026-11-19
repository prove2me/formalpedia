-- Prove2me | Definitions.Def_AlgebraicGeometry_AbelianSheafTorsors
-- name    : AlgebraicGeometry_AbelianSheafTorsors
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-18T19:57:34.526561+00:00
-- url     : https://prove2.me/theorems/f27fb28e-e3c2-4a1d-9e19-30f1a7023247
-- title:
--   Torsors under an abelian sheaf
-- statement:
--   A torsor under an abelian sheaf is a sheaf of sets with local sections, equipped with a natural difference map satisfying the triangle identity. Taking differences from any section gives a bijection with the group of sections on the same object. The definitions also specify equivariant isomorphism and a map from pairs of sections that adds their differences.
-- source:
--   Stacks Project, Section 21.4, https://stacks.math.columbia.edu/tag/03AG.

import Mathlib

section
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open CategoryTheory Opposite

namespace PhilipponTorsorPresheafDifference
universe u v w
variable {C : Type u} [Category.{v} C]

/-- A presheaf with subtraction taking values in a fixed abelian
presheaf. The subtraction of a torsor satisfies these two identities. -/
structure Difference (G : Cᵒᵖ ⥤ AddCommGrpCat.{w}) where
  P : Cᵒᵖ ⥤ Type w
  diff (U : Cᵒᵖ) : P.obj U → P.obj U → G.obj U
  diff_add_diff (U : Cᵒᵖ) (x y z : P.obj U) : diff U x y + diff U y z = diff U x z
  map_diff {U V : Cᵒᵖ} (f : U ⟶ V) (x y : P.obj U) :
    G.map f (diff U x y) = diff V (P.map f x) (P.map f y)

end PhilipponTorsorPresheafDifference
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory Opposite

namespace PhilipponTorsorInvariantDescent
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The sieve of arrows with a section of the given presheaf on their
source. Restriction of a section makes it downward closed. -/
def presence (P : Cᵒᵖ ⥤ Type w) (T : C) : Sieve T where
  arrows := fun V _ => Nonempty (P.obj (op V))
  downward_closed := fun {_ _ _} h g => h.map (P.map g.op)

end PhilipponTorsorInvariantDescent
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open PhilipponTorsorInvariantDescent PhilipponTorsorPresheafDifference

namespace PhilipponTorsorSectionFibers
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A torsor under an abelian sheaf, specified by its difference map.
At a chosen local section, taking differences is a bijection. -/
structure Torsor (G : Sheaf J AddCommGrpCat.{w}) where
  D : Difference G.obj
  isSheaf : Presheaf.IsSheaf J D.P
  locally_nonempty (U : C) : presence D.P U ∈ J U
  diff_bijective (U : Cᵒᵖ) (p : D.P.obj U) : Function.Bijective (fun q => D.diff U q p)

end PhilipponTorsorSectionFibers
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open PhilipponTorsorInvariantDescent
open PhilipponTorsorSectionFibers

namespace PhilipponTorsorFiberComparison
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- An isomorphism of section presheaves that respects the torsor
differences, equivalently the action of the abelian sheaf. -/
def Equivalent {G : Sheaf J AddCommGrpCat.{w}} (P Q : Torsor G) : Prop :=
  ∃ e : P.D.P ≅ Q.D.P, ∀ (U : Cᵒᵖ) (p q : P.D.P.obj U),
    Q.D.diff U (e.hom.app U p) (e.hom.app U q) = P.D.diff U p q

end PhilipponTorsorFiberComparison
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open PhilipponTorsorInvariantDescent PhilipponTorsorPresheafDifference
open PhilipponTorsorSectionFibers
open PhilipponTorsorFiberComparison

namespace PhilipponTorsorClassification
universe u v w w'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
/-- Simultaneous pairs of sections carry the sum of the two differences. -/
def pair {G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (D E : Difference G) : Difference G where
  P :=
    { obj U := D.P.obj U × E.P.obj U
      map f := ↾fun x => (D.P.map f x.1, E.P.map f x.2)
      map_id U := by
        apply ConcreteCategory.hom_ext
        intro x
        exact Prod.ext (by simp) (by simp)
      map_comp f g := by
        apply ConcreteCategory.hom_ext
        intro x
        exact Prod.ext (by simp) (by simp) }
  diff U x y := D.diff U x.1 y.1 + E.diff U x.2 y.2
  diff_add_diff U x y z := by
    rw [add_add_add_comm, D.diff_add_diff, E.diff_add_diff]
  map_diff {U V} f x y := by
    change G.map f (D.diff U x.1 y.1 + E.diff U x.2 y.2) =
      D.diff V (D.P.map f x.1) (D.P.map f y.1) + E.diff V (E.P.map f x.2) (E.P.map f y.2)
    rw [map_add, D.map_diff, E.map_diff]

/-- A map from simultaneous sections into a third torsor which adds differences. -/
def Combines {G : Sheaf J AddCommGrpCat.{w}} (P Q R : Torsor G) : Prop :=
  ∃ m : (pair P.D Q.D).P ⟶ R.D.P,
    ∀ (U : Cᵒᵖ) (x y : (pair P.D Q.D).P.obj U),
      R.D.diff U (m.app U x) (m.app U y) = (pair P.D Q.D).diff U x y

end PhilipponTorsorClassification
end
end


