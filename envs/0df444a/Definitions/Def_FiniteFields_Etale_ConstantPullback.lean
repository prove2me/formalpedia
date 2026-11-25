-- Prove2me | Definitions.Def_FiniteFields_Etale_ConstantPullback
-- name    : FiniteFields_Etale_ConstantPullback
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-25T11:46:51.173904+00:00
-- url     : https://prove2.me/theorems/33fac303-80d6-450d-ba78-205453d0976f
-- title:
--   Inverse image of a constant étale sheaf is constant: $f^{-1}\underline A_Y\cong\underline A_X$
-- statement:
--   For a morphism of schemes $f\colon X\to Y$ and an abelian group $A$, the inverse image of the constant étale sheaf $\underline A_Y$ is canonically isomorphic to the constant sheaf $\underline A_X$.
--
--   The isomorphism is the uniqueness isomorphism between two left adjoints of the functor of global sections (sections at the terminal object): direct image followed by global sections on $Y$ is canonically global sections on $X$, so $f^{-1}\circ(\text{constant sheaf on }Y)$ and the constant sheaf on $X$ are both left adjoint to global sections on $X$.
-- source:
--   The Stacks Project, Chapter 59 (Étale Cohomology), Section 59.36 (Inverse image).

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Definitions.Def_FiniteFields_Etale_Cohomology
import Definitions.Def_FiniteFields_Etale_ExactPullback
import Definitions.Def_FiniteFields_Etale_FiniteCoefficients
import Definitions.Def_FiniteFields_Etale_Functoriality
import Definitions.Def_FiniteFields_Etale_Sites

noncomputable section

open CategoryTheory

namespace FiniteFields.Etale

open AlgebraicGeometry CategoryTheory.Limits

universe u

-- Portage v4.33 : option nécessaire avec Mathlib `0df444a` (comme dans `Sites/Etale.lean`).
set_option backward.isDefEq.respectTransparency.types false

/-- Pushforward followed by sections at the terminal etale object is canonically sections at the
terminal etale object of the source. -/
def smallEtalePushforwardTerminalSectionsIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtalePushforward f ⋙
        (sheafSections (smallEtaleSiteTopology Y) Ab.{u + 1}).obj
          (Opposite.op (⊤_ SmallEtaleSite Y)) ≅
      (sheafSections (smallEtaleSiteTopology X) Ab.{u + 1}).obj
        (Opposite.op (⊤_ SmallEtaleSite X)) :=
  NatIso.ofComponents (fun F =>
    let e : (smallEtaleBaseChange f).obj (⊤_ SmallEtaleSite Y) ≅
        ⊤_ SmallEtaleSite X := PreservesTerminal.iso (smallEtaleBaseChange f)
    F.obj.mapIso e.symm.op) (fun {F G} α => by
      change α.hom.app _ ≫ G.obj.map _ = F.obj.map _ ≫ α.hom.app _
      exact (α.hom.naturality
        (PreservesTerminal.iso (smallEtaleBaseChange f)).inv.op).symm)

private def smallEtalePullbackConstantAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    constantSheaf (smallEtaleSiteTopology Y) Ab.{u + 1} ⋙ smallEtalePullback f ⊣
      (sheafSections (smallEtaleSiteTopology X) Ab.{u + 1}).obj
        (Opposite.op (⊤_ SmallEtaleSite X)) :=
  Adjunction.ofNatIsoRight
    ((constantSheafAdj (smallEtaleSiteTopology Y) Ab.{u + 1} terminalIsTerminal).comp
      (smallEtalePullbackPushforwardAdjunction f))
    (smallEtalePushforwardTerminalSectionsIso f)





/-- The native inverse-image functor carries the native constant sheaf to the native constant
sheaf.  This is the canonical uniqueness isomorphism between two left adjoints to terminal-object
sections. -/
def smallEtalePullbackConstantIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    constantSheaf (smallEtaleSiteTopology Y) Ab.{u + 1} ⋙ smallEtalePullback f ≅
      constantSheaf (smallEtaleSiteTopology X) Ab.{u + 1} :=
  (smallEtalePullbackConstantAdjunction f).leftAdjointUniq
    (constantSheafAdj (smallEtaleSiteTopology X) Ab.{u + 1} terminalIsTerminal)











end FiniteFields.Etale


