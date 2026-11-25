-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_TwistingSheaf
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_TwistingSheaf
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T03:11:54.418513+00:00
-- url     : https://prove2.me/theorems/cf387e41-dca1-4771-b4f9-d7bcd2a4520e
-- title:
--   Twisting Sheaf
-- statement:
--   Definitions and structural lemmas for Twisting Sheaf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/TwistingSheaf.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwist
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Linear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory TopologicalSpace MvPolynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
def IsCoherent {X : Scheme.{u}} (F : X.Modules) : Prop :=
  F.IsQuasicoherent ∧ ∀ U : X.Opens, IsAffineOpen U → Module.Finite Γ(X, U) Γ(F, U)
abbrev algebraOfOver (X : Scheme.{u}) (A : Type u) [CommRing A] [X.Over (Spec (.of A))] :
    Algebra A Γ(X, ⊤) :=
  overAlgebra (CommRingCat.of A)
namespace ProjSpace
variable (A : Type u) [CommRing A] (n : ℕ)
def toSpecBase : projectiveSpace A n ⟶ Spec (.of A) :=
  Proj.toSpecZero (grading A n) ≫
    Spec.map (CommRingCat.ofHom (algebraMap A (grading A n 0)))
instance overSpec : (projectiveSpace A n).Over (Spec (.of A)) := ⟨toSpecBase A n⟩
variable {A n}
def twist (G : (projectiveSpace A n).Modules) (k : ℤ) : (projectiveSpace A n).Modules :=
  G ⊗ twistingSheaf (grading A n) k
end ProjSpace
namespace ProjScheme
variable {A : Type u} [CommRing A] {n : ℕ} {X : Scheme.{u}} (i : X ⟶ projectiveSpace A n)
def twistingSheaf (k : ℤ) : X.Modules :=
  (Scheme.Modules.pullback i).obj (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k)
def twist (F : X.Modules) (k : ℤ) : X.Modules :=
  F ⊗ twistingSheaf i k
end ProjScheme
end
end GroundTheory.Arith.SchemeCoh


