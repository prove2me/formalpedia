-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_IsTorus
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_IsTorus
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:54:32.674409+00:00
-- url     : https://prove2.me/theorems/ac331c8b-dd31-48e4-98d6-e0fab595f726
-- title:
--   Is Torus
-- statement:
--   Definitions and structural lemmas for Is Torus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/SplitTori/IsTorus.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusAff
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.Semi
noncomputable abbrev fieldBaseChange (k Ω : Type u) [Field k] [CommRing Ω] [Algebra k Ω]
    (T : Over (Spec (.of k))) : Over (Spec (.of Ω)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).obj T
structure IsTorus {k : Type u} [Field k] (T : Over (Spec (.of k))) [GrpObj T] : Prop where
  comm : IsCommMonObj T
  finiteType : LocallyOfFiniteType T.hom
  quasiCompact : QuasiCompact T.hom
  splits : ∃ (Ω : Type u) (_ : Field Ω) (_ : Algebra k Ω)
    (X : Type u) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X)
    (e : fieldBaseChange k Ω T ≅ splitTorus (Spec (.of Ω)) X), IsMonHom e.hom
end ReciprocityTheory.ChartRestriction.G.Semi


