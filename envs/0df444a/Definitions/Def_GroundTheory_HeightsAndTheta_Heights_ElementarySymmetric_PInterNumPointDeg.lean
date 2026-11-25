-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumPointDeg
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumPointDeg
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T07:15:33.404696+00:00
-- url     : https://prove2.me/theorems/569c28c9-14d2-4ab5-82a2-d2151bb901f4
-- title:
--   PInter Num Point Deg
-- statement:
--   Definitions and structural lemmas for PInter Num Point Deg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumPointDeg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumPointDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PInterNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
namespace InterNumPointDeg
variable {k : Type u} [Field k] {N : ℕ}
abbrev OneRing (k : Type u) [Field k] (N : ℕ) : Type u := NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k
abbrev coneField (P : Ideal (OneRing k N)) [P.IsPrime] : Type u := FractionRing (OneRing k N ⧸ P)
instance small_coneField [Small.{w} k] (P : Ideal (OneRing k N)) [P.IsPrime] : Small.{w} (coneField P) := by
  have : Small.{w} (OneRing k N ⧸ P) := small_of_surjective Ideal.Quotient.mk_surjective
  refine small_of_surjective (α := (OneRing k N ⧸ P) × nonZeroDivisors (OneRing k N ⧸ P))
    (f := fun z => IsLocalization.mk' (coneField P) z.1 z.2) fun z => ?_
  obtain ⟨q, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (OneRing k N ⧸ P)) z
  exact ⟨q, rfl⟩
variable [Small.{w} k] (pp : Ideal (Poly k N)) [pp.IsPrime]
def coneHom : OneRing k N →ₐ[k] Shrink.{w} (coneField (pp.comap (oneBlock (S := k) (N := N)).toRingHom)) :=
  (Shrink.algEquiv k _).symm.toAlgHom.comp
    ((IsScalarTower.toAlgHom k (OneRing k N ⧸ pp.comap (oneBlock (S := k) (N := N)).toRingHom) _).comp
      (Ideal.Quotient.mkₐ k (pp.comap (oneBlock (S := k) (N := N)).toRingHom)))
def pt : Fin (N + 1) → Shrink.{w} (coneField (pp.comap (oneBlock (S := k) (N := N)).toRingHom)) :=
  fun i => coneHom pp (X ⟨(), i⟩)
end InterNumPointDeg
end
end GroundTheory.Heights₂.Heights.Kleiman


