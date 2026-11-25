-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
-- name    : GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T23:59:58.474337+00:00
-- url     : https://prove2.me/theorems/d58820e1-17e0-4528-a89f-17c8cc0fd55e
-- title:
--   Qcoh Zariski
-- statement:
--   Definitions and structural lemmas for Qcoh Zariski, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/QcohZariski.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohPresheaf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.Etale
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u
section Unit
variable {V T U : Scheme.{u}}
noncomputable def pullbackUnitApp (g : T ⟶ U) (N : U.Modules) (O : U.Opens) :
    Γ(N, O) →+ Γ((Scheme.Modules.pullback g).obj N, g ⁻¹ᵁ O) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).app O).hom
end Unit
section Opens
variable {X : Scheme.{u}} (F : X.Modules) (U : X.Etale)
noncomputable abbrev openObj (O : U.left.Opens) : X.Etale := Scheme.Etale.mk (O.ι ≫ U.hom)
noncomputable def openIncl (O : U.left.Opens) : openObj U O ⟶ U :=
  MorphismProperty.Over.homMk O.ι rfl trivial
noncomputable def openInclLE {O' O : U.left.Opens} (h : O' ≤ O) : openObj U O' ⟶ openObj U O :=
  MorphismProperty.Over.homMk (U.left.homOfLE h)
    (by
      change U.left.homOfLE h ≫ (O.ι ≫ U.hom) = O'.ι ≫ U.hom
      rw [← Category.assoc, Scheme.homOfLE_ι]) trivial
instance {Y Z : Scheme.{u}} (a : Y ⟶ Z) (b : Z ⟶ X) (c : Y ⟶ X) (h : a ≫ b = c) :
    IsIso (compHom F a b c h) := by
  unfold compHom
  infer_instance
noncomputable def openSection (O : U.left.Opens) :
    Γ((Scheme.Modules.pullback U.hom).obj F, O) →+
      Γ((Scheme.Modules.pullback (O.ι ≫ U.hom)).obj F, ⊤) :=
  ((compHom F O.ι U.hom _ rfl).app ⊤).hom.comp
    ((((Scheme.Modules.pullback O.ι).obj ((Scheme.Modules.pullback U.hom).obj F)).presheaf.map
      (homOfLE (by rw [Scheme.Opens.ι_preimage_self]) : (⊤ : O.toScheme.Opens) ⟶ O.ι ⁻¹ᵁ O).op).hom.comp
      (pullbackUnitApp O.ι _ O))
end Opens
end GroundTheory.Arith.Etale


