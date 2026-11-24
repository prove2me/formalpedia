-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CocycleLocalSectionsRestrictCompatibly
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_CocycleLocalSectionsRestrictCompatibly
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T16:11:17.953804+00:00
-- url     : https://prove2.me/theorems/a9fbabbf-fa75-40c4-8946-cd4c8f97b25e
-- title:
--   Cocycle Local Sections Restrict Compatibly
-- statement:
--   Definitions and structural lemmas for Cocycle Local Sections Restrict Compatibly, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CocycleLocalSectionsRestrictCompatibly.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullA
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh
  GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
namespace GlobalTheory.CechDR.AffLoc
variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}
theorem resThk_pt (T : TT s) {p q : Pair (pt T)} (hpq : p ≤ q) :
    spMap ((RingHom.id (Sec (algStr R T.obj.B) p.1.1.1)).comp
      (Sec.res (algStr R T.obj.B) (Pair.le_fst hpq) : Sec (algStr R T.obj.B) q.1.1.1 →+* Sec (algStr R T.obj.B) p.1.1.1)) ≫
      (affPt (algStr R T.obj.B) q.1.1 ≫ pt T) = affPt (algStr R T.obj.B) p.1.1 ≫ pt T := by
  rw [RingHom.id_comp, ← Category.assoc, affPt_res]
def resThk (T : TT s) {p q : Pair (pt T)} (hpq : p ≤ q) : thk T q ⟶ thk T p :=
  ⟨Thick.trivHom (T := (thk T p).obj) (Sec.res (algStr R T.obj.B) (Pair.le_fst hpq)) (resThk_pt T hpq)⟩
end GlobalTheory.CechDR.AffLoc


