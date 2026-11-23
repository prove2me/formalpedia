-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLPb
-- name    : Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLPb
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:48:32.468671+00:00
-- url     : https://prove2.me/theorems/6488b626-b1eb-48b2-8094-c13589b361ce
-- title:
--   Data LPb
-- statement:
--   Definitions and structural lemmas for Data LPb, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataLPb.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}
def gen (Qq : Type) [Field Qq] (p : ℕ) (a : ℤ) : Fin 1 → Qq := fun _ => (p : Qq) ^ a
def toQuot (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] (p : ℕ) (a : ℤ) :
    W →ₗ[W] (↥(line W (Qq := Qq) p a) ⧸ Submodule.comap (line W (Qq := Qq) p a).subtype (line W p (a + 1))) :=
  (Submodule.mkQ _).comp (LinearMap.toSpanSingleton W _ ⟨gen Qq p a, Submodule.mem_span_singleton_self _⟩)
def edge1 (W : Type) (Qq : Type) [CommRing W] [Field Qq] [Algebra W Qq] (p : ℕ) (a : ℤ) : Edge W Qq 1 :=
  ⟨line W p (a + 1), line W p a⟩
end Formalism.MainNotions.G.Inhab
end


