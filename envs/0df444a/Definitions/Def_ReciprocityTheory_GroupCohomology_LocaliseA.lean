-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_LocaliseA
-- name    : ReciprocityTheory_GroupCohomology_LocaliseA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:08.201178+00:00
-- url     : https://prove2.me/theorems/0ab567b7-3140-41ca-9a22-e9888902c456
-- title:
--   Localise A
-- statement:
--   Definitions and structural lemmas for Localise A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/LocaliseA.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_d
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_d


set_option autoImplicit false
namespace ReciprocityTheory.Coh
open Cx Function
universe u
section Alg
variable {R : Type u} [CommRing R] {A B : Cx R}
end Alg
section Trunc
variable {R : Type u} [CommRing R] (A : Cx R) (L : Submodule R (A.H 1))
def truncW : (n : ℕ) → Submodule R (A.X n)
  | 0 => ⊤
  | 1 => (L.comap ((A.B 1).comap (A.Z 1).subtype).mkQ).map (A.Z 1).subtype
  | _ + 2 => ⊥
theorem mem_truncW_one {x : A.X 1} :
    x ∈ truncW A L 1 ↔ ∃ hx : A.d 1 x = 0, A.cls 1 x hx ∈ L := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, hz⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩
theorem truncW_d (n : ℕ) (x : A.X n) (hx : x ∈ truncW A L n) : A.d n x ∈ truncW A L (n + 1) := by
  match n, x, hx with
  | 0, x, _ =>
    rw [mem_truncW_one]
    refine ⟨A.dd 0 x, ?_⟩
    rw [cls_d]; exact L.zero_mem
  | 1, x, hx =>
    obtain ⟨hx0, _⟩ := (mem_truncW_one A L).1 hx
    show A.d 1 x ∈ (⊥ : Submodule R _)
    rw [hx0]; exact Submodule.zero_mem _
  | n + 2, x, hx =>
    have : x = 0 := (Submodule.mem_bot R).1 hx
    subst this
    rw [map_zero]; exact Submodule.zero_mem _
def truncCx : Cx R where
  X n := truncW A L n
  d n := (A.d n).restrict fun x hx => truncW_d A L n x hx
  dd n x := Subtype.ext (A.dd n x.1)
def truncHom : Hom (truncCx A L) A where
  f n := (truncW A L n).subtype
  comm _ _ := rfl
end Trunc
end ReciprocityTheory.Coh


