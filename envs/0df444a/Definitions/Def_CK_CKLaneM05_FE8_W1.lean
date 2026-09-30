-- Prove2me | Definitions.Def_CK_CKLaneM05_FE8_W1
-- name    : CK_CKLaneM05_FE8_W1
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:04:39.480791+00:00
-- url     : https://prove2.me/theorems/3648bafb-e87e-475b-8efa-14244dd17b07
-- title:
--   Courtade–Kumar proof module `CKLaneM05.FE8.W1` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM05.FE8.W1` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM05.FE8.W1` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM05.FE8.W1 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM05/FE8/W1.lean)

import Definitions.Def_CK_CKLaneM05_FE8_Parent

-- ===== source module CKLaneM05.FE8.W1 =====
section

/-!
# Lane M05 / FE8: certificate type v1 (outside, cap, parent) and shard-entry soundness

`W1.check_sound : W1.check B w = true → LeafOK B`. A shard is a list of archived paths with
certificate trees below their boxes (`CT W1`, refinement inside a leaf allowed); `entries_sound`
turns one kernel-evaluated `List.all` into `∀ q ∈ paths, LeafOK (feBox q)`. The facts produced are
independent of the certificate type, so later kernels (new certificate types) add facts without
invalidating earlier shards.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM05.FE8

/-- FE8 certificate, version 1. -/
inductive W1 where
  | outside
  | cap
  | parent (w : PW)
  deriving Repr

def W1.check (B : CKLaneD.Box) : W1 → Bool
  | .outside => decide (B.bhi - B.alo < 1 / 20)
  | .cap => capCheck B
  | .parent w => parentCheck B w

theorem W1.check_sound : ∀ (B : CKLaneD.Box) (w : W1), W1.check B w = true → LeafOK B
  | _, .outside, h => leafOK_of_outside (by simpa [W1.check] using h)
  | _, .cap, h => leafOK_of_cap h
  | _, .parent _, h => leafOK_of_parentCheck h

/-- A shard: archived paths with certificate trees; one Boolean check for all of them. -/
theorem entries_sound {α : Type} (chk : CKLaneD.Box → α → Bool)
    (hchk : ∀ B w, chk B w = true → LeafOK B) (L : List (List ℕ × CT α))
    (h : L.all (fun x => x.2.check chk (feBox x.1)) = true) :
    ∀ q ∈ L.map Prod.fst, LeafOK (feBox q) := by
  intro q hq
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
  rw [List.all_eq_true] at h
  exact CT.sound chk hchk x.2 _ (h x hx)

end CKLaneM05.FE8

#check @CKLaneM05.FE8.W1.check_sound
#check @CKLaneM05.FE8.entries_sound
#print axioms CKLaneM05.FE8.W1.check_sound
#print axioms CKLaneM05.FE8.entries_sound

end


