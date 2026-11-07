-- Prove2me | Definitions.Def_ErasureQTanner_covered
-- name    : ErasureQTanner_covered
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:39.050062+00:00
-- url     : https://prove2.me/theorems/78eead34-494c-4903-bbcb-42b3c8156ad1
-- title:
--   The covered subcode $S_C(x)$ and the failure event $\mathrm{decode}(C,x)=0$
-- statement:
--   For a linear code $C\subseteq\mathbb F^\iota$ and an erasure pattern $x$, the **subcode of $C$ covered by $x$** is
--   $$S_C(x):=\{c\in C: c_i=0\text{ for all } i\text{ with }x_i=0\}.$$
--   Decoding from $x$ succeeds when $S_C(x)=\{0\}$, and it fails, written $\mathrm{decode}(C,x)=0$, otherwise. Every erasure statement in the paper is about these two objects.
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), §6, p.13

import Mathlib

set_option autoImplicit false

namespace ErasureQTanner

/-- The subcode of `C` covered by the erasure pattern `x`: Pfister, Sprumont, Zémor, STOC 2027 submission (manuscript
sha256 bf7a84a5…), §6, p.13: "`S_C(x) := { c ∈ C : cᵢ = 0 for all i ∈ [n] where xᵢ = 0 }`".

**Formalization Note.** The field `F` and the finite coordinate type `ι` are arbitrary (the page has `F_q`, `[n]`);
`x i = true` means `xᵢ = 1`. -/
def covered {F ι : Type*} [Field F] (C : Submodule F (ι → F)) (x : ι → Bool) : Submodule F (ι → F) where
  carrier := {c | c ∈ C ∧ ∀ i, x i = false → c i = 0}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨C.add_mem ha hb, fun i hi => by simp [ha' i hi, hb' i hi]⟩
  zero_mem' := ⟨C.zero_mem, fun _ _ => rfl⟩
  smul_mem' := by
    rintro r a ⟨ha, ha'⟩
    exact ⟨C.smul_mem r ha, fun i hi => by simp [ha' i hi]⟩

/-- "`decode(C, x) = 0`" (§6, p.13: `decode(C, x) = 1` if `S_C(x) = {0}`, `0` otherwise). -/
def decodeFails {F ι : Type*} [Field F] (C : Submodule F (ι → F)) (x : ι → Bool) : Prop :=
  covered C x ≠ ⊥

end ErasureQTanner


