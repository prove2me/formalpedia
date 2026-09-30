-- Prove2me | Definitions.Def_TauCeti_RingTheory_RootsOfUnity_PrimitiveRoots
-- name    : TauCeti_RingTheory_RootsOfUnity_PrimitiveRoots
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:49:36.197368+00:00
-- url     : https://prove2.me/theorems/f5a390b2-c2e7-4a2f-84d3-31e392bca39c
-- title:
--   Maps determined by their value on a primitive root
-- statement:
--   For a primitive $m$-th root of unity $\zeta$, the cyclotomic character records the exponent by which an automorphism acts. Its value is one exactly when the automorphism fixes $\zeta$. This identifies the kernel of the cyclotomic action.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/RingTheory/RootsOfUnity/PrimitiveRoots.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/RingTheory/RootsOfUnity/PrimitiveRoots.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.Algebra.Rat
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Maps determined by their value on a primitive root

In a domain the `n`-th roots of unity are exactly the powers of a primitive one, so a ring
endomorphism is pinned down on all of them by its value on a single primitive `n`-th root: if it
raises that root to the `j`-th power, it raises every `n`-th root of unity to the `j`-th power.

The same principle characterises when the cyclotomic character `IsPrimitiveRoot.autToPow` is
trivial: it kills an automorphism exactly when that automorphism fixes the chosen primitive root,
because the character records nothing but the power the root is sent to.

Over a normal extension of `ℚ`, every coprime power of a primitive root is attained by an
automorphism. Indeed the two primitive roots have the same cyclotomic minimal polynomial, and
normality extends that conjugacy to the ambient field.

## Main results

* `IsPrimitiveRoot.map_eq_pow`: a ring endomorphism sending a primitive `n`-th root of
  unity `ζ` to `ζ ^ j` sends every `n`-th root of unity `μ` to `μ ^ j`.
* `IsPrimitiveRoot.autToPow_eq_one_iff`: the cyclotomic character kills an automorphism exactly
  when it fixes the chosen primitive root.
* `IsPrimitiveRoot.exists_algEquiv_apply_eq_pow_of_coprime`: every coprime power of a primitive
  root in a normal extension of `ℚ` is realized by an automorphism.

## References

The characterisation of the cyclotomic character's kernel by its value on a chosen primitive root
is due to the Birkbeck--Brasca Chebotarev density project,
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0).
-/

 section

namespace TauCeti

universe u

variable {R : Type u} [CommRing R] [IsDomain R]





end TauCeti

/-- **The cyclotomic character detects fixing `ζ`.** `autToPow` sends `x` to `1` exactly when `x`
fixes the chosen primitive root, since `autToPow` is defined by the power `x` sends it to. -/
@[simp]
theorem _root_.IsPrimitiveRoot.autToPow_eq_one_iff {K M : Type*} [CommRing K] [CommRing M]
    [IsDomain M] [Algebra K M] {m : ℕ} [NeZero m] {ζ : M} (hζ : IsPrimitiveRoot ζ m)
    (x : M ≃ₐ[K] M) : hζ.autToPow K x = 1 ↔ x ζ = ζ := by
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)) with hm | hm
  · -- `m = 1` forces `ζ = 1`, and `(ZMod 1)ˣ` is trivial, so both sides always hold
    have hζ1 : ζ = 1 := by simpa [← hm] using hζ.pow_eq_one
    have : Subsingleton (ZMod m)ˣ := by rw [← hm]; infer_instance
    exact ⟨fun _ ↦ by simp [hζ1], fun _ ↦ Subsingleton.elim _ _⟩
  · have : Fact (1 < m) := ⟨hm⟩
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have hspec := hζ.autToPow_spec (R := K) x
      rw [h, Units.val_one, ZMod.val_one, pow_one] at hspec
      exact hspec.symm
    · have hspec := hζ.autToPow_spec (R := K) x
      rw [h] at hspec
      have hval : (hζ.autToPow K x : ZMod m).val = 1 :=
        hζ.pow_inj (ZMod.val_lt _) hm (by rw [hspec, pow_one])
      exact Units.ext (ZMod.val_injective m (by rw [hval, Units.val_one, ZMod.val_one]))

end
end


