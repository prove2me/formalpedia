-- Prove2me | Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
-- name    : Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:10.495201+00:00
-- url     : https://prove2.me/theorems/de9f0a10-99a5-4cdd-aa66-c4940f4951f5
-- title:
--   Unimod Unram Unique
-- statement:
--   Definitions and structural lemmas for Unimod Unram Unique, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/UnimodUnramUnique.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementJac
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HermitianLatticesTheory
open Polynomial IsLocalRing Matrix
section Quad
variable {S : Type*} [CommRing S] [HenselianLocalRing S]
end Quad
section Herm
variable {R : Type} [CommRing R] [StarRing R] {R₀ : Subring R}
theorem unimodUnramUnique_fixUnit (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {x : R} (hx : star x = x)
    (hu : IsUnit x) : IsUnit (⟨x, (hR₀ x).2 hx⟩ : R₀) := by
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  have h1 : star y * x = 1 := by
    have := congrArg star hy
    rwa [star_mul, hx, star_one] at this
  have hy' : star y = y := by
    calc star y = star y * (x * y) := by rw [hy, mul_one]
      _ = (star y * x) * y := by ring
      _ = y := by rw [h1, one_mul]
  exact isUnit_iff_exists_inv.2 ⟨⟨y, (hR₀ y).2 hy'⟩, Subtype.ext hy⟩
theorem unimodUnramUnique_unitAdd [IsLocalRing R₀] (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {x y : R}
    (hx : star x = x) (hy : star y = y) (h : IsUnit (x + y)) : IsUnit x ∨ IsUnit y := by
  have hxy : star (x + y) = x + y := by rw [star_add, hx, hy]
  have := unimodUnramUnique_fixUnit hR₀ hxy h
  have e : (⟨x + y, (hR₀ _).2 hxy⟩ : R₀) = ⟨x, (hR₀ x).2 hx⟩ + ⟨y, (hR₀ y).2 hy⟩ := rfl
  rw [e] at this
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add this with h1 | h1
  · exact Or.inl (by simpa using h1.map R₀.subtype)
  · exact Or.inr (by simpa using h1.map R₀.subtype)
theorem unimodUnramUnique_trFix (x : R) : star (x + star x) = x + star x := by
  rw [star_add, star_star, add_comm]
theorem unimodUnramUnique_nontriv [IsLocalRing R₀] : Nontrivial R :=
  ⟨⟨0, 1, fun h => zero_ne_one (α := R₀) (Subtype.ext (by simpa using h))⟩⟩
def unimodUnramUnique_J [IsLocalRing R₀] (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) : Ideal R where
  carrier := {r | ∀ c : R, ¬ IsUnit (c * r + star (c * r))}
  add_mem' := by
    intro a b ha hb c h
    have e : c * (a + b) + star (c * (a + b))
        = (c * a + star (c * a)) + (c * b + star (c * b)) := by
      rw [mul_add, star_add]; ring
    rw [e] at h
    rcases unimodUnramUnique_unitAdd hR₀ (unimodUnramUnique_trFix _)
      (unimodUnramUnique_trFix _) h with h | h
    exacts [ha c h, hb c h]
  zero_mem' := fun c => by
    have := unimodUnramUnique_nontriv (R₀ := R₀)
    simp
  smul_mem' := by
    intro a r hr c
    simpa [smul_eq_mul, mul_assoc] using hr (c * a)
end Herm
end Formalism.HermitianLatticesTheory


