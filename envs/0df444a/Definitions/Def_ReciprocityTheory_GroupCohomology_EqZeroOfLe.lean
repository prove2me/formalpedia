-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_EqZeroOfLe
-- name    : ReciprocityTheory_GroupCohomology_EqZeroOfLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:32.008722+00:00
-- url     : https://prove2.me/theorems/ceb97db4-5e90-452d-ad79-80728e59046c
-- title:
--   Eq Zero Of Le
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/EqZeroOfLe.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh.EulerCharacteristicLength
universe u
variable {R : Type u} [CommRing R]
open Function
section LES
variable {a b c : ℕ → Type u} [∀ n, AddCommGroup (a n)] [∀ n, Module R (a n)]
  [∀ n, AddCommGroup (b n)] [∀ n, Module R (b n)] [∀ n, AddCommGroup (c n)] [∀ n, Module R (c n)]
  (f : ∀ n, a n →ₗ[R] b n) (g : ∀ n, b n →ₗ[R] c n) (δ : ∀ n, c n →ₗ[R] a (n + 1))
end LES
def FL (a : ℕ → Type u) [∀ n, AddCommGroup (a n)] [∀ n, Module R (a n)] (N : ℕ) : Prop :=
  (∀ n, Module.length R (a n) ≠ ⊤) ∧ ∀ n, N < n → Module.length R (a n) = 0
noncomputable def ch (a : ℕ → Type u) [∀ n, AddCommGroup (a n)] [∀ n, Module R (a n)] (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * ((Module.length R (a n)).toNat : ℤ)
section LES2
variable {a b c : ℕ → Type u} [∀ n, AddCommGroup (a n)] [∀ n, Module R (a n)]
  [∀ n, AddCommGroup (b n)] [∀ n, Module R (b n)] [∀ n, AddCommGroup (c n)] [∀ n, Module R (c n)]
  (f : ∀ n, a n →ₗ[R] b n) (g : ∀ n, b n →ₗ[R] c n) (δ : ∀ n, c n →ₗ[R] a (n + 1))
  (h0 : Injective (f 0)) (hB : ∀ n, Exact (f n) (g n)) (hC : ∀ n, Exact (g n) (δ n))
  (hA : ∀ n, Exact (δ n) (f (n + 1)))
include h0 hB hC hA
end LES2
end ReciprocityTheory.Coh.EulerCharacteristicLength


