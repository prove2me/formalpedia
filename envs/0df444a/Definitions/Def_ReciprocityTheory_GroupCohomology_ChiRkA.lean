-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_ChiRkA
-- name    : ReciprocityTheory_GroupCohomology_ChiRkA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:31.361152+00:00
-- url     : https://prove2.me/theorems/4d401e76-9664-4787-9c66-728811e56192
-- title:
--   Chi Rk A
-- statement:
--   Definitions and structural lemmas for Chi Rk A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ChiRkA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh.EulerCharacteristicRank
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
open Function Module
def FG (a : ℕ → Type u) [∀ n, AddCommGroup (a n)] [∀ n, Module R (a n)] (N : ℕ) : Prop :=
  (∀ n, Module.Finite R (a n)) ∧ ∀ n, N < n → Subsingleton (a n)
noncomputable def cr (a : ℕ → Type u) [∀ n, AddCommGroup (a n)] [∀ n, Module R (a n)] (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * (finrank R (a n) : ℤ)
section LES
variable {a b c : ℕ → Type u} [∀ n, AddCommGroup (a n)] [∀ n, Module R (a n)]
  [∀ n, AddCommGroup (b n)] [∀ n, Module R (b n)] [∀ n, AddCommGroup (c n)] [∀ n, Module R (c n)]
  (f : ∀ n, a n →ₗ[R] b n) (g : ∀ n, b n →ₗ[R] c n) (δ : ∀ n, c n →ₗ[R] a (n + 1))
end LES
def piOpt {α : Type u} (M : Option α → Type u) [∀ v, AddCommGroup (M v)] [∀ v, Module R (M v)] :
    (∀ v, M v) ≃ₗ[R] M none × ∀ a, M (some a) :=
  { Equiv.piOptionEquivProd with map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
end ReciprocityTheory.Coh.EulerCharacteristicRank


