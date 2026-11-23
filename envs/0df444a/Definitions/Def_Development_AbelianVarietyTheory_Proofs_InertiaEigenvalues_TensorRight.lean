-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRight
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:52.698865+00:00
-- url     : https://prove2.me/theorems/fc3aeadb-1ff5-46e0-b0c5-01f7cb57fdbb
-- title:
--   Tensor Right
-- statement:
--   Definitions and structural lemmas for Tensor Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TensorRight.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.Cyc.FontW
def Dv (l r : ℕ) (M : Type*) [AddCommGroup M] : AddSubgroup M :=
  (nsmulAddMonoidHom (l ^ r) : M →+ M).range
def Cpl (l : ℕ) (M : Type*) [AddCommGroup M] : Prop :=
  (∀ x : M, (∀ r, x ∈ Dv l r M) → x = 0) ∧
    ∀ f : ℕ → M, (∀ r, f (r + 1) - f r ∈ Dv l r M) → ∃ L, ∀ r, L - f r ∈ Dv l r M
section Avg
variable {G A M : Type*} [Group G] [CommRing A] [AddCommGroup M] [Module A M] (l : ℕ)
  (𝓕 : Filter G) (a : G → A → A) (ρ : G → M →+ M)
end Avg
end GlobalTheory.Cyc.FontW


