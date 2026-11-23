-- Prove2me | Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvKMCore
-- name    : Development_DiscreteGroups_GlobalIrreducibility_LConvKMCore
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:03.321797+00:00
-- url     : https://prove2.me/theorems/ac5eba41-af36-4c05-8861-ee4e4bd1b975
-- title:
--   LConv KMCore
-- statement:
--   Definitions and structural lemmas for LConv KMCore, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set ComplexConjugate
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace DiscreteGroups.sglob.LConvKM
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
def InvF {G : Type*} [Group G] (ρ : Representation ℂ G M) (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) : Prop :=
  (∀ x y, (starRingEnd ℂ) (B x y) = B y x) ∧ (∀ x, 0 ≤ (B x x).re) ∧ ∀ g x y, B (ρ g x) (ρ g y) = B x y
section form
variable (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
end form
def ev (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) : M → M → ℂ := fun x y => B x y
def sesqSet : Set (M → M → ℂ) :=
  {F | ∀ x y z, F (x + y) z = F x z + F y z} ∩ {F | ∀ (a : ℂ) x z, F (a • x) z = (starRingEnd ℂ) a * F x z} ∩
    {F | ∀ x y z, F x (y + z) = F x y + F x z} ∩ {F | ∀ (a : ℂ) x y, F x (a • y) = a * F x y}
def mkForm (F : M → M → ℂ) (h : F ∈ (sesqSet : Set (M → M → ℂ))) : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) F h.1.1.1 (fun a x z => h.1.1.2 a x z) h.1.2
    (fun a x y => h.2 a x y)
section cap
variable {G : Type*} [Group G] (ρ : Representation ℂ G M) (c : ℕ → ℝ) (xs : ℕ → M)
def Cap (F : M → M → ℂ) : Prop := ∀ n, ∑ i ∈ Finset.range n, c i * (F (xs i) (xs i)).re ≤ 1
def capSet : Set (M → M → ℂ) :=
  (sesqSet : Set (M → M → ℂ)) ∩ {F | ∀ x y, (starRingEnd ℂ) (F x y) = F y x} ∩ {F | ∀ x, 0 ≤ (F x x).re} ∩
    {F | ∀ g x y, F (ρ g x) (ρ g y) = F x y} ∩ {F | Cap c xs F}
end cap
end DiscreteGroups.sglob.LConvKM


