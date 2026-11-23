-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:05.108463+00:00
-- url     : https://prove2.me/theorems/7c5b4101-2da4-4b88-b668-d41053c1b37f
-- title:
--   Dvd Mul Of Idem
-- statement:
--   Definitions and structural lemmas for Dvd Mul Of Idem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.HeckeTate
section Ring
variable {R : Type} [CommRing R]
def IsPart (P : Ideal R) (N e : R) : Prop :=
  N ∣ e * (1 - e) ∧ 1 - e ∈ P ∧ ∀ q : Ideal R, q.IsMaximal → N ∈ q → q ≠ P → e ∈ q
end Ring
section Module
variable {R : Type} [CommRing R] {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
def mults (M : Type) [AddCommGroup M] [Module R M] (N : R) : Submodule R M :=
  LinearMap.range (N • (LinearMap.id : M →ₗ[R] M))
def IsUnimod (σ : R ≃+* R) (B : M →+ M →+ ℤ) : Prop :=
  (∀ x y, B x y = -B y x) ∧ (∀ (a : R) x y, B (a • x) y = B x (σ a • y)) ∧ Function.Bijective B
variable {σ : R ≃+* R} {B : M →+ M →+ ℤ} {B' : M' →+ M' →+ ℤ}
end Module
end GlobalTheory.HeckeTate


