-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_MemSpanOfSmulMem
-- name    : Formalism_LocalToGlobal_IndefiniteReal_MemSpanOfSmulMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:26.175928+00:00
-- url     : https://prove2.me/theorems/f9df9c78-bcc6-4a75-a4b5-2a6000d8fc4b
-- title:
--   Mem Span Of Smul Mem
-- statement:
--   Definitions and structural lemmas for Mem Span Of Smul Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/MemSpanOfSmulMem.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
namespace Formalism.IndefR.LatticeTransfer.Lat
open Formalism.IndefR.TransferLatticeStatement Formalism.HN Formalism.IndefR.LatticeTransfer
section
variable {K : Type} [Field K] [NumberField K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end
section
variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {n : ℕ}
def Tr (p₀ p : V →ₗ[K] V) (x y : Fin n → V →ₗ[K] V) (c : Matrix (Fin n) (Fin n) K) : Prop :=
  (∀ a, p₀ (p₀ a) = p₀ a) ∧ (∀ a, p (p a) = p a) ∧
  (∀ j a, p₀ a = a → p (x j a) = x j a) ∧ (∀ i a, p a = a → p₀ (y i a) = y i a) ∧
  c.det ≠ 0 ∧ (∀ i j a, p₀ a = a → y i (x j a) = c i j • a) ∧
  (∀ a, p a = a → ∑ j, ∑ i, c⁻¹ j i • x j (y i a) = a)
variable {p₀ p : V →ₗ[K] V} {x y : Fin n → V →ₗ[K] V} {c : Matrix (Fin n) (Fin n) K}
end
section
variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {S : Type} [Fintype S] {T : S → Type} [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)]
  [∀ s, FiniteDimensional K (T s)] {τ : ∀ s, Representation K G (T s)}
end
end Formalism.IndefR.LatticeTransfer.Lat


