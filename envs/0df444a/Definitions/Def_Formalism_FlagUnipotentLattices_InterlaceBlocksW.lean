-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_InterlaceBlocksW
-- name    : Formalism_FlagUnipotentLattices_InterlaceBlocksW
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:31:51.923193+00:00
-- url     : https://prove2.me/theorems/061acc81-b318-4d04-a4d3-f3458b30cd7e
-- title:
--   Interlace Blocks W
-- statement:
--   Definitions and structural lemmas for Interlace Blocks W, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/InterlaceBlocksW.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_MemLpTwoOfOneTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset TensorProduct
noncomputable section
namespace Formalism.HermitianLatticeCounting.S8
def InterlaceBlocksW : Prop :=
  ∀ (m : ℕ) (t : ℕ → ℕ) (u v : List ℝ) (b e : ℕ → ℝ),
    Interlaces u v → (∀ x ∈ u, -b 0 < x) →
    (∀ j < m, b j < e j) → (∀ j, j + 1 < m → e j < b (j + 1)) →
    (∀ i < m, ∀ j < m, ((t j : ℝ) + 1) / 2 ≤ |b i - e j|) →
    Interlaces (u ++ (List.range m).flatMap (fun j => blockP (-e j) (t j + 1)))
      (v ++ (List.range m).flatMap (fun j => -b j :: blockP (-e j) (t j)))
def LLmap {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] {n : ℕ}
    (ℓ : V →ₗ[ℂ] U) (a : Fin n) : V ⊗[ℂ] (Fin n → ℂ) →ₗ[ℂ] U :=
  (TensorProduct.rid ℂ U).toLinearMap ∘ₗ TensorProduct.map ℓ (LinearMap.proj a)
def LLEquivariant : Prop :=
  ∀ (V U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (n r k : ℕ) (c w : ℕ → Fin n)
    (E : Fin n → Fin n → Module.End ℂ V) (π : Fin k → Fin k → Module.End ℂ U) (d : ℕ → ℂ) (ℓ : V →ₗ[ℂ] U),
    ChainLabel r k c w → ChainEquivariant r k c w E π d ℓ →
    ChainEquivariant r k c w (Formalism.REAL.tens E (stdRep n)) π d (LLmap ℓ (c 0)) ∧
    ChainEquivariant r k c w (Formalism.REAL.tens E (fun a b => -stdRep n b a)) π d (LLmap ℓ (c (2 * r)))
def ChainReverse : Prop :=
  ∀ (V U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (n r k : ℕ) (c w : ℕ → Fin n)
    (E : Fin n → Fin n → Module.End ℂ V) (π : Fin k → Fin k → Module.End ℂ U) (d : ℕ → ℂ) (ℓ : V →ₗ[ℂ] U),
    ChainLabel r k c w → ChainEquivariant r k c w E π d ℓ →
    ChainLabel r k (fun i => c (2 * r - i)) w ∧
      ChainEquivariant r k (fun i => c (2 * r - i)) w (fun a b => -E b a) (fun a b => -π b a)
        (fun j => -d (2 * r - 1 - j)) ℓ ∧
      ∏ j ∈ Finset.range (2 * r), (-d (2 * r - 1 - j)) = ∏ j ∈ Finset.range (2 * r), d j
def ResidueOpDual : Prop :=
  ∀ (V U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (r k : ℕ)
    (c w : ℕ → Fin (2 * r + k + 1)) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ V)
    (π : Fin k → Fin k → Module.End ℂ U) (d : ℕ → ℂ) (ℓ : V →ₗ[ℂ] U)
    (lam : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℂ)
    (p : Fin (2 * r + k + 1) → Module.End ℂ (V ⊗[ℂ] (Fin (2 * r + k + 1) → ℂ))) (v : V),
    Formalism.REAL.GlRel E → ChainLabel r k c w → ChainEquivariant r k c w E π d ℓ →
    (∀ (x : ℂ) (v : V), Formalism.REAL.qdet E x v = (∏ s, (x - ((2 * r + k : ℕ) : ℂ) / 2 + lam s)) • v) →
    (∀ (x : ℂ) (a : U), Formalism.REAL.qdet π x a = (∏ j, (x - ((k : ℂ) - 1) / 2 + u j)) • a) →
    ∑ i, p i = 1 → (∀ i j, p i * p j = if i = j then p i else 0) →
    Formalism.REAL.Om (fun _ => true) E (fun a b => -stdRep (2 * r + k + 1) b a) =
      ∑ i, (-lam i + (1 - ((2 * r + k + 1 : ℕ) : ℂ)) / 2) • p i →
    Function.Injective lam → (∀ j < 2 * r, d j ≠ 0) → ℓ v ≠ 0 →
    ∀ i, (LLmap ℓ (c (2 * r)) (p i (v ⊗ₜ[ℂ] (Pi.single (c 0) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ))) = 0 ↔
      ∃ j, u j = lam i - 1 / 2)
def ResidueOp : Prop :=
  ∀ (V U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (r k : ℕ)
    (c w : ℕ → Fin (2 * r + k + 1)) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ V)
    (π : Fin k → Fin k → Module.End ℂ U) (d : ℕ → ℂ) (ℓ : V →ₗ[ℂ] U)
    (lam : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℂ)
    (p : Fin (2 * r + k + 1) → Module.End ℂ (V ⊗[ℂ] (Fin (2 * r + k + 1) → ℂ))) (v : V),
    Formalism.REAL.GlRel E → ChainLabel r k c w → ChainEquivariant r k c w E π d ℓ →
    (∀ (x : ℂ) (v : V),
      Formalism.REAL.qdet (fun a b => -E b a) x v = (∏ s, (x - ((2 * r + k : ℕ) : ℂ) / 2 - lam s)) • v) →
    (∀ (x : ℂ) (a : U), Formalism.REAL.qdet (fun a b => -π b a) x a = (∏ j, (x - ((k : ℂ) - 1) / 2 - u j)) • a) →
    ∑ i, p i = 1 → (∀ i j, p i * p j = if i = j then p i else 0) →
    Formalism.REAL.Om (fun _ => true) E (stdRep (2 * r + k + 1)) =
      ∑ i, (lam i + (1 - ((2 * r + k + 1 : ℕ) : ℂ)) / 2) • p i →
    Function.Injective lam → (∀ j < 2 * r, d j ≠ 0) → ℓ v ≠ 0 →
    ∀ i, (LLmap ℓ (c 0) (p i (v ⊗ₜ[ℂ] (Pi.single (c (2 * r)) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ))) = 0 ↔
      ∃ j, u j = lam i + 1 / 2)
end Formalism.HermitianLatticeCounting.S8


