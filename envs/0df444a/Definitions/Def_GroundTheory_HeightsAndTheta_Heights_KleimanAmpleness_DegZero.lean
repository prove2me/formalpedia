-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DegZero
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DegZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:09.765279+00:00
-- url     : https://prove2.me/theorems/db88a97a-4f43-40b2-a0f1-7af31cb89dcd
-- title:
--   Deg Zero
-- statement:
--   Definitions and structural lemmas for Deg Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DegZero.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
noncomputable section
namespace EulerSES
variable {F : Type} [Field F] {A : ℕ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module F (A n)]
def cyc (C : ∀ n, Submodule F (A n)) (d : ∀ n, A n →ₗ[F] A (n + 1)) (n : ℕ) : Submodule F (A n) :=
  C n ⊓ LinearMap.ker (d n)
def bnd (C : ∀ n, Submodule F (A n)) (d : ∀ n, A n →ₗ[F] A (n + 1)) : (n : ℕ) → Submodule F (A n)
  | 0 => ⊥
  | n + 1 => (C n).map (d n)
abbrev coh (C : ∀ n, Submodule F (A n)) (d : ∀ n, A n →ₗ[F] A (n + 1)) (n : ℕ) : Type :=
  ↥(cyc C d n) ⧸ (bnd C d n).comap (cyc C d n).subtype
end EulerSES
open EulerSES
def EulerSES.Statement : Prop :=
  ∀ (F : Type) [Field F] (A B C : ℕ → Type) [∀ n, AddCommGroup (A n)] [∀ n, Module F (A n)]
    [∀ n, AddCommGroup (B n)] [∀ n, Module F (B n)] [∀ n, AddCommGroup (C n)] [∀ n, Module F (C n)]
    (CA : ∀ n, Submodule F (A n)) (CB : ∀ n, Submodule F (B n)) (CC : ∀ n, Submodule F (C n))
    (dA : ∀ n, A n →ₗ[F] A (n + 1)) (dB : ∀ n, B n →ₗ[F] B (n + 1)) (dC : ∀ n, C n →ₗ[F] C (n + 1))
    (f : ∀ n, A n →ₗ[F] B n) (g : ∀ n, B n →ₗ[F] C n) (N : ℕ),
    (∀ n, ∀ x ∈ CA n, dA n x ∈ CA (n + 1)) → (∀ n, ∀ x ∈ CB n, dB n x ∈ CB (n + 1)) →
    (∀ n, ∀ x ∈ CC n, dC n x ∈ CC (n + 1)) →
    (∀ n, ∀ x ∈ CA n, dA (n + 1) (dA n x) = 0) → (∀ n, ∀ x ∈ CB n, dB (n + 1) (dB n x) = 0) →
    (∀ n, ∀ x ∈ CC n, dC (n + 1) (dC n x) = 0) →
    (∀ n, ∀ x ∈ CA n, f n x ∈ CB n) → (∀ n, ∀ y ∈ CB n, g n y ∈ CC n) →
    (∀ n, ∀ x ∈ CA n, dB n (f n x) = f (n + 1) (dA n x)) →
    (∀ n, ∀ y ∈ CB n, dC n (g n y) = g (n + 1) (dB n y)) →
    (∀ n, ∀ x ∈ CA n, f n x = 0 → x = 0) →
    (∀ n, ∀ x ∈ CA n, g n (f n x) = 0) →
    (∀ n, ∀ y ∈ CB n, g n y = 0 → ∃ x ∈ CA n, f n x = y) →
    (∀ n, ∀ z ∈ CC n, ∃ y ∈ CB n, g n y = z) →
    (∀ n, FiniteDimensional F (coh CA dA n)) → (∀ n, FiniteDimensional F (coh CB dB n)) →
    (∀ n, FiniteDimensional F (coh CC dC n)) →
    Subsingleton (coh CA dA (N + 1)) →
    ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * (Module.finrank F (coh CB dB n) : ℤ) =
      ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * (Module.finrank F (coh CA dA n) : ℤ) +
        ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * (Module.finrank F (coh CC dC n) : ℤ)
def EulerSES.degZero (n : ℕ) : Submodule ℚ ℚ := if n = 0 then ⊤ else ⊥
end
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization


