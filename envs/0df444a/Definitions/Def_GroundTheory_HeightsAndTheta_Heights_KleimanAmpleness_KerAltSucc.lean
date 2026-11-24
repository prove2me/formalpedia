-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KerAltSucc
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KerAltSucc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:55.900619+00:00
-- url     : https://prove2.me/theorems/fde66bcd-3e72-42d5-83b9-8955be5e493c
-- title:
--   Ker Alt Succ
-- statement:
--   Definitions and structural lemmas for Ker Alt Succ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/KerAltSucc.lean

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
def Staircase.bdry {R : Type} [CommRing R] {A : ℕ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    (d : ∀ n, A n →ₗ[R] A (n + 1)) : ∀ n, Submodule R (A n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (d n)
abbrev Staircase.H {R : Type} [CommRing R] {A : ℕ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    (d : ∀ n, A n →ₗ[R] A (n + 1)) (n : ℕ) : Type :=
  LinearMap.ker (d n) ⧸ (Staircase.bdry d n).comap (LinearMap.ker (d n)).subtype
def Staircase.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (D : ℕ → ℕ → Type) [∀ p q, AddCommGroup (D p q)] [∀ p q, Module R (D p q)]
    (v : ∀ p q, D p q →ₗ[R] D (p + 1) q) (h : ∀ p q, D p q →ₗ[R] D p (q + 1))
    (A : ℕ → Type) [∀ p, AddCommGroup (A p)] [∀ p, Module R (A p)] (dA : ∀ p, A p →ₗ[R] A (p + 1))
    (a : ∀ p, A p →ₗ[R] D p 0)
    (C : ℕ → Type) [∀ q, AddCommGroup (C q)] [∀ q, Module R (C q)] (dC : ∀ q, C q →ₗ[R] C (q + 1))
    (c : ∀ q, C q →ₗ[R] D 0 q),
    (∀ p q, (v p (q + 1)).comp (h p q) = (h (p + 1) q).comp (v p q)) →
    (∀ p, (a (p + 1)).comp (dA p) = (v p 0).comp (a p)) →
    (∀ q, (c (q + 1)).comp (dC q) = (h 0 q).comp (c q)) →
    (∀ p, LinearMap.ker (a p) = ⊥) →
    (∀ p, LinearMap.ker (h p 0) = LinearMap.range (a p)) →
    (∀ p q, LinearMap.ker (h p (q + 1)) = LinearMap.range (h p q)) →
    (∀ q, LinearMap.ker (c q) = ⊥) →
    (∀ q, LinearMap.ker (v 0 q) = LinearMap.range (c q)) →
    (∀ p q, LinearMap.ker (v (p + 1) q) = LinearMap.range (v p q)) →
    ∀ n, Nonempty (Staircase.H dA n ≃ₗ[R] Staircase.H dC n)
def Staircase.alt (R : Type) [CommRing R] (m : ℕ) : R →ₗ[R] R :=
  if m % 2 = 1 then LinearMap.id else 0
theorem Staircase.alt_comm (R : Type) [CommRing R] (p q : ℕ) :
    (Staircase.alt R p).comp (Staircase.alt R q) = (Staircase.alt R q).comp (Staircase.alt R p) := by
  unfold Staircase.alt
  split_ifs <;> simp
theorem Staircase.ker_alt_zero (R : Type) [CommRing R] :
    LinearMap.ker (Staircase.alt R 0) = LinearMap.range (LinearMap.id : R →ₗ[R] R) := by
  simp [Staircase.alt]
theorem Staircase.ker_alt_succ (R : Type) [CommRing R] (q : ℕ) :
    LinearMap.ker (Staircase.alt R (q + 1)) = LinearMap.range (Staircase.alt R q) := by
  unfold Staircase.alt
  rcases Nat.mod_two_eq_zero_or_one q with hq | hq
  · rw [if_pos (by omega), if_neg (by omega)]
    simp
  · rw [if_neg (by omega), if_pos (by omega)]
    simp
theorem Staircase.hyps :
    (∀ p q : ℕ, (Staircase.alt ℤ p).comp (Staircase.alt ℤ q) = (Staircase.alt ℤ q).comp (Staircase.alt ℤ p)) ∧
    (∀ p : ℕ, (LinearMap.id : ℤ →ₗ[ℤ] ℤ).comp (Staircase.alt ℤ p) = (Staircase.alt ℤ p).comp LinearMap.id) ∧
    LinearMap.ker (LinearMap.id : ℤ →ₗ[ℤ] ℤ) = ⊥ ∧
    LinearMap.ker (Staircase.alt ℤ 0) = LinearMap.range (LinearMap.id : ℤ →ₗ[ℤ] ℤ) ∧
    (∀ q : ℕ, LinearMap.ker (Staircase.alt ℤ (q + 1)) = LinearMap.range (Staircase.alt ℤ q)) :=
  ⟨Staircase.alt_comm ℤ, fun p => by simp, LinearMap.ker_id, Staircase.ker_alt_zero ℤ, Staircase.ker_alt_succ ℤ⟩
example (hS : Staircase.Statement) (n : ℕ) :
    Nonempty (Staircase.H (fun p => Staircase.alt ℤ p) n ≃ₗ[ℤ] Staircase.H (fun q => Staircase.alt ℤ q) n) :=
  hS ℤ (fun _ _ => ℤ) (fun p _ => Staircase.alt ℤ p) (fun _ q => Staircase.alt ℤ q) (fun _ => ℤ)
    (fun p => Staircase.alt ℤ p) (fun _ => LinearMap.id) (fun _ => ℤ) (fun q => Staircase.alt ℤ q) (fun _ => LinearMap.id)
    (fun p q => Staircase.hyps.1 p q) Staircase.hyps.2.1 Staircase.hyps.2.1 (fun _ => Staircase.hyps.2.2.1)
    (fun _ => Staircase.hyps.2.2.2.1) (fun _ => Staircase.hyps.2.2.2.2) (fun _ => Staircase.hyps.2.2.1)
    (fun _ => Staircase.hyps.2.2.2.1) (fun p _ => Staircase.hyps.2.2.2.2 p) n
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization


