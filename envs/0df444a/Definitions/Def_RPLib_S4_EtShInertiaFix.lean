-- Prove2me | Definitions.Def_RPLib_S4_EtShInertiaFix
-- name    : RPLib_S4_EtShInertiaFix
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:14:38.370757+00:00
-- url     : https://prove2.me/theorems/b4bfaa5d-0635-4762-9aea-7fd497a47614
-- title:
--   An inertia element fixes a prime of $B \otimes_A R'$ over the generic point
-- statement:
--   Let $\tau : B \to B$ be an $A$-algebra automorphism with $\tau(b) - b \in Q$ for all $b \in B$ (an inertia element at the prime $Q$), and let $\mathfrak q$ be a prime of $S = B \otimes_A R'$ containing $Q \otimes 1$. Then $\tau \otimes 1$ maps $\mathfrak q$ to itself. If moreover $B$ is an integrally closed domain and $R'$ is standard etale over $A$, then a minimal prime $\mathfrak p \subseteq \mathfrak q$ of $S$ lies over $(0) \subset B$ (by flatness) and is also fixed by $\tau \otimes 1$ (by the unibranch property).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Raynaud, Anneaux locaux henseliens, Lecture Notes in Math. 169, Springer (1970), Chapters V and VIII; J. Neukirch, Algebraic Number Theory, Grundlehren 322, Springer (1999), Chapter I, Section 9

import Mathlib
import Definitions.Def_RPLib_S4_EtShUnibranch

/-!
# S4-EtSheaves, O10c part 2a: an inertia element fixes a prime of `B ⊗[A] R'` over `(0)`

Let `τ : B ≃ₐ[A] B` satisfy `τ b - b ∈ Q` for all `b` (an inertia element at `Q`), and let `𝔮` be a
prime of `S = B ⊗[A] R'` containing `Q ⊗ 1`. Then `τ ⊗ 1` maps `𝔮` to itself. If moreover `B` is an
integrally closed domain and `R'` is standard etale over `A`, a minimal prime `𝔭 ≤ 𝔮` of `S` lies
over `(0)` (flatness) and is fixed by `τ ⊗ 1` (unibranch property, part 1).
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace RamanujanPetersson.EtSheaves.InertiaFix

variable {A B R' : Type*} [CommRing A] [CommRing B] [CommRing R'] [Algebra A B] [Algebra A R']

/-- The automorphism `τ ⊗ 1` of `B ⊗[A] R'`. -/
abbrev tauT (τ : B ≃ₐ[A] B) : B ⊗[A] R' ≃ₐ[A] B ⊗[A] R' :=
  Algebra.TensorProduct.congr τ AlgEquiv.refl

theorem tauT_tmul (τ : B ≃ₐ[A] B) (b : B) (r : R') : tauT τ (b ⊗ₜ r) = τ b ⊗ₜ r := by
  simp [tauT]

theorem tauT_algebraMap (τ : B ≃ₐ[A] B) (b : B) :
    tauT (R' := R') τ (algebraMap B (B ⊗[A] R') b) = algebraMap B (B ⊗[A] R') (τ b) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply, tauT_tmul]

/-- `τ ⊗ 1` moves every element by an element of `𝔮` when `τ` is in the inertia group of `Q`. -/
theorem sub_mem (τ : B ≃ₐ[A] B) (Q : Ideal B) (hτ : ∀ b, τ b - b ∈ Q)
    (𝔮 : Ideal (B ⊗[A] R')) (h𝔮 : ∀ b ∈ Q, b ⊗ₜ[A] (1 : R') ∈ 𝔮) (s : B ⊗[A] R') :
    tauT τ s - s ∈ 𝔮 := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul b r =>
    rw [tauT_tmul, ← sub_tmul]
    have e : (τ b - b) ⊗ₜ[A] r = ((τ b - b) ⊗ₜ[A] (1 : R')) * ((1 : B) ⊗ₜ r) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e]
    exact 𝔮.mul_mem_right _ (h𝔮 _ (hτ b))
  | add x y hx hy =>
    rw [map_add, add_sub_add_comm]
    exact 𝔮.add_mem hx hy

/-- HEADLINE: an inertia element at `Q` fixes every prime of `B ⊗[A] R'` containing `Q ⊗ 1`. -/
theorem comap_tauT_eq (τ : B ≃ₐ[A] B) (Q : Ideal B) (hτ : ∀ b, τ b - b ∈ Q)
    (𝔮 : Ideal (B ⊗[A] R')) (h𝔮 : ∀ b ∈ Q, b ⊗ₜ[A] (1 : R') ∈ 𝔮) :
    𝔮.comap (tauT τ) = 𝔮 := by
  ext s
  have h := sub_mem τ Q hτ 𝔮 h𝔮 s
  rw [Ideal.mem_comap]
  constructor
  · intro hs
    simpa using 𝔮.sub_mem hs h
  · intro hs
    simpa using 𝔮.add_mem h hs

/-- Minimal primes of a flat algebra over a domain lie over `(0)`. -/
theorem comap_eq_bot_of_mem_minimalPrimes {B S : Type*} [CommRing B] [IsDomain B] [CommRing S]
    [Algebra B S] [Module.Flat B S] {𝔭 : Ideal S} (h𝔭 : 𝔭 ∈ minimalPrimes S) :
    𝔭.comap (algebraMap B S) = ⊥ := by
  rw [eq_bot_iff]
  intro b hb
  rw [Ideal.mem_comap] at hb
  rw [Ideal.mem_bot]
  by_contra hb0
  have hreg : IsSMulRegular S b :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hb0)
  have hnz : algebraMap B S b ∈ nonZeroDivisors S := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    refine hreg ?_
    show b • x = b • (0 : S)
    rw [smul_zero, Algebra.smul_def, mul_comm, hx]
  exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes h𝔭) hb hnz

/-- HEADLINE: an inertia element at `Q` fixes a prime of `B ⊗[A] R'` over `(0)` below `𝔮`. -/
theorem exists_fixed_prime [IsDomain B] [IsIntegrallyClosed B] (P0 : StandardEtalePresentation A R')
    (τ : B ≃ₐ[A] B) (Q : Ideal B) (hτ : ∀ b, τ b - b ∈ Q) (𝔮 : Ideal (B ⊗[A] R')) [𝔮.IsPrime]
    (h𝔮 : ∀ b ∈ Q, b ⊗ₜ[A] (1 : R') ∈ 𝔮) :
    ∃ 𝔭 : Ideal (B ⊗[A] R'), 𝔭.IsPrime ∧ 𝔭 ≤ 𝔮 ∧ 𝔭.comap (algebraMap B (B ⊗[A] R')) = ⊥ ∧
      𝔭.comap (tauT τ) = 𝔭 := by
  haveI : Algebra.IsStandardEtale A R' := ⟨⟨P0⟩⟩
  haveI : Module.Flat A R' := inferInstance
  obtain ⟨𝔭, h𝔭, h𝔭q⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal (B ⊗[A] R'))) (J := 𝔮)
    bot_le
  haveI : 𝔭.IsPrime := h𝔭.1.1
  have h0 : 𝔭.comap (algebraMap B (B ⊗[A] R')) = ⊥ := comap_eq_bot_of_mem_minimalPrimes h𝔭
  refine ⟨𝔭, inferInstance, h𝔭q, h0, ?_⟩
  refine Unibranch.unibranch (P0.baseChange (T := B)) (𝔮 := 𝔮) ?_ h𝔭q ?_ h0
  · calc 𝔭.comap (tauT τ) ≤ 𝔮.comap (tauT τ) := Ideal.comap_mono h𝔭q
      _ = 𝔮 := comap_tauT_eq τ Q hτ 𝔮 h𝔮
  · ext b
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    rw [tauT_algebraMap, ← Ideal.mem_comap, h0, Ideal.mem_bot, map_eq_zero_iff τ τ.injective]

end RamanujanPetersson.EtSheaves.InertiaFix


