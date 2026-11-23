-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_NsetExpInjectiveSurjective
-- name    : ReciprocityTheory_DualLattices_NsetExpInjectiveSurjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:25.674318+00:00
-- url     : https://prove2.me/theorems/319bc45c-c847-4bf2-95df-36b7144ae49d
-- title:
--   Nset Exp Injective Surjective
-- statement:
--   Definitions and structural lemmas for Nset Exp Injective Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NsetExpInjectiveSurjective.lean

import Definitions.Def_ReciprocityTheory_DualLattices_StThmA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
namespace ReciprocityTheory.PGsh
universe u
structure ATower (R₀ : Type u) [CommRing R₀] (p : ℕ) where
  O : LAlg R₀
  R' : ℕ → LAlg R₀
  R : ℕ → LAlg R₀
  π : ∀ n, LHom (R' n) (R n)
  q : ∀ n, LHom O (R n)
  ξ : ∀ n, (R' n : Type u)
  surj : ∀ n, Function.Surjective (π n).1
  ker_eq : ∀ n, RingHom.ker (π n).1 = Ideal.span {ξ n}
  ξ_sq : ∀ n, ξ n * ξ n = 0
  ann : ∀ n (a : (R' n : Type u)), a * ξ n = 0 → a ∈ Ideal.span {ξ n}
  char : ∀ n, ((p ^ (n + 1) : ℕ) : (R' n : Type u)) = 0
  sep : ∀ a : (O : Type u), (∀ n, (q n).1 a = 0) → a = 0
  c : (O : Type u)
  cp : ∀ n, (R' n : Type u)
  cp_spec : ∀ n, (π n).1 (cp n) = (q n).1 c
  zh : ∀ n, (R' n : Type u)ˣ
  zh_pow : ∀ n, (zh n : (R' n : Type u)) ^ (p ^ (n + 1)) = 1 + cp n * ξ n
  ζ : ∀ n, (O : Type u)ˣ
  ζ_spec : ∀ n, (q n).1 (ζ n : (O : Type u)) = (π n).1 (zh n : (R' n : Type u))
variable {R₀ : Type u} [CommRing R₀]
lemma ATower.ξ_mem {p : ℕ} (Tw : ATower R₀ p) (n : ℕ) : Tw.ξ n ∈ (Tw.π n).ker := by
  rw [LHom.ker, Submodule.restrictScalars_mem, Tw.ker_eq]
  exact Ideal.subset_span (Set.mem_singleton _)
lemma ATower.sqZero {p : ℕ} (Tw : ATower R₀ p) (n : ℕ) : (Tw.π n).SqZero := ⟨Tw.surj n, by
    rw [Tw.ker_eq, sq, Ideal.span_singleton_mul_span_singleton, Tw.ξ_sq, Ideal.span_singleton_eq_bot]⟩
def NsetExpInjectiveSurjective (B : BX R₀) {p : ℕ} (Tw : ATower R₀ p) : Prop :=
  ∀ (Dp : ∀ n, DualPair (Tw.R n)) (ι : Type) (τ : ι → ℕ → B.G Tw.O)
    (E : ι → ι → (Tw.O : Type u)) (ht : ι → B.gg →ₗ[R₀] (Tw.O : Type u))
    (bt : ι → B.gg ⊗[R₀] (Tw.O : Type u)),
    (∀ i j n, ∃ k : ℕ, (Tw.q n).1 (E i j) = k ∧
      B.IsPairing (p ^ (n + 1)) (τ i n) (τ j n) (Tw.ζ n ^ k)) →
    (∀ i n, B.IsHeight (Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ i n))
      ((Tw.q n).1.toLinearMap ∘ₗ ht i)) →
    (∀ i n, ∃ (th : B.G (Tw.R' n)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)),
      B.map (Tw.π n) th = B.map (Tw.q n) (τ i n) ∧
      (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
        (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) ∧
      LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w =
        LinearMap.lTensor B.gg (Tw.q n).1.toLinearMap (bt i)) →
    ∀ i j, Tw.c * E i j = B.ev (ht j) (bt i) - B.ev (ht i) (bt j)
end ReciprocityTheory.PGsh


