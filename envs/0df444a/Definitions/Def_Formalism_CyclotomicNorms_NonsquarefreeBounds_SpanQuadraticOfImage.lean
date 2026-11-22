-- Prove2me | Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SpanQuadraticOfImage
-- name    : Formalism_CyclotomicNorms_NonsquarefreeBounds_SpanQuadraticOfImage
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:15:58.190388+00:00
-- url     : https://prove2.me/theorems/fadadd58-9153-47d1-9e29-a328e111d685
-- title:
--   Span Quadratic Of Image
-- statement:
--   Definitions and structural lemmas for Span Quadratic Of Image, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SpanQuadraticOfImage.lean

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
namespace Formalism.CyclotomicNorms
namespace PrismSpan
variable {k G : Type} [Field k] [Group G] {a : ℕ} {W : Fin a → Type}
  [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]
def diag (ρ : ∀ i, Representation k G (W i)) : G →* (∀ i, Module.End k (W i)) where
  toFun g i := ρ i g
  map_one' := by funext i; exact map_one (ρ i)
  map_mul' g h := by funext i; exact map_mul (ρ i) g h
abbrev alg (ρ : ∀ i, Representation k G (W i)) : Subalgebra k (∀ i, Module.End k (W i)) :=
  (MonoidAlgebra.lift k (∀ i, Module.End k (W i)) G (diag ρ)).range
variable (ρ : ∀ i, Representation k G (W i))
variable {ρ}
variable (ρ) in

def coordSub (i : Fin a) : Submodule (alg ρ) (∀ j, W j) where
  carrier := {v | ∀ j, j ≠ i → v j = 0}
  add_mem' {u v} hu hv j hj := by
    show u j + v j = 0
    rw [hu j hj, hv j hj, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' r v hv j hj := by
    show (r : ∀ i, Module.End k (W i)) j (v j) = 0
    rw [hv j hj, map_zero]
end PrismSpan
namespace PrismSpan
variable {k G : Type} [Field k] [Group G] {a : ℕ} {W : Fin a → Type}
  [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]
  {La : Fin a → Type} [∀ i, AddCommGroup (La i)] [∀ i, Module k (La i)]
def post (x : ∀ i, La i →ₗ[k] W i) :
    (∀ i, Module.End k (W i)) →ₗ[k] (∀ i, La i →ₗ[k] W i) where
  toFun E i := E i ∘ₗ x i
  map_add' E F := by funext i; exact LinearMap.add_comp _ _ _
  map_smul' c E := by funext i; exact LinearMap.smul_comp _ _ _
def sr (i : Fin a) (w : W i) : Module.Dual k (La i) →ₗ[k] (∀ j, La j →ₗ[k] W j) where
  toFun ψ := Pi.single i (ψ.smulRight w)
  map_add' ψ ψ' := by
    rw [← Pi.single_add]; congr 1; ext; simp [add_smul]
  map_smul' c ψ := by
    rw [RingHom.id_apply, ← Pi.single_smul]; congr 1; ext; simp [smul_smul]
end PrismSpan
end Formalism.CyclotomicNorms


