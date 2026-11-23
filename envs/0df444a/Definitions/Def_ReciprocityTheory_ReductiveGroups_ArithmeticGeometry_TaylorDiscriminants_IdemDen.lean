-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_IdemDen
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_IdemDen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:05.106494+00:00
-- url     : https://prove2.me/theorems/617b73e8-aacd-4670-b1a5-6b36f4ad1d54
-- title:
--   Idem Den
-- statement:
--   Definitions and structural lemmas for Idem Den, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/IdemDen.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField TensorProduct
namespace ReciprocityTheory.ChartRestriction.G.TB
def trDual {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) :
    Module.Basis ι ℚ E :=
  (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) b
def idemOf {E : Type} [Field E] [NumberField E] {C : Type} [Field C] [Algebra ℚ C] {ι : Type} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℚ E) (τ : E →+* C) : E ⊗[ℚ] C :=
  ∑ i, trDual b i ⊗ₜ[ℚ] τ (b i)
def evAt {E : Type} [Field E] {C : Type} [Field C] [Algebra ℚ E] [Algebra ℚ C] (σ : E →+* C) :
    E ⊗[ℚ] C →ₐ[ℚ] C :=
  Algebra.TensorProduct.productMap (σ.toRatAlgHom) (AlgHom.id ℚ C)
open Classical in

def IdemEvalSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C] [IsAlgClosed C] (ι : Type) [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℚ E) (τ σ : E →+* C),
    evAt σ (idemOf b τ) = if σ = τ then 1 else 0
def DualDiffSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E),
    (∀ i, IsIntegral ℤ (b i)) →
    (∀ x : 𝓞 E, ∃ c : ι → ℤ, (x : E) = ∑ i, (c i : ℚ) • b i) →
    ∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ i, IsIntegral ℤ ((δ : E) * trDual b i)
end ReciprocityTheory.ChartRestriction.G.TB


