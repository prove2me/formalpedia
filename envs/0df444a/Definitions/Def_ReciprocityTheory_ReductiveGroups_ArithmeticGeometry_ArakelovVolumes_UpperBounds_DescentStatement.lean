-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DescentStatement
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DescentStatement
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:58:27.839022+00:00
-- url     : https://prove2.me/theorems/b9006aec-6ee1-4331-8cbf-5ed5f25e94e9
-- title:
--   Descent Statement
-- statement:
--   Definitions and structural lemmas for Descent Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DescentStatement.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FunKerSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
def KerDimStatement : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] (sg : K →+* ℂ) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V],
    letI : Algebra K ℂ := sg.toAlgebra
    ∀ (Wc : Submodule ℂ (ℂ ⊗[K] V)) (FF : Set (Module.Dual ℂ (ℂ ⊗[K] V))),
    (∀ c ∈ FF, ∃ K' : IntermediateField K ℂ, FiniteDimensional K K' ∧ DefinedOver c K') →
    (∀ c ∈ FF, Wc ≤ LinearMap.ker c) →
    (∀ x ∈ baseSpan ℂ (⊤ : Submodule K V), x ∉ Wc → ∃ c ∈ FF, c x ≠ 0) →
    (∀ c ∈ FF, ∀ K₂ : IntermediateField K ℂ, FiniteDimensional K K₂ → IsGalois K K₂ →
      DefinedOver c K₂ → ∀ σ : K₂ ≃ₐ[K] K₂, ∀ x ∈ descend K₂ Wc,
        c (inclT K₂ V (galAct σ x)) = 0) →
    Submodule.span ℂ ((fun v => (1 : ℂ) ⊗ₜ[K] v) '' {v : V | (1 : ℂ) ⊗ₜ[K] v ∈ Wc}) = Wc ∧
      Module.finrank K (Submodule.span K {v : V | (1 : ℂ) ⊗ₜ[K] v ∈ Wc}) = Module.finrank ℂ Wc
def DescentStatement : Prop :=
  ∀ (F F' V : Type) [Field F] [Field F'] [Algebra F F'] [AddCommGroup V] [Module F V]
    (ι : Type) [Fintype ι] (v : ι → V),
    (LinearIndependent F v ↔ LinearIndependent F' (fun i => (1 : F') ⊗ₜ[F] v i)) ∧
    (∀ x : V, x ∈ Submodule.span F (Set.range v) ↔
      (1 : F') ⊗ₜ[F] x ∈ Submodule.span F' (Set.range fun i => (1 : F') ⊗ₜ[F] v i)) ∧
    Module.finrank F (Submodule.span F (Set.range v)) =
      Module.finrank F' (Submodule.span F' (Set.range fun i => (1 : F') ⊗ₜ[F] v i))
end ReciprocityTheory.ChartRestriction.G.AR.Up


