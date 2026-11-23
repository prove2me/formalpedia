-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreH
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreH
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:46:12.357119+00:00
-- url     : https://prove2.me/theorems/9a61aabf-e746-4152-9ea7-4b0846ca49d6
-- title:
--   QCore H
-- statement:
--   Definitions and structural lemmas for QCore H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/QCoreH.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable def detCT {K K₁ V : Type*} [Field K] [NumberField K] [Field K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] {M : Submodule (𝓞 K) V} {ρ : ℕ}
    (c : Fin ρ → Module.Dual K₁ (K₁ ⊗[K] V)) (θ : Fin ρ → M) : K₁ :=
  (Matrix.of fun i j => c i ((1 : K₁) ⊗ₜ[K] ((θ j : M) : V))).det
noncomputable def nnFun {K K₁ : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁]
    [Algebra K K₁] {ρ : ℕ} (D : K₁) (s : Fin ρ → HeightOneSpectrum (𝓞 K₁) → ℝ)
    (la : HeightOneSpectrum (𝓞 K)) : ℝ :=
  (∑ᶠ w : {w : HeightOneSpectrum (𝓞 K₁) // LiesOver w la},
      (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * ((ordAt w.1 D : ℝ) + ∑ i, s i w.1)) /
    (Module.finrank K K₁ : ℝ)
def QCoreLocalStatement : Prop :=
  LenDescentStatement → QuotLocalStatement →
  ∀ (K K₁ V : Type) [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), M.FG → Submodule.span K (M : Set V) = ⊤ →
    ∀ (W : Submodule K V) (θ : Fin (Module.finrank (𝓞 K) (QuotMW M W)) → M),
      Submodule.span K (Set.range fun j => ((θ j : M) : V)) ⊔ W = ⊤ →
    ∀ (c : Fin (Module.finrank (𝓞 K) (QuotMW M W)) → Module.Dual K₁ (K₁ ⊗[K] V)),
      (∀ x : K₁ ⊗[K] V, (∀ i, c i x = 0) ↔
        x ∈ Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V))) →
    ∀ (be : HeightOneSpectrum (𝓞 K) → ℝ)
      (s : Fin (Module.finrank (𝓞 K) (QuotMW M W)) → HeightOneSpectrum (𝓞 K₁) → ℝ),
      (∀ la, 0 ≤ be la) → (∀ i, (Function.support (s i)).Finite) →
      (∀ (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁)), LiesOver w la →
        ∀ i, ∀ m ∈ M, c i ((1 : K₁) ⊗ₜ[K] m) ≠ 0 →
          -((w.asIdeal.ramificationIdx (𝓞 K) : ℝ) * be la) ≤
            (ordAt w (c i ((1 : K₁) ⊗ₜ[K] m)) : ℝ) + s i w) →
      detCT c θ ≠ 0 ∧
      ∀ la : HeightOneSpectrum (𝓞 K), ∃ ℓ : ℕ,
        lenLa la (QuotMW M W ⧸ Submodule.span (𝓞 K)
          (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W))) = ℓ ∧
        (ℓ : ℝ) ≤ nnFun (detCT c θ) s la + (Module.finrank (𝓞 K) (QuotMW M W) : ℝ) * be la
def QCoreGlobalStatement : Prop :=
  ∀ (K K₁ V : Type) [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] (M : Submodule (𝓞 K) V) (ρ : ℕ)
    (θ : Fin ρ → M) (c : Fin ρ → Module.Dual K₁ (K₁ ⊗[K] V)), detCT c θ ≠ 0 →
    ∀ (s : Fin ρ → HeightOneSpectrum (𝓞 K₁) → ℝ), (∀ i, (Function.support (s i)).Finite) →
    ∀ (supN : (K →+* ℂ) → V → ℝ) (a : Fin ρ → InfinitePlace K₁ → ℝ) (Bθ Carch Bdeg : ℝ),
      (∀ τ v, supN ((starRingEnd ℂ).comp τ) v = supN τ v) →
      (∀ j, (∑ τ : K →+* ℂ, Real.log (supN τ ((θ j : M) : V))) / (Fintype.card (K →+* ℂ) : ℝ) ≤ Bθ) →
      (∀ (σ : InfinitePlace K₁) i j, c i ((1 : K₁) ⊗ₜ[K] ((θ j : M) : V)) ≠ 0 →
        Real.log (σ (c i ((1 : K₁) ⊗ₜ[K] ((θ j : M) : V)))) + a i σ ≤
          Real.log (supN (σ.embedding.comp (algebraMap K K₁)) ((θ j : M) : V)) + Carch) →
      (∀ i, ((∑ᶠ w, s i w * logN w) - ∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * a i σ) /
          (Module.finrank ℚ K₁ : ℝ) ≤ Bdeg) →
      (Function.support (nnFun (K := K) (detCT c θ) s)).Finite ∧
      (∑ᶠ la : HeightOneSpectrum (𝓞 K), nnFun (K := K) (detCT c θ) s la * logN la) /
          (Module.finrank ℚ K : ℝ) ≤
        (ρ : ℝ) * (Bθ + Carch + Bdeg) + (ρ : ℝ) / 2 * Real.log ρ
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank


