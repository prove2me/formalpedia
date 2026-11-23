-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:40:54.507796+00:00
-- url     : https://prove2.me/theorems/98955f65-9cfd-4d21-8ab3-d3b615e1e31e
-- title:
--   QCore St
-- statement:
--   Definitions and structural lemmas for QCore St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/QCoreSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobSt
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
noncomputable def lenLa {K : Type*} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
    (N : Type*) [AddCommGroup N] [Module (𝓞 K) N] : ℕ∞ :=
  Module.length (Localization.AtPrime la.asIdeal) (LocalizedModule la.asIdeal.primeCompl N)
def LiesOver {K K₁ : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    (w : HeightOneSpectrum (𝓞 K₁)) (la : HeightOneSpectrum (𝓞 K)) : Prop :=
  w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 K₁)) = la.asIdeal
abbrev QuotMW {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V) (W : Submodule K V) :=
  M ⧸ (W.restrictScalars (𝓞 K)).comap M.subtype
noncomputable def lenW {K K₁ V : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁]
    [Algebra K K₁] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (w : HeightOneSpectrum (𝓞 K₁)) (M : Submodule (𝓞 K) V) (W : Submodule K V) {ρ : ℕ}
    (θ : Fin ρ → M) : ℕ∞ :=
  let Rw := (w.valuationSubringAtPrime K₁).toSubring
  letI : Module Rw (K₁ ⊗[K] V) := Module.compHom _ Rw.subtype
  let Mw := Submodule.span Rw ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (M.restrictScalars ℤ : Set V))
  let Nw := (Submodule.span Rw (Submodule.span K₁
      ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V)) : Set (K₁ ⊗[K] V)) ⊓ Mw) ⊔
    Submodule.span Rw (Set.range fun j => (1 : K₁) ⊗ₜ[K] ((θ j : M) : V))
  Module.length Rw (Mw ⧸ Nw.comap Mw.subtype)
def LenDescentStatement : Prop :=
  ∀ (K K₁ V : Type) [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), M.FG → Submodule.span K (M : Set V) = ⊤ →
    ∀ (W : Submodule K V) {ρ : ℕ} (θ : Fin ρ → M) (la : HeightOneSpectrum (𝓞 K))
      (w : HeightOneSpectrum (𝓞 K₁)), LiesOver w la →
      lenW w M W θ = (w.asIdeal.ramificationIdx (𝓞 K) : ℕ∞) *
        lenLa la (QuotMW M W ⧸ Submodule.span (𝓞 K)
          (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W)))
def QuotCoreStatement : Prop :=
  LenDescentStatement →
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
      (∀ la, 0 ≤ be la) → (Function.support be).Finite → (∀ i, (Function.support (s i)).Finite) →

      (∀ (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁)), LiesOver w la →
        ∀ i, ∀ m ∈ M, c i ((1 : K₁) ⊗ₜ[K] m) ≠ 0 →
          -((w.asIdeal.ramificationIdx (𝓞 K) : ℝ) * be la) ≤
            (ordAt w (c i ((1 : K₁) ⊗ₜ[K] m)) : ℝ) + s i w) →
    ∀ (supN : (K →+* ℂ) → V → ℝ) (a : Fin (Module.finrank (𝓞 K) (QuotMW M W)) → InfinitePlace K₁ → ℝ)
      (Bθ Carch Bdeg : ℝ),

      (∀ τ v, supN ((starRingEnd ℂ).comp τ) v = supN τ v) →

      (∀ j, (∑ τ : K →+* ℂ, Real.log (supN τ ((θ j : M) : V))) / (Fintype.card (K →+* ℂ) : ℝ) ≤ Bθ) →

      (∀ (σ : InfinitePlace K₁) i j, c i ((1 : K₁) ⊗ₜ[K] ((θ j : M) : V)) ≠ 0 →
        Real.log (σ (c i ((1 : K₁) ⊗ₜ[K] ((θ j : M) : V)))) + a i σ ≤
          Real.log (supN (σ.embedding.comp (algebraMap K K₁)) ((θ j : M) : V)) + Carch) →

      (∀ i, ((∑ᶠ w, s i w * logN w) - ∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * a i σ) /
          (Module.finrank ℚ K₁ : ℝ) ≤ Bdeg) →
      ∃ nn : HeightOneSpectrum (𝓞 K) →₀ ℝ,
        (∀ la, ∃ ℓ : ℕ,
          lenLa la (QuotMW M W ⧸ Submodule.span (𝓞 K)
            (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W))) = ℓ ∧
          (ℓ : ℝ) ≤ nn la + (Module.finrank (𝓞 K) (QuotMW M W) : ℝ) * be la) ∧
        (nn.sum fun la v => v * logN la) / (Module.finrank ℚ K : ℝ) ≤
          (Module.finrank (𝓞 K) (QuotMW M W) : ℝ) * (Bθ + Carch + Bdeg) +
            (Module.finrank (𝓞 K) (QuotMW M W) : ℝ) / 2 *
              Real.log (Module.finrank (𝓞 K) (QuotMW M W) : ℝ)
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank


