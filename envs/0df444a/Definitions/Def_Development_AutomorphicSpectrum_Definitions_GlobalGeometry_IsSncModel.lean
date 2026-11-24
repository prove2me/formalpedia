-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
-- name    : Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:18.396545+00:00
-- url     : https://prove2.me/theorems/b912f86d-8d9a-4cec-b2e9-c039f02ddd0d
-- title:
--   Is Snc Model
-- statement:
--   Definitions and structural lemmas for Is Snc Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsSncModel.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_MetricsProjectionFormulaNef
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ConjugateHermitianLineIsometries
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cmp
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ)
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
structure IsEmbedded {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : Ideal (MRing ι))
    (U : X → Set X) (lam : X → X → (Σ k, ι k) → ℂ) : Prop where
  isOpen : ∀ x, IsOpen (U x)
  mem_U : ∀ x, x ∈ U x
  holo : ∀ x p, A.HoloOn (U x) fun y => lam x y p
  mem : ∀ x, ∀ y ∈ U x, lam x y ∈ mcPts P
  compat : ∀ x x', ∀ y ∈ U x ∩ U x', SameOrbit (lam x y) (lam x' y)
  surj : ∀ z ∈ mcPts P, ∃ x, SameOrbit (lam x x) z
  inj : ∀ x x', SameOrbit (lam x x) (lam x' x') → x = x'
  immersion : ∀ x, ∀ p : (k : K) → ι k, (∀ k, lam x x ⟨k, p k⟩ ≠ 0) → ∀ j, x ∈ (A.chart j).source →
    (fderiv ℂ (fun y => affCoord p (lam x ((A.chart j).symm y))) (A.chart j x)).ker = ⊥
def secOf {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (β : MRing ι) : R.X → R.X → ℂ :=
  fun x y => evC (R.lift x y) β
def IsSncModel {Ω : Type} [Field Ω] [Algebra ℚ Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)) : Prop :=
  ∀ c : (k : K) → ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (m : ℕ) (f a : Fin m → Ω),
    (∀ l, f l ∈ Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) ∧
    (∀ l, a l ∈ Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) ∧
    ∑ l, a l * f l = 1 ∧ ∀ l, f l ≠ 0 → ∀ S : Subalgebra ℚ Ω,
      S = Algebra.adjoin ℚ (insert (f l)⁻¹ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) →
      Algebra.Smooth ℚ S ∧ ∃ (z : Fin e → S) (n : ℕ), n ≤ e ∧
        LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)) ∧
        Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ ∧
        ∀ q : Ideal S, q.IsPrime →
          ((∀ g ∈ J, ∀ s : S, (s : Ω) = aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) g → s ∈ q) ↔
            ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)
def AlgOver {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) : Prop :=
  ∃ (K₀ : Type) (_ : Fintype K₀) (ι₀ : K₀ → Type) (_ : ∀ k, Fintype (ι₀ k)) (κ : K₀ → K)
    (v : (Σ k, ι₀ k) → Σ k, ι k) (U : S.X → Set S.X) (lam : S.X → S.X → (Σ k, ι₀ k) → ℂ) (β : MRing ι₀) (b : K₀ → ℕ),
    IsBlockMap κ v ∧ IsEmbedded S.A (imageZ v P) U lam ∧
    (∀ x, SameOrbit (lam (Re.π x) (Re.π x)) fun p => Re.R.lift x x (v p)) ∧
    IsMultiHomog β b ∧ β ∉ imageZ v P ∧ ∀ x ∈ bdry S.s, evC (lam x x) β = 0
section Same
variable {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
def SameSing {D : ℕ} {σ₁ σ₂ : Type} {S₁ : AnSys D σ₁} {S₂ : AnSys D σ₂} {P₁ : Ideal (MRing ι₁)}
    {P₂ : Ideal (MRing ι₂)} (Re₁ : Realis S₁ P₁) (Re₂ : Realis S₂ P₂) (P : Ideal (MRing ι)) (κ₁ : K₁ → K)
    (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, ι k) (β : MRing ι) (a₁ : σ₁) (a₂ : σ₂) :
    Prop :=
  ∃ f g : MRing ι, IsLineIso P (pullDeg κ₁ (Re₁.ref a₁).a) (pullDeg κ₂ (Re₂.ref a₂).a) f g ∧
    ∀ z ∈ mcPts P, evC z β ≠ 0 → ∀ (x₁ : Re₁.R.X) (x₂ : Re₂.R.X),
      SameOrbit (Re₁.R.lift x₁ x₁) (fun p => z (v₁ p)) → SameOrbit (Re₂.R.lift x₂ x₂) (fun p => z (v₂ p)) →
      Re₁.π x₁ ∉ bdry S₁.s → Re₂.π x₂ ∉ bdry S₂.s →
      ∀ u v : MRing ι, u * f - v * g ∈ P → evC z u ≠ 0 →
        Real.log (‖evC z v‖ / ‖evC z u‖ * (Re₂.ref a₂).h (fun p => z (v₂ p)) / (Re₁.ref a₁).h fun p => z (v₁ p)) =
          S₁.ph a₁ (Re₁.π x₁) - S₂.ph a₂ (Re₂.π x₂)
end Same
end GlobalTheory.CompanionTheory.Ar.Cmp


