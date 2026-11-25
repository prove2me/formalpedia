-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_ShareSt
-- name    : ReciprocityTheory_SemistableReduction_ShareSt
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:23:10.172916+00:00
-- url     : https://prove2.me/theorems/2adc5ff4-5184-41f5-b9bf-17d94c6aa1a4
-- title:
--   Share St
-- statement:
--   Definitions and structural lemmas for Share St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareSt.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IndependentSectionsUpperCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate Module
open scoped ComplexOrder
def ballRatio (r : ℕ) : ℝ := (1 + 1 / (7 * (r : ℝ))) / (1 - 1 / (7 * (r : ℝ)))
def signMat (p r : ℕ) : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun k : Fin r => sgn p k
def BoundedBallStatement : Prop :=
  ∀ (r p : ℕ) (H : Matrix (Fin r) (Fin r) ℂ) (s : ℝ),
    H.PosDef → H * signMat p r * H = signMat p r → 0 ≤ s → s < 1 →
    (∀ u : Fin r → ℂ, signMat p r *ᵥ (H *ᵥ u) = u → negSq p u ≤ s ^ 2 * posSq p u) →
    ∀ u : Fin r → ℂ, hq H u ≤ (1 + s) / (1 - s) * normSq u ∧
      normSq u ≤ (1 + s) / (1 - s) * hq H u
def NearMaj {K : Type} [Field K] [NumberField K] {r : ℕ} {S : HermForm K r}
    (M0 M : Majorant S) (c : ℝ) : Prop :=
  ∀ (σ : K →+* ℂ) (u : Fin r → ℂ),
    hq (M.H σ) u ≤ c * hq (M0.H σ) u ∧ hq (M0.H σ) u ≤ c * hq (M.H σ) u
def NoContraction {K : Type} [Field K] [NumberField K] {r : ℕ}
    (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  ∀ N : Matrix (Fin r) (Fin r) K, (∀ x ∈ L, N *ᵥ x ∈ L) →
    (∀ (σ : K →+* ℂ) (u : Fin r → ℂ), u ≠ 0 → hq (H σ) (N.map σ *ᵥ u) < hq (H σ) u) → N = 0
def BallTrivialStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r g : ℕ) (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)) (M0 M1 M2 : Majorant S) (γ : Matrix (Fin r) (Fin r) K),
    NoContraction M0.H L → NearMaj M0 M1 (ballRatio r) → NearMaj M0 M2 (ballRatio r) →
    (∀ (σ : K →+* ℂ) (u : Fin r → ℂ), hq (M2.H σ) (γ.map σ *ᵥ u) = hq (M1.H σ) u) →
    (∀ x ∈ L, γ *ᵥ x ∈ L) →
    (∀ n : ℕ, 1 ≤ n → n ≤ r → ∃ z : 𝓞 K, (γ ^ n).trace - r = (g : K) * z) → 3 * r < g →
    γ = 1
def orbitMat {U Z : Type} [Group U] [MulAction U Z] (u0 : Z → ℂ) (z : Z) : Matrix U U ℂ :=
  Matrix.of fun a b => u0 ((a * b) • z)
def MonomialDetStatement : Prop :=
  ∀ (U : Type) [Group U] [Fintype U] [DecidableEq U] (Z : Type) [MulAction U Z]
    (u0 : Z → ℂ) (z0 : Z),
    u0 z0 ≠ 0 → (∀ a : U, a ≠ 1 → u0 (a • z0) = 0) →
    ∀ h : U, (orbitMat (U := U) u0 (h • z0)).det ≠ 0
def ZeroByDetStatement : Prop :=
  ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La]
    (A : ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La) (U : Type) [Fintype U] [DecidableEq U]
    (la la' : La) (M : U → U → ι → Y → ℂ) (x : ι → Y → ℂ),
    (∀ a b, A.IsSec la (M a b)) → A.IsSec la' x →
    (∀ y, ∃ y' ∈ connectedComponent y,
      (Matrix.of fun a b => M a b (A.pick y') y').det ≠ 0) →
    (∀ y, (Matrix.of fun a b => M a b (A.pick y) y).det ≠ 0 → x (A.pick y) y = 0) →
    ∀ j y, y ∈ (A.chart j).source → x j y = 0
def CountStatement : Prop :=
  ∀ (V W R R' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup R] [Module ℂ R] [AddCommGroup R'] [Module ℂ R'] (U : Type) [Fintype U]
    (m d0 : ℕ) (g : Fin m → V) (res : V →ₗ[ℂ] R) (resW : W →ₗ[ℂ] R')
    (Φ : V →ₗ[ℂ] (U → W)) (Wψ : Submodule ℂ W),
    LinearIndependent ℂ (res ∘ g) →
    (∀ v ∈ Submodule.span ℂ (Set.range g), ∀ h, Φ v h ∈ Wψ) →
    (∀ v ∈ Submodule.span ℂ (Set.range g), (∀ h, resW (Φ v h) = 0) → res v = 0) →
    (∀ (k : ℕ) (f : Fin k → W), (∀ i, f i ∈ Wψ) → LinearIndependent ℂ (resW ∘ f) → k ≤ d0) →
    m ≤ Fintype.card U * d0
def psiPart {K U V : Type} [Field K] [Monoid U] [AddCommGroup V] [Module K V]
    (ρ : Representation K U V) (χ : U →* Kˣ) : Submodule K V :=
  ⨅ u : U, LinearMap.ker (ρ u - ((χ u : Kˣ) : K) • LinearMap.id)
def psiPartBC {K L U V : Type} [Field K] [Field L] [Algebra K L] [Monoid U] [AddCommGroup V]
    [Module K V] (ρ : Representation K U V) (χ : U →* Kˣ) :
    Submodule L (TensorProduct K L V) :=
  ⨅ u : U, LinearMap.ker ((ρ u).baseChange L - algebraMap K L ((χ u : Kˣ) : K) • LinearMap.id)
def FreePsiStatement : Prop :=
  ∀ (K : Type) [Field K] (U : Type) [Group U] [Fintype U] [DecidableEq U]
    (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K U V) (χ : U →* Kˣ) (W0 : Submodule K V),
    DirectSum.IsInternal (fun u : U => W0.map (ρ u)) →
    Fintype.card U * finrank K (psiPart ρ χ) = finrank K V
def PsiBaseChangeStatement : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (U : Type) [Group U] [Fintype U]
    (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K U V) (χ : U →* Kˣ),
    finrank L (psiPartBC (L := L) ρ χ) = finrank K (psiPart ρ χ)
def ShareNumbersStatement : Prop :=
  ∀ (D T P f k : ℕ), 6 ≤ D → P ^ 3 * D ^ 3 * k * f ≤ T → f * k ≤ P → 2 ≤ f * k →
    ((D * (D + 6) : ℕ) : ℝ) / T ≤ 1 / (4 * ((f * k : ℕ) : ℝ) ^ 3)
end ReciprocityTheory.MultiplicativeHeights


