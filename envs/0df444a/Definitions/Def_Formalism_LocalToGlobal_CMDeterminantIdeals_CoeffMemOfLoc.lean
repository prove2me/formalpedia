-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CoeffMemOfLoc
-- name    : Formalism_LocalToGlobal_CMDeterminantIdeals_CoeffMemOfLoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:10.648748+00:00
-- url     : https://prove2.me/theorems/1c71e608-0475-479b-bf71-9d3f0b8b28fd
-- title:
--   Coeff Mem Of Loc
-- statement:
--   Definitions and structural lemmas for Coeff Mem Of Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CoeffMemOfLoc.lean

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
def CMNumbers0 {K : Type} [Field K] [NumberField K] {g : ℕ} (abelian₂ : MLine K) (ℓ : Fin g → MLine K) (de : MLine K)
    (La logOm : ℝ) : Prop :=
  abelian₂.Good ∧ (∀ j, (ℓ j).Good) ∧ de.Good ∧ 1 ≤ La ∧
  ∑ j, (ℓ j).deg - (g : ℝ) * (Module.finrank ℚ K : ℝ) * Real.log La ≤ abelian₂.deg ∧ (∀ j, (ℓ j).ndeg = logOm / 2) ∧
  de.ndeg ≤ (1 / 2) * abelian₂.dual.ndeg + (g : ℝ) / 4 * Real.log (2 * Real.pi)
def CMNumbersLink : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (Lie : MLat K g) (ℓ : Fin g → MLine K) (u : Fin g → Fin g → K)
    (de : MLine K) (La logOm : ℝ), CMNumbers Lie ℓ u de La logOm → CMNumbers0 Lie.detLine ℓ de La logOm
def DegDe0 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (abelian₂ : MLine K) (ℓ : Fin g → MLine K) (de : MLine K) (La logOm : ℝ),
    CMNumbers0 abelian₂ ℓ de La logOm → de.ndeg ≤ (g : ℝ) * (pDeg logOm + (1 / 2) * Real.log La)
def DegNN0 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (abelian₂ : MLine K) (ℓ : Fin g → MLine K) (de : MLine K) (La logOm : ℝ)
    (V : Type) [Fintype V] (c : V → Fin g) (μ : V → ℕ) (n : ℕ), CMNumbers0 abelian₂ ℓ de La logOm →
    (lineNN de ℓ c μ n).Good ∧
    (lineNN de ℓ c μ n).ndeg ≤ (pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (g : ℝ) * n)
def LamNumber0 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (abelian₂ : MLine K) (ℓ : Fin g → MLine K) (de : MLine K) (La logOm : ℝ)
    (V : Type) [Fintype V] (c : V → Fin g) (G : MvPolynomial V K) (μ : V →₀ ℕ) (n : ℕ) (S : (K →+* ℂ) → ℝ) (Rr : ℝ),
    CMNumbers0 abelian₂ ℓ de La logOm → MvPolynomial.coeff μ G ≠ 0 → MvPolynomial.coeff μ G ∈ (lineNN de ℓ c μ n).I →
    (∀ σ, 0 < S σ) → 0 < Rr →
    (∀ (σ : K →+* ℂ) (z : V → ℂ), (∀ v, ‖z v‖ * (ℓ (c v)).n σ ≤ 1) →
      ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * de.n σ ^ n ≤ S σ * Rr ^ (∑ v, μ v)) →
    - ((pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (g : ℝ) * n)) - (∑ v, (μ v : ℝ)) * Real.log Rr ≤
      (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ)
def HadamardLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (abelian₂ : MLine K) (ℓ : Fin g → MLine K) (u : Fin g → Fin g → K)
    (B : HeightOneSpectrum (𝓞 K) → Matrix (Fin g) (Fin g) K) (H : (K →+* ℂ) → Matrix (Fin g) (Fin g) ℂ) (La : ℝ),
    abelian₂.I ≠ 0 → (∀ j, (ℓ j).Good) → LinearIndependent K u → 0 < La → (∀ σ, (H σ).PosDef) →
    (∀ σ, abelian₂.n σ = Real.sqrt (H σ).det.re) → (∀ p, IsLocGen p (B p).det abelian₂.I) →
    (∀ p j, ∃ c : K, IsLocGen p c (ℓ j).I ∧ ∀ i, p.valuation K (((B p)⁻¹.mulVec (c • u j)) i) ≤ 1) →
    (∀ σ j, ReciprocityTheory.MultiplicativeHeights.hq (H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ (u j)) ≤ (La * (ℓ j).n σ) ^ 2) →
    ∑ j, (ℓ j).deg - (g : ℝ) * (Module.finrank ℚ K : ℝ) * Real.log La ≤ abelian₂.deg
def CoeffMemOfLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (ℓ : Fin g → MLine K) (de : MLine K) (V : Type) [Fintype V] (c : V → Fin g)
    (μ : V → ℕ) (n : ℕ) (cf : K), de.Good → (∀ j, (ℓ j).Good) →
    (∀ p : HeightOneSpectrum (𝓞 K), ∃ (t : K) (cl : Fin g → K), IsLocGen p t de.I ∧ (∀ j, IsLocGen p (cl j) (ℓ j).I) ∧
      p.valuation K (cf * ∏ v, cl (c v) ^ μ v) ≤ p.valuation K (t ^ n)) →
    cf ∈ (lineNN de ℓ c μ n).I
def DegGalois : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (γ : K ≃+* K) (L L' : MLine K), L.Good →
    (∀ x : K, γ x ∈ L'.I ↔ x ∈ L.I) → (∀ σ : K →+* ℂ, L'.n σ = L.n (σ.comp (γ : K →+* K))) → L'.deg = L.deg
end Formalism.L2.LamCM


