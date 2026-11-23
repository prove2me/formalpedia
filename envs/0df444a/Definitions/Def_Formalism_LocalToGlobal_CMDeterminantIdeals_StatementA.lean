-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
-- name    : Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:52.287554+00:00
-- url     : https://prove2.me/theorems/7f063afe-5887-4df0-8574-4c5d39099ca1
-- title:
--   Statement A
-- statement:
--   Definitions and structural lemmas for Statement A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/StatementA.lean

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_DetIdeal
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
def DegAlg : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (L M : MLine K), L.Good → M.Good →
    (L.tensor M).Good ∧ (L.tensor M).deg = L.deg + M.deg ∧ L.dual.Good ∧ L.dual.deg = - L.deg ∧
      ∀ k : ℕ, (L.pow k).Good ∧ (L.pow k).deg = k * L.deg
def DegProdPow : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [Fintype V] (ℓ : V → MLine K) (k : V → ℕ), (∀ v, (ℓ v).Good) →
    (MLine.prodPow ℓ k).Good ∧ (MLine.prodPow ℓ k).deg = ∑ v, (k v : ℝ) * (ℓ v).deg
def ProdFormula : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (L : MLine K) (x : K), L.Good → x ≠ 0 →
    L.deg = Real.log ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ x * L.I⁻¹) : ℚ) : ℝ) -
      ∑ σ : K →+* ℂ, Real.log (L.len σ x)
def ProdIneq : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (L : MLine K) (x : K), L.Good → x ≠ 0 → x ∈ L.I →
    - ∑ σ : K →+* ℂ, Real.log (L.len σ x) ≤ L.deg
def MemOfLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (I : FractionalIdeal (𝓞 K)⁰ K) (x : K), I ≠ 0 →
    (∀ p : HeightOneSpectrum (𝓞 K), ∃ c : K, IsLocGen p c I ∧ p.valuation K x ≤ p.valuation K c) → x ∈ I
def NormOfLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (I : FractionalIdeal (𝓞 K)⁰ K) (c : HeightOneSpectrum (𝓞 K) → K), I ≠ 0 →
    (∀ p, IsLocGen p (c p) I) →
    (Function.support fun p : HeightOneSpectrum (𝓞 K) =>
      FractionalIdeal.count K p (FractionalIdeal.spanSingleton (𝓞 K)⁰ (c p))).Finite ∧
    Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) =
      ∑ᶠ p : HeightOneSpectrum (𝓞 K), (FractionalIdeal.count K p (FractionalIdeal.spanSingleton (𝓞 K)⁰ (c p)) : ℝ) *
        Real.log (Ideal.absNorm p.asIdeal : ℝ)
def DetGood : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (L : MLat K m), L.Good →
    IsFractional (𝓞 K)⁰ L.detSub ∧ L.detLine.Good
def DetFree : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (L : MLat K m) (b : Fin m → Fin m → K), L.Good →
    L.M = Submodule.span (𝓞 K) (Set.range b) →
    L.detLine.deg = - (1 / 2) * ∑ σ : K →+* ℂ, Real.log (ReciprocityTheory.MultiplicativeHeights.gramC (L.H σ) σ b).det.re
def DetMono : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (L L' : MLat K m), L.Good → L'.Good → L'.H = L.H → L'.M ≤ L.M →
    L'.detLine.deg ≤ L.detLine.deg
def HadamardPD : Prop :=
  ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ), A.PosDef → A.det.re ≤ ∏ i, (A i i).re
def HadamardIdeals : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (L : MLat K m) (ℓ : Fin m → MLine K) (u : Fin m → Fin m → K) (La : ℝ),
    L.Good → (∀ j, (ℓ j).Good) → LinearIndependent K u → (∀ j, ∀ a ∈ (ℓ j).I, a • u j ∈ L.M) → 0 < La →
    (∀ σ j, L.sq σ (u j) ≤ (La * (ℓ j).n σ) ^ 2) →
    ∑ j, (ℓ j).deg - (m : ℝ) * (Module.finrank ℚ K : ℝ) * Real.log La ≤ L.detLine.deg
def DetLatDeg : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (L : MLat K m) (b : Fin m → Fin m → K), L.Good →
    ReciprocityTheory.MultiplicativeHeights.IsKBasisIn L.M b → L.detLine.deg = ReciprocityTheory.MultiplicativeHeights.latDeg L.H L.M b
end Formalism.L2.LamCM


